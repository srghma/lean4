// Lean compiler output
// Module: Lean.Data.RBTree
// Imports: Lean.Data.RBMap
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Lean::Data::RBMap::{
    initialize_Lean_Data_RBMap, l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit,
    l_Lean_RBMap_filter___redArg, l_Lean_RBNode_all___redArg, l_Lean_RBNode_any___redArg,
    l_Lean_RBNode_appendTrees___redArg, l_Lean_RBNode_balLeft___redArg,
    l_Lean_RBNode_balRight___redArg, l_Lean_RBNode_depth___redArg, l_Lean_RBNode_erase___redArg,
    l_Lean_RBNode_findCore___redArg, l_Lean_RBNode_fold___redArg, l_Lean_RBNode_foldM___redArg,
    l_Lean_RBNode_insert___redArg, l_Lean_RBNode_isBlack___redArg, l_Lean_RBNode_isRed___redArg,
    l_Lean_RBNode_max___redArg, l_Lean_RBNode_min___redArg, l_Lean_RBNode_revFold___redArg,
    l_Lean_RBNode_setBlack___redArg, runtime_initialize_Lean_Data_RBMap,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_RBTree_toList___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_RBTree_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBTree_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toList___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_RBTree_toArray___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_RBTree_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBTree_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_RBTree_toArray___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_RBTree_toArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            76, 101, 97, 110, 46, 114, 98, 116, 114, 101, 101, 79, 102, 32, 0,
        ],
    };
static mut l_Lean_RBTree_instRepr___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_RBTree_instRepr___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_instInhabitedRBTree(
    mut v_00_u03b1_990_: *mut LeanObject,
    mut v_p_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = lean_box(0);
    return v___x_992_;
}
pub unsafe fn l_Lean_instInhabitedRBTree___boxed(
    mut v_00_u03b1_993_: *mut LeanObject,
    mut v_p_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_995_: *mut LeanObject = core::ptr::null_mut();
    v_res_995_ = l_Lean_instInhabitedRBTree(v_00_u03b1_993_, v_p_994_);
    lean_dec_ref(v_p_994_);
    return v_res_995_;
}
pub unsafe fn l_Lean_mkRBTree(
    mut v_00_u03b1_996_: *mut LeanObject,
    mut v_cmp_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v___x_998_ = lean_box(0);
    return v___x_998_;
}
pub unsafe fn l_Lean_mkRBTree___boxed(
    mut v_00_u03b1_999_: *mut LeanObject,
    mut v_cmp_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1001_: *mut LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_mkRBTree(v_00_u03b1_999_, v_cmp_1000_);
    lean_dec_ref(v_cmp_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBTree(
    mut v_00_u03b1_1002_: *mut LeanObject,
    mut v_cmp_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_box(0);
    return v___x_1004_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBTree___boxed(
    mut v_00_u03b1_1005_: *mut LeanObject,
    mut v_cmp_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1007_: *mut LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Lean_instEmptyCollectionRBTree(v_00_u03b1_1005_, v_cmp_1006_);
    lean_dec_ref(v_cmp_1006_);
    return v_res_1007_;
}
pub unsafe fn l_Lean_RBTree_empty(
    mut v_00_u03b1_1008_: *mut LeanObject,
    mut v_cmp_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_box(0);
    return v___x_1010_;
}
pub unsafe fn l_Lean_RBTree_empty___boxed(
    mut v_00_u03b1_1011_: *mut LeanObject,
    mut v_cmp_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_RBTree_empty(v_00_u03b1_1011_, v_cmp_1012_);
    lean_dec_ref(v_cmp_1012_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_RBTree_depth___redArg(
    mut v_f_1014_: *mut LeanObject,
    mut v_t_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Lean_RBNode_depth___redArg(v_f_1014_, v_t_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Lean_RBTree_depth___redArg___boxed(
    mut v_f_1017_: *mut LeanObject,
    mut v_t_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_RBTree_depth___redArg(v_f_1017_, v_t_1018_);
    lean_dec(v_t_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_RBTree_depth(
    mut v_00_u03b1_1020_: *mut LeanObject,
    mut v_cmp_1021_: *mut LeanObject,
    mut v_f_1022_: *mut LeanObject,
    mut v_t_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    v___x_1024_ = l_Lean_RBNode_depth___redArg(v_f_1022_, v_t_1023_);
    return v___x_1024_;
}
pub unsafe fn l_Lean_RBTree_depth___boxed(
    mut v_00_u03b1_1025_: *mut LeanObject,
    mut v_cmp_1026_: *mut LeanObject,
    mut v_f_1027_: *mut LeanObject,
    mut v_t_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_RBTree_depth(v_00_u03b1_1025_, v_cmp_1026_, v_f_1027_, v_t_1028_);
    lean_dec(v_t_1028_);
    lean_dec_ref(v_cmp_1026_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_RBTree_fold___redArg___lam__0(
    mut v_f_1030_: *mut LeanObject,
    mut v_r_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_x_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    v___x_1034_ = lean_apply_2(v_f_1030_, v_r_1031_, v_a_1032_);
    return v___x_1034_;
}
pub unsafe fn l_Lean_RBTree_fold___redArg(
    mut v_f_1035_: *mut LeanObject,
    mut v_init_1036_: *mut LeanObject,
    mut v_t_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    v___f_1038_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1038_, 0, v_f_1035_);
    v___x_1039_ = l_Lean_RBNode_fold___redArg(v___f_1038_, v_init_1036_, v_t_1037_);
    return v___x_1039_;
}
pub unsafe fn l_Lean_RBTree_fold(
    mut v_00_u03b1_1040_: *mut LeanObject,
    mut v_00_u03b2_1041_: *mut LeanObject,
    mut v_cmp_1042_: *mut LeanObject,
    mut v_f_1043_: *mut LeanObject,
    mut v_init_1044_: *mut LeanObject,
    mut v_t_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v___f_1046_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1046_, 0, v_f_1043_);
    v___x_1047_ = l_Lean_RBNode_fold___redArg(v___f_1046_, v_init_1044_, v_t_1045_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_RBTree_fold___boxed(
    mut v_00_u03b1_1048_: *mut LeanObject,
    mut v_00_u03b2_1049_: *mut LeanObject,
    mut v_cmp_1050_: *mut LeanObject,
    mut v_f_1051_: *mut LeanObject,
    mut v_init_1052_: *mut LeanObject,
    mut v_t_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_RBTree_fold(
        v_00_u03b1_1048_,
        v_00_u03b2_1049_,
        v_cmp_1050_,
        v_f_1051_,
        v_init_1052_,
        v_t_1053_,
    );
    lean_dec_ref(v_cmp_1050_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_RBTree_revFold___redArg(
    mut v_f_1055_: *mut LeanObject,
    mut v_init_1056_: *mut LeanObject,
    mut v_t_1057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    v___f_1058_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1058_, 0, v_f_1055_);
    v___x_1059_ = l_Lean_RBNode_revFold___redArg(v___f_1058_, v_init_1056_, v_t_1057_);
    return v___x_1059_;
}
pub unsafe fn l_Lean_RBTree_revFold(
    mut v_00_u03b1_1060_: *mut LeanObject,
    mut v_00_u03b2_1061_: *mut LeanObject,
    mut v_cmp_1062_: *mut LeanObject,
    mut v_f_1063_: *mut LeanObject,
    mut v_init_1064_: *mut LeanObject,
    mut v_t_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___f_1066_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1066_, 0, v_f_1063_);
    v___x_1067_ = l_Lean_RBNode_revFold___redArg(v___f_1066_, v_init_1064_, v_t_1065_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_RBTree_revFold___boxed(
    mut v_00_u03b1_1068_: *mut LeanObject,
    mut v_00_u03b2_1069_: *mut LeanObject,
    mut v_cmp_1070_: *mut LeanObject,
    mut v_f_1071_: *mut LeanObject,
    mut v_init_1072_: *mut LeanObject,
    mut v_t_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_RBTree_revFold(
        v_00_u03b1_1068_,
        v_00_u03b2_1069_,
        v_cmp_1070_,
        v_f_1071_,
        v_init_1072_,
        v_t_1073_,
    );
    lean_dec_ref(v_cmp_1070_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_RBTree_foldM___redArg(
    mut v_inst_1075_: *mut LeanObject,
    mut v_f_1076_: *mut LeanObject,
    mut v_init_1077_: *mut LeanObject,
    mut v_t_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___f_1079_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1079_, 0, v_f_1076_);
    v___x_1080_ = l_Lean_RBNode_foldM___redArg(v_inst_1075_, v___f_1079_, v_init_1077_, v_t_1078_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_RBTree_foldM(
    mut v_00_u03b1_1081_: *mut LeanObject,
    mut v_00_u03b2_1082_: *mut LeanObject,
    mut v_cmp_1083_: *mut LeanObject,
    mut v_m_1084_: *mut LeanObject,
    mut v_inst_1085_: *mut LeanObject,
    mut v_f_1086_: *mut LeanObject,
    mut v_init_1087_: *mut LeanObject,
    mut v_t_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    v___f_1089_ = lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1089_, 0, v_f_1086_);
    v___x_1090_ = l_Lean_RBNode_foldM___redArg(v_inst_1085_, v___f_1089_, v_init_1087_, v_t_1088_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_RBTree_foldM___boxed(
    mut v_00_u03b1_1091_: *mut LeanObject,
    mut v_00_u03b2_1092_: *mut LeanObject,
    mut v_cmp_1093_: *mut LeanObject,
    mut v_m_1094_: *mut LeanObject,
    mut v_inst_1095_: *mut LeanObject,
    mut v_f_1096_: *mut LeanObject,
    mut v_init_1097_: *mut LeanObject,
    mut v_t_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_RBTree_foldM(
        v_00_u03b1_1091_,
        v_00_u03b2_1092_,
        v_cmp_1093_,
        v_m_1094_,
        v_inst_1095_,
        v_f_1096_,
        v_init_1097_,
        v_t_1098_,
    );
    lean_dec_ref(v_cmp_1093_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_RBTree_forM___redArg___lam__0(
    mut v_f_1100_: *mut LeanObject,
    mut v_r_1101_: *mut LeanObject,
    mut v_a_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = lean_apply_1(v_f_1100_, v_a_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_RBTree_forM___redArg(
    mut v_inst_1105_: *mut LeanObject,
    mut v_f_1106_: *mut LeanObject,
    mut v_t_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___f_1108_ = lean_alloc_closure(
        l_Lean_RBTree_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1108_, 0, v_f_1106_);
    v___x_1109_ = lean_box(0);
    v___x_1110_ = l_Lean_RBNode_foldM___redArg(v_inst_1105_, v___f_1108_, v___x_1109_, v_t_1107_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_RBTree_forM(
    mut v_00_u03b1_1111_: *mut LeanObject,
    mut v_cmp_1112_: *mut LeanObject,
    mut v_m_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_f_1115_: *mut LeanObject,
    mut v_t_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v___f_1117_ = lean_alloc_closure(
        l_Lean_RBTree_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1117_, 0, v_f_1115_);
    v___x_1118_ = lean_box(0);
    v___x_1119_ = l_Lean_RBNode_foldM___redArg(v_inst_1114_, v___f_1117_, v___x_1118_, v_t_1116_);
    return v___x_1119_;
}
pub unsafe fn l_Lean_RBTree_forM___boxed(
    mut v_00_u03b1_1120_: *mut LeanObject,
    mut v_cmp_1121_: *mut LeanObject,
    mut v_m_1122_: *mut LeanObject,
    mut v_inst_1123_: *mut LeanObject,
    mut v_f_1124_: *mut LeanObject,
    mut v_t_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1126_: *mut LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lean_RBTree_forM(
        v_00_u03b1_1120_,
        v_cmp_1121_,
        v_m_1122_,
        v_inst_1123_,
        v_f_1124_,
        v_t_1125_,
    );
    lean_dec_ref(v_cmp_1121_);
    return v_res_1126_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg___lam__0(
    mut v_f_1127_: *mut LeanObject,
    mut v_a_1128_: *mut LeanObject,
    mut v_x_1129_: *mut LeanObject,
    mut v_acc_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = lean_apply_2(v_f_1127_, v_a_1128_, v_acc_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg___lam__1(
    mut v_toPure_1132_: *mut LeanObject,
    mut v_____do__lift_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v_a_1134_ = lean_ctor_get(v_____do__lift_1133_, 0);
    lean_inc(v_a_1134_);
    lean_dec_ref(v_____do__lift_1133_);
    v___x_1135_ = lean_apply_2(v_toPure_1132_, lean_box(0), v_a_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg(
    mut v_inst_1136_: *mut LeanObject,
    mut v_t_1137_: *mut LeanObject,
    mut v_init_1138_: *mut LeanObject,
    mut v_f_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1140_ = lean_ctor_get(v_inst_1136_, 0);
    v_toBind_1141_ = lean_ctor_get(v_inst_1136_, 1);
    lean_inc(v_toBind_1141_);
    v_toPure_1142_ = lean_ctor_get(v_toApplicative_1140_, 1);
    lean_inc(v_toPure_1142_);
    v___f_1143_ = lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1143_, 0, v_f_1139_);
    v___x_1144_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_1136_,
        v___f_1143_,
        v_t_1137_,
        v_init_1138_,
    );
    v___f_1145_ = lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1145_, 0, v_toPure_1142_);
    v___x_1146_ = lean_apply_4(
        v_toBind_1141_,
        lean_box(0),
        lean_box(0),
        v___x_1144_,
        v___f_1145_,
    );
    return v___x_1146_;
}
pub unsafe fn l_Lean_RBTree_forIn(
    mut v_00_u03b1_1147_: *mut LeanObject,
    mut v_cmp_1148_: *mut LeanObject,
    mut v_m_1149_: *mut LeanObject,
    mut v_00_u03c3_1150_: *mut LeanObject,
    mut v_inst_1151_: *mut LeanObject,
    mut v_t_1152_: *mut LeanObject,
    mut v_init_1153_: *mut LeanObject,
    mut v_f_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1155_ = lean_ctor_get(v_inst_1151_, 0);
    v_toBind_1156_ = lean_ctor_get(v_inst_1151_, 1);
    lean_inc(v_toBind_1156_);
    v_toPure_1157_ = lean_ctor_get(v_toApplicative_1155_, 1);
    lean_inc(v_toPure_1157_);
    v___f_1158_ = lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1158_, 0, v_f_1154_);
    v___x_1159_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_1151_,
        v___f_1158_,
        v_t_1152_,
        v_init_1153_,
    );
    v___f_1160_ = lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1160_, 0, v_toPure_1157_);
    v___x_1161_ = lean_apply_4(
        v_toBind_1156_,
        lean_box(0),
        lean_box(0),
        v___x_1159_,
        v___f_1160_,
    );
    return v___x_1161_;
}
pub unsafe fn l_Lean_RBTree_forIn___boxed(
    mut v_00_u03b1_1162_: *mut LeanObject,
    mut v_cmp_1163_: *mut LeanObject,
    mut v_m_1164_: *mut LeanObject,
    mut v_00_u03c3_1165_: *mut LeanObject,
    mut v_inst_1166_: *mut LeanObject,
    mut v_t_1167_: *mut LeanObject,
    mut v_init_1168_: *mut LeanObject,
    mut v_f_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_RBTree_forIn(
        v_00_u03b1_1162_,
        v_cmp_1163_,
        v_m_1164_,
        v_00_u03c3_1165_,
        v_inst_1166_,
        v_t_1167_,
        v_init_1168_,
        v_f_1169_,
    );
    lean_dec_ref(v_cmp_1163_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg___lam__0(
    mut v___y_1171_: *mut LeanObject,
    mut v_a_1172_: *mut LeanObject,
    mut v_x_1173_: *mut LeanObject,
    mut v_acc_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = lean_apply_2(v___y_1171_, v_a_1172_, v_acc_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg___lam__2(
    mut v_inst_1176_: *mut LeanObject,
    mut v_00_u03b2_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1181_ = lean_ctor_get(v_inst_1176_, 0);
    v_toBind_1182_ = lean_ctor_get(v_inst_1176_, 1);
    lean_inc(v_toBind_1182_);
    v_toPure_1183_ = lean_ctor_get(v_toApplicative_1181_, 1);
    lean_inc(v_toPure_1183_);
    v___f_1184_ = lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1184_, 0, v___y_1180_);
    v___x_1185_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_1176_,
        v___f_1184_,
        v___y_1178_,
        v___y_1179_,
    );
    v___f_1186_ = lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1186_, 0, v_toPure_1183_);
    v___x_1187_ = lean_apply_4(
        v_toBind_1182_,
        lean_box(0),
        lean_box(0),
        v___x_1185_,
        v___f_1186_,
    );
    return v___x_1187_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg(
    mut v_inst_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1189_: *mut LeanObject = core::ptr::null_mut();
    v___f_1189_ = lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1189_, 0, v_inst_1188_);
    return v___f_1189_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad(
    mut v_00_u03b1_1190_: *mut LeanObject,
    mut v_cmp_1191_: *mut LeanObject,
    mut v_m_1192_: *mut LeanObject,
    mut v_inst_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1194_: *mut LeanObject = core::ptr::null_mut();
    v___f_1194_ = lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1194_, 0, v_inst_1193_);
    return v___f_1194_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___boxed(
    mut v_00_u03b1_1195_: *mut LeanObject,
    mut v_cmp_1196_: *mut LeanObject,
    mut v_m_1197_: *mut LeanObject,
    mut v_inst_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1199_: *mut LeanObject = core::ptr::null_mut();
    v_res_1199_ =
        l_Lean_RBTree_instForInOfMonad(v_00_u03b1_1195_, v_cmp_1196_, v_m_1197_, v_inst_1198_);
    lean_dec_ref(v_cmp_1196_);
    return v_res_1199_;
}
pub unsafe fn l_Lean_RBTree_isEmpty___redArg(mut v_t_1200_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_t_1200_) == 0 {
        let mut v___x_1201_: u8 = 0;
        v___x_1201_ = 1;
        return v___x_1201_;
    } else {
        let mut v___x_1202_: u8 = 0;
        v___x_1202_ = 0;
        return v___x_1202_;
    }
}
pub unsafe fn l_Lean_RBTree_isEmpty___redArg___boxed(
    mut v_t_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1204_: u8 = 0;
    let mut v_r_1205_: *mut LeanObject = core::ptr::null_mut();
    v_res_1204_ = l_Lean_RBTree_isEmpty___redArg(v_t_1203_);
    lean_dec(v_t_1203_);
    v_r_1205_ = lean_box((v_res_1204_) as usize);
    return v_r_1205_;
}
pub unsafe fn l_Lean_RBTree_isEmpty(
    mut v_00_u03b1_1206_: *mut LeanObject,
    mut v_cmp_1207_: *mut LeanObject,
    mut v_t_1208_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_t_1208_) == 0 {
        let mut v___x_1209_: u8 = 0;
        v___x_1209_ = 1;
        return v___x_1209_;
    } else {
        let mut v___x_1210_: u8 = 0;
        v___x_1210_ = 0;
        return v___x_1210_;
    }
}
pub unsafe fn l_Lean_RBTree_isEmpty___boxed(
    mut v_00_u03b1_1211_: *mut LeanObject,
    mut v_cmp_1212_: *mut LeanObject,
    mut v_t_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1214_: u8 = 0;
    let mut v_r_1215_: *mut LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Lean_RBTree_isEmpty(v_00_u03b1_1211_, v_cmp_1212_, v_t_1213_);
    lean_dec(v_t_1213_);
    lean_dec_ref(v_cmp_1212_);
    v_r_1215_ = lean_box((v_res_1214_) as usize);
    return v_r_1215_;
}
pub unsafe fn l_Lean_RBTree_toList___redArg___lam__0(
    mut v_r_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_x_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    v___x_1219_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1219_, 0, v_a_1217_);
    lean_ctor_set(v___x_1219_, 1, v_r_1216_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_RBTree_toList___redArg(mut v_t_1221_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___f_1222_ = l_Lean_RBTree_toList___redArg___closed__0;
    v___x_1223_ = lean_box(0);
    v___x_1224_ = l_Lean_RBNode_revFold___redArg(v___f_1222_, v___x_1223_, v_t_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_RBTree_toList(
    mut v_00_u03b1_1225_: *mut LeanObject,
    mut v_cmp_1226_: *mut LeanObject,
    mut v_t_1227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_Lean_RBTree_toList___redArg(v_t_1227_);
    return v___x_1228_;
}
pub unsafe fn l_Lean_RBTree_toList___boxed(
    mut v_00_u03b1_1229_: *mut LeanObject,
    mut v_cmp_1230_: *mut LeanObject,
    mut v_t_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_RBTree_toList(v_00_u03b1_1229_, v_cmp_1230_, v_t_1231_);
    lean_dec_ref(v_cmp_1230_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_RBTree_toArray___redArg___lam__0(
    mut v_r_1233_: *mut LeanObject,
    mut v_a_1234_: *mut LeanObject,
    mut v_x_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    v___x_1236_ = lean_array_push(v_r_1233_, v_a_1234_);
    return v___x_1236_;
}
pub unsafe fn l_Lean_RBTree_toArray___redArg(mut v_t_1240_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    v___f_1241_ = l_Lean_RBTree_toArray___redArg___closed__0;
    v___x_1242_ = l_Lean_RBTree_toArray___redArg___closed__1;
    v___x_1243_ = l_Lean_RBNode_fold___redArg(v___f_1241_, v___x_1242_, v_t_1240_);
    return v___x_1243_;
}
pub unsafe fn l_Lean_RBTree_toArray(
    mut v_00_u03b1_1244_: *mut LeanObject,
    mut v_cmp_1245_: *mut LeanObject,
    mut v_t_1246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_RBTree_toArray___redArg(v_t_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Lean_RBTree_toArray___boxed(
    mut v_00_u03b1_1248_: *mut LeanObject,
    mut v_cmp_1249_: *mut LeanObject,
    mut v_t_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_RBTree_toArray(v_00_u03b1_1248_, v_cmp_1249_, v_t_1250_);
    lean_dec_ref(v_cmp_1249_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_RBTree_min___redArg(mut v_t_1252_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v_fst_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = l_Lean_RBNode_min___redArg(v_t_1252_);
                if lean_obj_tag(v___x_1253_) == 0 {
                    v___x_1254_ = lean_box(0);
                    return v___x_1254_;
                } else {
                    v_val_1255_ = lean_ctor_get(v___x_1253_, 0);
                    v_isSharedCheck_1263_ = (!lean_is_exclusive(v___x_1253_)) as u8;
                    if v_isSharedCheck_1263_ == 0 {
                        v___x_1257_ = v___x_1253_;
                        v_isShared_1258_ = v_isSharedCheck_1263_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1255_);
                        lean_dec(v___x_1253_);
                        v___x_1257_ = lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1259_ = lean_ctor_get(v_val_1255_, 0);
                lean_inc(v_fst_1259_);
                lean_dec(v_val_1255_);
                if v_isShared_1258_ == 0 {
                    lean_ctor_set(v___x_1257_, 0, v_fst_1259_);
                    v___x_1261_ = v___x_1257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_fst_1259_);
                    v___x_1261_ = v_reuseFailAlloc_1262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_min___redArg___boxed(
    mut v_t_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_RBTree_min___redArg(v_t_1264_);
    lean_dec(v_t_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_RBTree_min(
    mut v_00_u03b1_1266_: *mut LeanObject,
    mut v_cmp_1267_: *mut LeanObject,
    mut v_t_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v_fst_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = l_Lean_RBNode_min___redArg(v_t_1268_);
                if lean_obj_tag(v___x_1269_) == 0 {
                    v___x_1270_ = lean_box(0);
                    return v___x_1270_;
                } else {
                    v_val_1271_ = lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1279_ = (!lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1273_ = v___x_1269_;
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1271_);
                        lean_dec(v___x_1269_);
                        v___x_1273_ = lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1275_ = lean_ctor_get(v_val_1271_, 0);
                lean_inc(v_fst_1275_);
                lean_dec(v_val_1271_);
                if v_isShared_1274_ == 0 {
                    lean_ctor_set(v___x_1273_, 0, v_fst_1275_);
                    v___x_1277_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_fst_1275_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_min___boxed(
    mut v_00_u03b1_1280_: *mut LeanObject,
    mut v_cmp_1281_: *mut LeanObject,
    mut v_t_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Lean_RBTree_min(v_00_u03b1_1280_, v_cmp_1281_, v_t_1282_);
    lean_dec(v_t_1282_);
    lean_dec_ref(v_cmp_1281_);
    return v_res_1283_;
}
pub unsafe fn l_Lean_RBTree_max___redArg(mut v_t_1284_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v_fst_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = l_Lean_RBNode_max___redArg(v_t_1284_);
                if lean_obj_tag(v___x_1285_) == 0 {
                    v___x_1286_ = lean_box(0);
                    return v___x_1286_;
                } else {
                    v_val_1287_ = lean_ctor_get(v___x_1285_, 0);
                    v_isSharedCheck_1295_ = (!lean_is_exclusive(v___x_1285_)) as u8;
                    if v_isSharedCheck_1295_ == 0 {
                        v___x_1289_ = v___x_1285_;
                        v_isShared_1290_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1287_);
                        lean_dec(v___x_1285_);
                        v___x_1289_ = lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1291_ = lean_ctor_get(v_val_1287_, 0);
                lean_inc(v_fst_1291_);
                lean_dec(v_val_1287_);
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 0, v_fst_1291_);
                    v___x_1293_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fst_1291_);
                    v___x_1293_ = v_reuseFailAlloc_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_max___redArg___boxed(
    mut v_t_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lean_RBTree_max___redArg(v_t_1296_);
    lean_dec(v_t_1296_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_RBTree_max(
    mut v_00_u03b1_1298_: *mut LeanObject,
    mut v_cmp_1299_: *mut LeanObject,
    mut v_t_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1306_: u8 = 0;
    let mut v_fst_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1301_ = l_Lean_RBNode_max___redArg(v_t_1300_);
                if lean_obj_tag(v___x_1301_) == 0 {
                    v___x_1302_ = lean_box(0);
                    return v___x_1302_;
                } else {
                    v_val_1303_ = lean_ctor_get(v___x_1301_, 0);
                    v_isSharedCheck_1311_ = (!lean_is_exclusive(v___x_1301_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1305_ = v___x_1301_;
                        v_isShared_1306_ = v_isSharedCheck_1311_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1303_);
                        lean_dec(v___x_1301_);
                        v___x_1305_ = lean_box(0);
                        v_isShared_1306_ = v_isSharedCheck_1311_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1307_ = lean_ctor_get(v_val_1303_, 0);
                lean_inc(v_fst_1307_);
                lean_dec(v_val_1303_);
                if v_isShared_1306_ == 0 {
                    lean_ctor_set(v___x_1305_, 0, v_fst_1307_);
                    v___x_1309_ = v___x_1305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_fst_1307_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_max___boxed(
    mut v_00_u03b1_1312_: *mut LeanObject,
    mut v_cmp_1313_: *mut LeanObject,
    mut v_t_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1315_: *mut LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_RBTree_max(v_00_u03b1_1312_, v_cmp_1313_, v_t_1314_);
    lean_dec(v_t_1314_);
    lean_dec_ref(v_cmp_1313_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg___lam__0(
    mut v_inst_1319_: *mut LeanObject,
    mut v_t_1320_: *mut LeanObject,
    mut v_prec_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_RBTree_instRepr___redArg___lam__0___closed__1;
    v___x_1323_ = l_Lean_RBTree_toList___redArg(v_t_1320_);
    v___x_1324_ = l_List_repr___redArg(v_inst_1319_, v___x_1323_);
    v___x_1325_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1325_, 0, v___x_1322_);
    lean_ctor_set(v___x_1325_, 1, v___x_1324_);
    v___x_1326_ = l_Repr_addAppParen(v___x_1325_, v_prec_1321_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg___lam__0___boxed(
    mut v_inst_1327_: *mut LeanObject,
    mut v_t_1328_: *mut LeanObject,
    mut v_prec_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_RBTree_instRepr___redArg___lam__0(v_inst_1327_, v_t_1328_, v_prec_1329_);
    lean_dec(v_prec_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg(
    mut v_inst_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1332_: *mut LeanObject = core::ptr::null_mut();
    v___f_1332_ = lean_alloc_closure(
        l_Lean_RBTree_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1332_, 0, v_inst_1331_);
    return v___f_1332_;
}
pub unsafe fn l_Lean_RBTree_instRepr(
    mut v_00_u03b1_1333_: *mut LeanObject,
    mut v_cmp_1334_: *mut LeanObject,
    mut v_inst_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1336_: *mut LeanObject = core::ptr::null_mut();
    v___f_1336_ = lean_alloc_closure(
        l_Lean_RBTree_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1336_, 0, v_inst_1335_);
    return v___f_1336_;
}
pub unsafe fn l_Lean_RBTree_instRepr___boxed(
    mut v_00_u03b1_1337_: *mut LeanObject,
    mut v_cmp_1338_: *mut LeanObject,
    mut v_inst_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_RBTree_instRepr(v_00_u03b1_1337_, v_cmp_1338_, v_inst_1339_);
    lean_dec_ref(v_cmp_1338_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_RBTree_insert___redArg(
    mut v_cmp_1341_: *mut LeanObject,
    mut v_t_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    v___x_1344_ = lean_box(0);
    v___x_1345_ = l_Lean_RBNode_insert___redArg(v_cmp_1341_, v_t_1342_, v_a_1343_, v___x_1344_);
    return v___x_1345_;
}
pub unsafe fn l_Lean_RBTree_insert(
    mut v_00_u03b1_1346_: *mut LeanObject,
    mut v_cmp_1347_: *mut LeanObject,
    mut v_t_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350_ = lean_box(0);
    v___x_1351_ = l_Lean_RBNode_insert___redArg(v_cmp_1347_, v_t_1348_, v_a_1349_, v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_RBTree_erase___redArg(
    mut v_cmp_1352_: *mut LeanObject,
    mut v_t_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_RBNode_erase___redArg(v_cmp_1352_, v_a_1354_, v_t_1353_);
    return v___x_1355_;
}
pub unsafe fn l_Lean_RBTree_erase(
    mut v_00_u03b1_1356_: *mut LeanObject,
    mut v_cmp_1357_: *mut LeanObject,
    mut v_t_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_RBNode_erase___redArg(v_cmp_1357_, v_a_1359_, v_t_1358_);
    return v___x_1360_;
}
pub unsafe fn l_Lean_RBTree_ofList___redArg(
    mut v_cmp_1361_: *mut LeanObject,
    mut v_x_1362_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1362_) == 0 {
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_cmp_1361_);
        v___x_1363_ = lean_box(0);
        return v___x_1363_;
    } else {
        let mut v_head_1364_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
        v_head_1364_ = lean_ctor_get(v_x_1362_, 0);
        lean_inc(v_head_1364_);
        v_tail_1365_ = lean_ctor_get(v_x_1362_, 1);
        lean_inc(v_tail_1365_);
        lean_dec_ref_known(v_x_1362_, 2);
        lean_inc_ref(v_cmp_1361_);
        v_val_1366_ = l_Lean_RBTree_ofList___redArg(v_cmp_1361_, v_tail_1365_);
        v___x_1367_ = lean_box(0);
        v___x_1368_ =
            l_Lean_RBNode_insert___redArg(v_cmp_1361_, v_val_1366_, v_head_1364_, v___x_1367_);
        return v___x_1368_;
    }
}
pub unsafe fn l_Lean_RBTree_ofList(
    mut v_00_u03b1_1369_: *mut LeanObject,
    mut v_cmp_1370_: *mut LeanObject,
    mut v_x_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_RBTree_ofList___redArg(v_cmp_1370_, v_x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Lean_RBTree_find_x3f___redArg(
    mut v_cmp_1373_: *mut LeanObject,
    mut v_t_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v_fst_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1376_ = l_Lean_RBNode_findCore___redArg(v_cmp_1373_, v_t_1374_, v_a_1375_);
                if lean_obj_tag(v___x_1376_) == 0 {
                    v___x_1377_ = lean_box(0);
                    return v___x_1377_;
                } else {
                    v_val_1378_ = lean_ctor_get(v___x_1376_, 0);
                    v_isSharedCheck_1386_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1380_ = v___x_1376_;
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1378_);
                        lean_dec(v___x_1376_);
                        v___x_1380_ = lean_box(0);
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1382_ = lean_ctor_get(v_val_1378_, 0);
                lean_inc(v_fst_1382_);
                lean_dec(v_val_1378_);
                if v_isShared_1381_ == 0 {
                    lean_ctor_set(v___x_1380_, 0, v_fst_1382_);
                    v___x_1384_ = v___x_1380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_fst_1382_);
                    v___x_1384_ = v_reuseFailAlloc_1385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_find_x3f(
    mut v_00_u03b1_1387_: *mut LeanObject,
    mut v_cmp_1388_: *mut LeanObject,
    mut v_t_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1396_: u8 = 0;
    let mut v_fst_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1391_ = l_Lean_RBNode_findCore___redArg(v_cmp_1388_, v_t_1389_, v_a_1390_);
                if lean_obj_tag(v___x_1391_) == 0 {
                    v___x_1392_ = lean_box(0);
                    return v___x_1392_;
                } else {
                    v_val_1393_ = lean_ctor_get(v___x_1391_, 0);
                    v_isSharedCheck_1401_ = (!lean_is_exclusive(v___x_1391_)) as u8;
                    if v_isSharedCheck_1401_ == 0 {
                        v___x_1395_ = v___x_1391_;
                        v_isShared_1396_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1393_);
                        lean_dec(v___x_1391_);
                        v___x_1395_ = lean_box(0);
                        v_isShared_1396_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1397_ = lean_ctor_get(v_val_1393_, 0);
                lean_inc(v_fst_1397_);
                lean_dec(v_val_1393_);
                if v_isShared_1396_ == 0 {
                    lean_ctor_set(v___x_1395_, 0, v_fst_1397_);
                    v___x_1399_ = v___x_1395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_fst_1397_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_contains___redArg(
    mut v_cmp_1402_: *mut LeanObject,
    mut v_t_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
) -> u8 {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Lean_RBNode_findCore___redArg(v_cmp_1402_, v_t_1403_, v_a_1404_);
    if lean_obj_tag(v___x_1405_) == 0 {
        let mut v___x_1406_: u8 = 0;
        v___x_1406_ = 0;
        return v___x_1406_;
    } else {
        let mut v___x_1407_: u8 = 0;
        lean_dec_ref_known(v___x_1405_, 1);
        v___x_1407_ = 1;
        return v___x_1407_;
    }
}
pub unsafe fn l_Lean_RBTree_contains___redArg___boxed(
    mut v_cmp_1408_: *mut LeanObject,
    mut v_t_1409_: *mut LeanObject,
    mut v_a_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1411_: u8 = 0;
    let mut v_r_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_RBTree_contains___redArg(v_cmp_1408_, v_t_1409_, v_a_1410_);
    v_r_1412_ = lean_box((v_res_1411_) as usize);
    return v_r_1412_;
}
pub unsafe fn l_Lean_RBTree_contains(
    mut v_00_u03b1_1413_: *mut LeanObject,
    mut v_cmp_1414_: *mut LeanObject,
    mut v_t_1415_: *mut LeanObject,
    mut v_a_1416_: *mut LeanObject,
) -> u8 {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_RBNode_findCore___redArg(v_cmp_1414_, v_t_1415_, v_a_1416_);
    if lean_obj_tag(v___x_1417_) == 0 {
        let mut v___x_1418_: u8 = 0;
        v___x_1418_ = 0;
        return v___x_1418_;
    } else {
        let mut v___x_1419_: u8 = 0;
        lean_dec_ref_known(v___x_1417_, 1);
        v___x_1419_ = 1;
        return v___x_1419_;
    }
}
pub unsafe fn l_Lean_RBTree_contains___boxed(
    mut v_00_u03b1_1420_: *mut LeanObject,
    mut v_cmp_1421_: *mut LeanObject,
    mut v_t_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lean_RBTree_contains(v_00_u03b1_1420_, v_cmp_1421_, v_t_1422_, v_a_1423_);
    v_r_1425_ = lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(
    mut v_cmp_1426_: *mut LeanObject,
    mut v_x_1427_: *mut LeanObject,
    mut v_x_1428_: *mut LeanObject,
    mut v_x_1429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1432_: u8 = 0;
    let mut v_lchild_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_lchild_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1464_: u8 = 0;
    let mut v_lchild_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kx_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vx_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ky_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vy_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kz_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vz_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1485_: u8 = 0;
    let mut v_lchild_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1490_: u8 = 0;
    let mut v_lchild_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1517_: u8 = 0;
    let mut v_lchild_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v_unused_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1542_: u8 = 0;
    let mut v_lchild_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kx_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vx_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ky_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vy_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kz_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vz_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1563_: u8 = 0;
    let mut v_lchild_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1568_: u8 = 0;
    let mut v_lchild_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_unused_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_unused_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_color_1595_: u8 = 0;
    let mut v_lchild_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1427_) == 0 {
                    lean_dec_ref(v_cmp_1426_);
                    v___x_1430_ = 0;
                    v___x_1431_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v___x_1431_, 0, v_x_1427_);
                    lean_ctor_set(v___x_1431_, 1, v_x_1428_);
                    lean_ctor_set(v___x_1431_, 2, v_x_1429_);
                    lean_ctor_set(v___x_1431_, 3, v_x_1427_);
                    lean_ctor_set_uint8(
                        v___x_1431_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_1430_,
                    );
                    return v___x_1431_;
                } else {
                    v_color_1432_ = lean_ctor_get_uint8(
                        v_x_1427_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    if v_color_1432_ == 0 {
                        v_lchild_1433_ = lean_ctor_get(v_x_1427_, 0);
                        v_key_1434_ = lean_ctor_get(v_x_1427_, 1);
                        v_val_1435_ = lean_ctor_get(v_x_1427_, 2);
                        v_rchild_1436_ = lean_ctor_get(v_x_1427_, 3);
                        v_isSharedCheck_1453_ = (!lean_is_exclusive(v_x_1427_)) as u8;
                        if v_isSharedCheck_1453_ == 0 {
                            v___x_1438_ = v_x_1427_;
                            v_isShared_1439_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_rchild_1436_);
                            lean_inc(v_val_1435_);
                            lean_inc(v_key_1434_);
                            lean_inc(v_lchild_1433_);
                            lean_dec(v_x_1427_);
                            v___x_1438_ = lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_lchild_1454_ = lean_ctor_get(v_x_1427_, 0);
                        v_key_1455_ = lean_ctor_get(v_x_1427_, 1);
                        v_val_1456_ = lean_ctor_get(v_x_1427_, 2);
                        v_rchild_1457_ = lean_ctor_get(v_x_1427_, 3);
                        v_isSharedCheck_1616_ = (!lean_is_exclusive(v_x_1427_)) as u8;
                        if v_isSharedCheck_1616_ == 0 {
                            v___x_1459_ = v_x_1427_;
                            v_isShared_1460_ = v_isSharedCheck_1616_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_rchild_1457_);
                            lean_inc(v_val_1456_);
                            lean_inc(v_key_1455_);
                            lean_inc(v_lchild_1454_);
                            lean_dec(v_x_1427_);
                            v___x_1459_ = lean_box(0);
                            v_isShared_1460_ = v_isSharedCheck_1616_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v_cmp_1426_);
                lean_inc(v_key_1434_);
                lean_inc(v_x_1428_);
                v___x_1440_ = lean_apply_2(v_cmp_1426_, v_x_1428_, v_key_1434_);
                v___x_1441_ = (lean_unbox(v___x_1440_) as u8);
                match v___x_1441_ {
                    0 => {
                        v___x_1442_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_lchild_1433_, v_x_1428_, v_x_1429_);
                        if v_isShared_1439_ == 0 {
                            lean_ctor_set(v___x_1438_, 0, v___x_1442_);
                            v___x_1444_ = v___x_1438_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 4, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                            lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_key_1434_);
                            lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_val_1435_);
                            lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_rchild_1436_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_1445_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1444_ = v_reuseFailAlloc_1445_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec(v_val_1435_);
                        lean_dec(v_key_1434_);
                        lean_dec_ref(v_cmp_1426_);
                        if v_isShared_1439_ == 0 {
                            lean_ctor_set(v___x_1438_, 2, v_x_1429_);
                            lean_ctor_set(v___x_1438_, 1, v_x_1428_);
                            v___x_1447_ = v___x_1438_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 4, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_lchild_1433_);
                            lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_x_1428_);
                            lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_x_1429_);
                            lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_rchild_1436_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_1448_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1447_ = v_reuseFailAlloc_1448_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1449_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_rchild_1436_, v_x_1428_, v_x_1429_);
                        if v_isShared_1439_ == 0 {
                            lean_ctor_set(v___x_1438_, 3, v___x_1449_);
                            v___x_1451_ = v___x_1438_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 4, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_lchild_1433_);
                            lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_key_1434_);
                            lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_val_1435_);
                            lean_ctor_set(v_reuseFailAlloc_1452_, 3, v___x_1449_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_1452_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1451_ = v_reuseFailAlloc_1452_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1444_;
            }
            3 => {
                return v___x_1447_;
            }
            4 => {
                return v___x_1451_;
            }
            5 => {
                lean_inc_ref(v_cmp_1426_);
                lean_inc(v_key_1455_);
                lean_inc(v_x_1428_);
                v___x_1461_ = lean_apply_2(v_cmp_1426_, v_x_1428_, v_key_1455_);
                v___x_1462_ = (lean_unbox(v___x_1461_) as u8);
                match v___x_1462_ {
                    0 => {
                        v___x_1463_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_lchild_1454_, v_x_1428_, v_x_1429_);
                        if lean_obj_tag(v___x_1463_) == 1 {
                            v_color_1464_ = lean_ctor_get_uint8(
                                v___x_1463_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                            );
                            v_lchild_1465_ = lean_ctor_get(v___x_1463_, 0);
                            lean_inc(v_lchild_1465_);
                            v_key_1466_ = lean_ctor_get(v___x_1463_, 1);
                            lean_inc(v_key_1466_);
                            v_val_1467_ = lean_ctor_get(v___x_1463_, 2);
                            lean_inc(v_val_1467_);
                            v_rchild_1468_ = lean_ctor_get(v___x_1463_, 3);
                            lean_inc(v_rchild_1468_);
                            if v_color_1464_ == 0 {
                                if lean_obj_tag(v_lchild_1465_) == 1 {
                                    v_color_1485_ = lean_ctor_get_uint8(
                                        v_lchild_1465_,
                                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    );
                                    if v_color_1485_ == 0 {
                                        lean_dec_ref_known(v___x_1463_, 4);
                                        v_lchild_1486_ = lean_ctor_get(v_lchild_1465_, 0);
                                        lean_inc(v_lchild_1486_);
                                        v_key_1487_ = lean_ctor_get(v_lchild_1465_, 1);
                                        lean_inc(v_key_1487_);
                                        v_val_1488_ = lean_ctor_get(v_lchild_1465_, 2);
                                        lean_inc(v_val_1488_);
                                        v_rchild_1489_ = lean_ctor_get(v_lchild_1465_, 3);
                                        lean_inc(v_rchild_1489_);
                                        lean_dec_ref_known(v_lchild_1465_, 4);
                                        v_a_1470_ = v_lchild_1486_;
                                        v_kx_1471_ = v_key_1487_;
                                        v_vx_1472_ = v_val_1488_;
                                        v_b_1473_ = v_rchild_1489_;
                                        v_ky_1474_ = v_key_1466_;
                                        v_vy_1475_ = v_val_1467_;
                                        v_c_1476_ = v_rchild_1468_;
                                        v_kz_1477_ = v_key_1455_;
                                        v_vz_1478_ = v_val_1456_;
                                        v_d_1479_ = v_rchild_1457_;
                                        state = 6;
                                        continue;
                                    } else {
                                        if lean_obj_tag(v_rchild_1468_) == 1 {
                                            v_color_1490_ = lean_ctor_get_uint8(
                                                v_rchild_1468_,
                                                (core::mem::size_of::<*mut LeanObject>() * 4)
                                                    as u32,
                                            );
                                            if v_color_1490_ == 0 {
                                                lean_dec_ref_known(v___x_1463_, 4);
                                                v_lchild_1491_ = lean_ctor_get(v_rchild_1468_, 0);
                                                lean_inc(v_lchild_1491_);
                                                v_key_1492_ = lean_ctor_get(v_rchild_1468_, 1);
                                                lean_inc(v_key_1492_);
                                                v_val_1493_ = lean_ctor_get(v_rchild_1468_, 2);
                                                lean_inc(v_val_1493_);
                                                v_rchild_1494_ = lean_ctor_get(v_rchild_1468_, 3);
                                                lean_inc(v_rchild_1494_);
                                                lean_dec_ref_known(v_rchild_1468_, 4);
                                                v_a_1470_ = v_lchild_1465_;
                                                v_kx_1471_ = v_key_1466_;
                                                v_vx_1472_ = v_val_1467_;
                                                v_b_1473_ = v_lchild_1491_;
                                                v_ky_1474_ = v_key_1492_;
                                                v_vy_1475_ = v_val_1493_;
                                                v_c_1476_ = v_rchild_1494_;
                                                v_kz_1477_ = v_key_1455_;
                                                v_vz_1478_ = v_val_1456_;
                                                v_d_1479_ = v_rchild_1457_;
                                                state = 6;
                                                continue;
                                            } else {
                                                lean_dec_ref_known(v_lchild_1465_, 4);
                                                lean_dec(v_val_1467_);
                                                lean_dec(v_key_1466_);
                                                lean_del_object(v___x_1459_);
                                                v_isSharedCheck_1501_ =
                                                    (!lean_is_exclusive(v_rchild_1468_)) as u8;
                                                if v_isSharedCheck_1501_ == 0 {
                                                    v_unused_1502_ =
                                                        lean_ctor_get(v_rchild_1468_, 3);
                                                    lean_dec(v_unused_1502_);
                                                    v_unused_1503_ =
                                                        lean_ctor_get(v_rchild_1468_, 2);
                                                    lean_dec(v_unused_1503_);
                                                    v_unused_1504_ =
                                                        lean_ctor_get(v_rchild_1468_, 1);
                                                    lean_dec(v_unused_1504_);
                                                    v_unused_1505_ =
                                                        lean_ctor_get(v_rchild_1468_, 0);
                                                    lean_dec(v_unused_1505_);
                                                    v___x_1496_ = v_rchild_1468_;
                                                    v_isShared_1497_ = v_isSharedCheck_1501_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_dec(v_rchild_1468_);
                                                    v___x_1496_ = lean_box(0);
                                                    v_isShared_1497_ = v_isSharedCheck_1501_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_rchild_1468_);
                                            lean_dec(v_val_1467_);
                                            lean_dec(v_key_1466_);
                                            lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1512_ =
                                                (!lean_is_exclusive(v_lchild_1465_)) as u8;
                                            if v_isSharedCheck_1512_ == 0 {
                                                v_unused_1513_ = lean_ctor_get(v_lchild_1465_, 3);
                                                lean_dec(v_unused_1513_);
                                                v_unused_1514_ = lean_ctor_get(v_lchild_1465_, 2);
                                                lean_dec(v_unused_1514_);
                                                v_unused_1515_ = lean_ctor_get(v_lchild_1465_, 1);
                                                lean_dec(v_unused_1515_);
                                                v_unused_1516_ = lean_ctor_get(v_lchild_1465_, 0);
                                                lean_dec(v_unused_1516_);
                                                v___x_1507_ = v_lchild_1465_;
                                                v_isShared_1508_ = v_isSharedCheck_1512_;
                                                state = 10;
                                                continue;
                                            } else {
                                                lean_dec(v_lchild_1465_);
                                                v___x_1507_ = lean_box(0);
                                                v_isShared_1508_ = v_isSharedCheck_1512_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if lean_obj_tag(v_rchild_1468_) == 1 {
                                        v_color_1517_ = lean_ctor_get_uint8(
                                            v_rchild_1468_,
                                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                        );
                                        if v_color_1517_ == 0 {
                                            lean_dec_ref_known(v___x_1463_, 4);
                                            v_lchild_1518_ = lean_ctor_get(v_rchild_1468_, 0);
                                            lean_inc(v_lchild_1518_);
                                            v_key_1519_ = lean_ctor_get(v_rchild_1468_, 1);
                                            lean_inc(v_key_1519_);
                                            v_val_1520_ = lean_ctor_get(v_rchild_1468_, 2);
                                            lean_inc(v_val_1520_);
                                            v_rchild_1521_ = lean_ctor_get(v_rchild_1468_, 3);
                                            lean_inc(v_rchild_1521_);
                                            lean_dec_ref_known(v_rchild_1468_, 4);
                                            v_a_1470_ = v_lchild_1465_;
                                            v_kx_1471_ = v_key_1466_;
                                            v_vx_1472_ = v_val_1467_;
                                            v_b_1473_ = v_lchild_1518_;
                                            v_ky_1474_ = v_key_1519_;
                                            v_vy_1475_ = v_val_1520_;
                                            v_c_1476_ = v_rchild_1521_;
                                            v_kz_1477_ = v_key_1455_;
                                            v_vz_1478_ = v_val_1456_;
                                            v_d_1479_ = v_rchild_1457_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_dec(v_val_1467_);
                                            lean_dec(v_key_1466_);
                                            lean_dec(v_lchild_1465_);
                                            lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1528_ =
                                                (!lean_is_exclusive(v_rchild_1468_)) as u8;
                                            if v_isSharedCheck_1528_ == 0 {
                                                v_unused_1529_ = lean_ctor_get(v_rchild_1468_, 3);
                                                lean_dec(v_unused_1529_);
                                                v_unused_1530_ = lean_ctor_get(v_rchild_1468_, 2);
                                                lean_dec(v_unused_1530_);
                                                v_unused_1531_ = lean_ctor_get(v_rchild_1468_, 1);
                                                lean_dec(v_unused_1531_);
                                                v_unused_1532_ = lean_ctor_get(v_rchild_1468_, 0);
                                                lean_dec(v_unused_1532_);
                                                v___x_1523_ = v_rchild_1468_;
                                                v_isShared_1524_ = v_isSharedCheck_1528_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_dec(v_rchild_1468_);
                                                v___x_1523_ = lean_box(0);
                                                v_isShared_1524_ = v_isSharedCheck_1528_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_rchild_1468_);
                                        lean_dec(v_val_1467_);
                                        lean_dec(v_key_1466_);
                                        lean_dec(v_lchild_1465_);
                                        lean_del_object(v___x_1459_);
                                        v___x_1533_ = lean_alloc_ctor(1, 4, (1) as u32);
                                        lean_ctor_set(v___x_1533_, 0, v___x_1463_);
                                        lean_ctor_set(v___x_1533_, 1, v_key_1455_);
                                        lean_ctor_set(v___x_1533_, 2, v_val_1456_);
                                        lean_ctor_set(v___x_1533_, 3, v_rchild_1457_);
                                        lean_ctor_set_uint8(
                                            v___x_1533_,
                                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                            v_color_1432_,
                                        );
                                        return v___x_1533_;
                                    }
                                }
                            } else {
                                lean_dec(v_rchild_1468_);
                                lean_dec(v_val_1467_);
                                lean_dec(v_key_1466_);
                                lean_dec(v_lchild_1465_);
                                lean_del_object(v___x_1459_);
                                v___x_1534_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v___x_1534_, 0, v___x_1463_);
                                lean_ctor_set(v___x_1534_, 1, v_key_1455_);
                                lean_ctor_set(v___x_1534_, 2, v_val_1456_);
                                lean_ctor_set(v___x_1534_, 3, v_rchild_1457_);
                                lean_ctor_set_uint8(
                                    v___x_1534_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v_color_1432_,
                                );
                                return v___x_1534_;
                            }
                        } else {
                            if v_isShared_1460_ == 0 {
                                lean_ctor_set(v___x_1459_, 0, v___x_1463_);
                                v___x_1536_ = v___x_1459_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1463_);
                                lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_key_1455_);
                                lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_val_1456_);
                                lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_rchild_1457_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_1537_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v_color_1432_,
                                );
                                v___x_1536_ = v_reuseFailAlloc_1537_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_val_1456_);
                        lean_dec(v_key_1455_);
                        lean_dec_ref(v_cmp_1426_);
                        if v_isShared_1460_ == 0 {
                            lean_ctor_set(v___x_1459_, 2, v_x_1429_);
                            lean_ctor_set(v___x_1459_, 1, v_x_1428_);
                            v___x_1539_ = v___x_1459_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 4, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_lchild_1454_);
                            lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_x_1428_);
                            lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_x_1429_);
                            lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_rchild_1457_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_1540_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1539_ = v_reuseFailAlloc_1540_;
                            state = 15;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1541_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_rchild_1457_, v_x_1428_, v_x_1429_);
                        if lean_obj_tag(v___x_1541_) == 1 {
                            v_color_1542_ = lean_ctor_get_uint8(
                                v___x_1541_,
                                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                            );
                            v_lchild_1543_ = lean_ctor_get(v___x_1541_, 0);
                            lean_inc(v_lchild_1543_);
                            v_key_1544_ = lean_ctor_get(v___x_1541_, 1);
                            lean_inc(v_key_1544_);
                            v_val_1545_ = lean_ctor_get(v___x_1541_, 2);
                            lean_inc(v_val_1545_);
                            v_rchild_1546_ = lean_ctor_get(v___x_1541_, 3);
                            lean_inc(v_rchild_1546_);
                            if v_color_1542_ == 0 {
                                if lean_obj_tag(v_lchild_1543_) == 1 {
                                    v_color_1563_ = lean_ctor_get_uint8(
                                        v_lchild_1543_,
                                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    );
                                    if v_color_1563_ == 0 {
                                        lean_dec_ref_known(v___x_1541_, 4);
                                        v_lchild_1564_ = lean_ctor_get(v_lchild_1543_, 0);
                                        lean_inc(v_lchild_1564_);
                                        v_key_1565_ = lean_ctor_get(v_lchild_1543_, 1);
                                        lean_inc(v_key_1565_);
                                        v_val_1566_ = lean_ctor_get(v_lchild_1543_, 2);
                                        lean_inc(v_val_1566_);
                                        v_rchild_1567_ = lean_ctor_get(v_lchild_1543_, 3);
                                        lean_inc(v_rchild_1567_);
                                        lean_dec_ref_known(v_lchild_1543_, 4);
                                        v_a_1548_ = v_lchild_1454_;
                                        v_kx_1549_ = v_key_1455_;
                                        v_vx_1550_ = v_val_1456_;
                                        v_b_1551_ = v_lchild_1564_;
                                        v_ky_1552_ = v_key_1565_;
                                        v_vy_1553_ = v_val_1566_;
                                        v_c_1554_ = v_rchild_1567_;
                                        v_kz_1555_ = v_key_1544_;
                                        v_vz_1556_ = v_val_1545_;
                                        v_d_1557_ = v_rchild_1546_;
                                        state = 16;
                                        continue;
                                    } else {
                                        if lean_obj_tag(v_rchild_1546_) == 1 {
                                            v_color_1568_ = lean_ctor_get_uint8(
                                                v_rchild_1546_,
                                                (core::mem::size_of::<*mut LeanObject>() * 4)
                                                    as u32,
                                            );
                                            if v_color_1568_ == 0 {
                                                lean_dec_ref_known(v___x_1541_, 4);
                                                v_lchild_1569_ = lean_ctor_get(v_rchild_1546_, 0);
                                                lean_inc(v_lchild_1569_);
                                                v_key_1570_ = lean_ctor_get(v_rchild_1546_, 1);
                                                lean_inc(v_key_1570_);
                                                v_val_1571_ = lean_ctor_get(v_rchild_1546_, 2);
                                                lean_inc(v_val_1571_);
                                                v_rchild_1572_ = lean_ctor_get(v_rchild_1546_, 3);
                                                lean_inc(v_rchild_1572_);
                                                lean_dec_ref_known(v_rchild_1546_, 4);
                                                v_a_1548_ = v_lchild_1454_;
                                                v_kx_1549_ = v_key_1455_;
                                                v_vx_1550_ = v_val_1456_;
                                                v_b_1551_ = v_lchild_1543_;
                                                v_ky_1552_ = v_key_1544_;
                                                v_vy_1553_ = v_val_1545_;
                                                v_c_1554_ = v_lchild_1569_;
                                                v_kz_1555_ = v_key_1570_;
                                                v_vz_1556_ = v_val_1571_;
                                                v_d_1557_ = v_rchild_1572_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_dec_ref_known(v_lchild_1543_, 4);
                                                lean_dec(v_val_1545_);
                                                lean_dec(v_key_1544_);
                                                lean_del_object(v___x_1459_);
                                                v_isSharedCheck_1579_ =
                                                    (!lean_is_exclusive(v_rchild_1546_)) as u8;
                                                if v_isSharedCheck_1579_ == 0 {
                                                    v_unused_1580_ =
                                                        lean_ctor_get(v_rchild_1546_, 3);
                                                    lean_dec(v_unused_1580_);
                                                    v_unused_1581_ =
                                                        lean_ctor_get(v_rchild_1546_, 2);
                                                    lean_dec(v_unused_1581_);
                                                    v_unused_1582_ =
                                                        lean_ctor_get(v_rchild_1546_, 1);
                                                    lean_dec(v_unused_1582_);
                                                    v_unused_1583_ =
                                                        lean_ctor_get(v_rchild_1546_, 0);
                                                    lean_dec(v_unused_1583_);
                                                    v___x_1574_ = v_rchild_1546_;
                                                    v_isShared_1575_ = v_isSharedCheck_1579_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_dec(v_rchild_1546_);
                                                    v___x_1574_ = lean_box(0);
                                                    v_isShared_1575_ = v_isSharedCheck_1579_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_rchild_1546_);
                                            lean_dec(v_val_1545_);
                                            lean_dec(v_key_1544_);
                                            lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1590_ =
                                                (!lean_is_exclusive(v_lchild_1543_)) as u8;
                                            if v_isSharedCheck_1590_ == 0 {
                                                v_unused_1591_ = lean_ctor_get(v_lchild_1543_, 3);
                                                lean_dec(v_unused_1591_);
                                                v_unused_1592_ = lean_ctor_get(v_lchild_1543_, 2);
                                                lean_dec(v_unused_1592_);
                                                v_unused_1593_ = lean_ctor_get(v_lchild_1543_, 1);
                                                lean_dec(v_unused_1593_);
                                                v_unused_1594_ = lean_ctor_get(v_lchild_1543_, 0);
                                                lean_dec(v_unused_1594_);
                                                v___x_1585_ = v_lchild_1543_;
                                                v_isShared_1586_ = v_isSharedCheck_1590_;
                                                state = 20;
                                                continue;
                                            } else {
                                                lean_dec(v_lchild_1543_);
                                                v___x_1585_ = lean_box(0);
                                                v_isShared_1586_ = v_isSharedCheck_1590_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if lean_obj_tag(v_rchild_1546_) == 1 {
                                        v_color_1595_ = lean_ctor_get_uint8(
                                            v_rchild_1546_,
                                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                        );
                                        if v_color_1595_ == 0 {
                                            lean_dec_ref_known(v___x_1541_, 4);
                                            v_lchild_1596_ = lean_ctor_get(v_rchild_1546_, 0);
                                            lean_inc(v_lchild_1596_);
                                            v_key_1597_ = lean_ctor_get(v_rchild_1546_, 1);
                                            lean_inc(v_key_1597_);
                                            v_val_1598_ = lean_ctor_get(v_rchild_1546_, 2);
                                            lean_inc(v_val_1598_);
                                            v_rchild_1599_ = lean_ctor_get(v_rchild_1546_, 3);
                                            lean_inc(v_rchild_1599_);
                                            lean_dec_ref_known(v_rchild_1546_, 4);
                                            v_a_1548_ = v_lchild_1454_;
                                            v_kx_1549_ = v_key_1455_;
                                            v_vx_1550_ = v_val_1456_;
                                            v_b_1551_ = v_lchild_1543_;
                                            v_ky_1552_ = v_key_1544_;
                                            v_vy_1553_ = v_val_1545_;
                                            v_c_1554_ = v_lchild_1596_;
                                            v_kz_1555_ = v_key_1597_;
                                            v_vz_1556_ = v_val_1598_;
                                            v_d_1557_ = v_rchild_1599_;
                                            state = 16;
                                            continue;
                                        } else {
                                            lean_dec(v_val_1545_);
                                            lean_dec(v_key_1544_);
                                            lean_dec(v_lchild_1543_);
                                            lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1606_ =
                                                (!lean_is_exclusive(v_rchild_1546_)) as u8;
                                            if v_isSharedCheck_1606_ == 0 {
                                                v_unused_1607_ = lean_ctor_get(v_rchild_1546_, 3);
                                                lean_dec(v_unused_1607_);
                                                v_unused_1608_ = lean_ctor_get(v_rchild_1546_, 2);
                                                lean_dec(v_unused_1608_);
                                                v_unused_1609_ = lean_ctor_get(v_rchild_1546_, 1);
                                                lean_dec(v_unused_1609_);
                                                v_unused_1610_ = lean_ctor_get(v_rchild_1546_, 0);
                                                lean_dec(v_unused_1610_);
                                                v___x_1601_ = v_rchild_1546_;
                                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                                state = 22;
                                                continue;
                                            } else {
                                                lean_dec(v_rchild_1546_);
                                                v___x_1601_ = lean_box(0);
                                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                                state = 22;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_rchild_1546_);
                                        lean_dec(v_val_1545_);
                                        lean_dec(v_key_1544_);
                                        lean_dec(v_lchild_1543_);
                                        lean_del_object(v___x_1459_);
                                        v___x_1611_ = lean_alloc_ctor(1, 4, (1) as u32);
                                        lean_ctor_set(v___x_1611_, 0, v_lchild_1454_);
                                        lean_ctor_set(v___x_1611_, 1, v_key_1455_);
                                        lean_ctor_set(v___x_1611_, 2, v_val_1456_);
                                        lean_ctor_set(v___x_1611_, 3, v___x_1541_);
                                        lean_ctor_set_uint8(
                                            v___x_1611_,
                                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                            v_color_1432_,
                                        );
                                        return v___x_1611_;
                                    }
                                }
                            } else {
                                lean_dec(v_rchild_1546_);
                                lean_dec(v_val_1545_);
                                lean_dec(v_key_1544_);
                                lean_dec(v_lchild_1543_);
                                lean_del_object(v___x_1459_);
                                v___x_1612_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v___x_1612_, 0, v_lchild_1454_);
                                lean_ctor_set(v___x_1612_, 1, v_key_1455_);
                                lean_ctor_set(v___x_1612_, 2, v_val_1456_);
                                lean_ctor_set(v___x_1612_, 3, v___x_1541_);
                                lean_ctor_set_uint8(
                                    v___x_1612_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v_color_1432_,
                                );
                                return v___x_1612_;
                            }
                        } else {
                            if v_isShared_1460_ == 0 {
                                lean_ctor_set(v___x_1459_, 3, v___x_1541_);
                                v___x_1614_ = v___x_1459_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_lchild_1454_);
                                lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_key_1455_);
                                lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_val_1456_);
                                lean_ctor_set(v_reuseFailAlloc_1615_, 3, v___x_1541_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_1615_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v_color_1432_,
                                );
                                v___x_1614_ = v_reuseFailAlloc_1615_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_1460_ == 0 {
                    lean_ctor_set(v___x_1459_, 3, v_b_1473_);
                    lean_ctor_set(v___x_1459_, 2, v_vx_1472_);
                    lean_ctor_set(v___x_1459_, 1, v_kx_1471_);
                    lean_ctor_set(v___x_1459_, 0, v_a_1470_);
                    v___x_1481_ = v___x_1459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1470_);
                    lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_kx_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_vx_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_b_1473_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1484_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_color_1432_,
                    );
                    v___x_1481_ = v_reuseFailAlloc_1484_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1482_ = lean_alloc_ctor(1, 4, (1) as u32);
                lean_ctor_set(v___x_1482_, 0, v_c_1476_);
                lean_ctor_set(v___x_1482_, 1, v_kz_1477_);
                lean_ctor_set(v___x_1482_, 2, v_vz_1478_);
                lean_ctor_set(v___x_1482_, 3, v_d_1479_);
                lean_ctor_set_uint8(
                    v___x_1482_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                v___x_1483_ = lean_alloc_ctor(1, 4, (1) as u32);
                lean_ctor_set(v___x_1483_, 0, v___x_1481_);
                lean_ctor_set(v___x_1483_, 1, v_ky_1474_);
                lean_ctor_set(v___x_1483_, 2, v_vy_1475_);
                lean_ctor_set(v___x_1483_, 3, v___x_1482_);
                lean_ctor_set_uint8(
                    v___x_1483_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1464_,
                );
                return v___x_1483_;
            }
            8 => {
                if v_isShared_1497_ == 0 {
                    lean_ctor_set(v___x_1496_, 3, v_rchild_1457_);
                    lean_ctor_set(v___x_1496_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1496_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1496_, 0, v___x_1463_);
                    v___x_1499_ = v___x_1496_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1463_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_rchild_1457_);
                    v___x_1499_ = v_reuseFailAlloc_1500_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_ctor_set_uint8(
                    v___x_1499_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1499_;
            }
            10 => {
                if v_isShared_1508_ == 0 {
                    lean_ctor_set(v___x_1507_, 3, v_rchild_1457_);
                    lean_ctor_set(v___x_1507_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1507_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1507_, 0, v___x_1463_);
                    v___x_1510_ = v___x_1507_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1463_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_rchild_1457_);
                    v___x_1510_ = v_reuseFailAlloc_1511_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_ctor_set_uint8(
                    v___x_1510_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1510_;
            }
            12 => {
                if v_isShared_1524_ == 0 {
                    lean_ctor_set(v___x_1523_, 3, v_rchild_1457_);
                    lean_ctor_set(v___x_1523_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1523_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1523_, 0, v___x_1463_);
                    v___x_1526_ = v___x_1523_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1463_);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_rchild_1457_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1526_;
            }
            14 => {
                return v___x_1536_;
            }
            15 => {
                return v___x_1539_;
            }
            16 => {
                if v_isShared_1460_ == 0 {
                    lean_ctor_set(v___x_1459_, 3, v_b_1551_);
                    lean_ctor_set(v___x_1459_, 2, v_vx_1550_);
                    lean_ctor_set(v___x_1459_, 1, v_kx_1549_);
                    lean_ctor_set(v___x_1459_, 0, v_a_1548_);
                    v___x_1559_ = v___x_1459_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1548_);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_kx_1549_);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_vx_1550_);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_b_1551_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1562_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_color_1432_,
                    );
                    v___x_1559_ = v_reuseFailAlloc_1562_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1560_ = lean_alloc_ctor(1, 4, (1) as u32);
                lean_ctor_set(v___x_1560_, 0, v_c_1554_);
                lean_ctor_set(v___x_1560_, 1, v_kz_1555_);
                lean_ctor_set(v___x_1560_, 2, v_vz_1556_);
                lean_ctor_set(v___x_1560_, 3, v_d_1557_);
                lean_ctor_set_uint8(
                    v___x_1560_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                v___x_1561_ = lean_alloc_ctor(1, 4, (1) as u32);
                lean_ctor_set(v___x_1561_, 0, v___x_1559_);
                lean_ctor_set(v___x_1561_, 1, v_ky_1552_);
                lean_ctor_set(v___x_1561_, 2, v_vy_1553_);
                lean_ctor_set(v___x_1561_, 3, v___x_1560_);
                lean_ctor_set_uint8(
                    v___x_1561_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1542_,
                );
                return v___x_1561_;
            }
            18 => {
                if v_isShared_1575_ == 0 {
                    lean_ctor_set(v___x_1574_, 3, v___x_1541_);
                    lean_ctor_set(v___x_1574_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1574_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1574_, 0, v_lchild_1454_);
                    v___x_1577_ = v___x_1574_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_lchild_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 3, v___x_1541_);
                    v___x_1577_ = v_reuseFailAlloc_1578_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                lean_ctor_set_uint8(
                    v___x_1577_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1577_;
            }
            20 => {
                if v_isShared_1586_ == 0 {
                    lean_ctor_set(v___x_1585_, 3, v___x_1541_);
                    lean_ctor_set(v___x_1585_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1585_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1585_, 0, v_lchild_1454_);
                    v___x_1588_ = v___x_1585_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_lchild_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1541_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                lean_ctor_set_uint8(
                    v___x_1588_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1588_;
            }
            22 => {
                if v_isShared_1602_ == 0 {
                    lean_ctor_set(v___x_1601_, 3, v___x_1541_);
                    lean_ctor_set(v___x_1601_, 2, v_val_1456_);
                    lean_ctor_set(v___x_1601_, 1, v_key_1455_);
                    lean_ctor_set(v___x_1601_, 0, v_lchild_1454_);
                    v___x_1604_ = v___x_1601_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_lchild_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_key_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_val_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___x_1541_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_ctor_set_uint8(
                    v___x_1604_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1604_;
            }
            24 => {
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
    mut v_cmp_1617_: *mut LeanObject,
    mut v_t_1618_: *mut LeanObject,
    mut v_k_1619_: *mut LeanObject,
    mut v_v_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: u8 = 0;
    v___x_1621_ = l_Lean_RBNode_isRed___redArg(v_t_1618_);
    if v___x_1621_ == 0 {
        let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
        v___x_1622_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1617_, v_t_1618_, v_k_1619_, v_v_1620_);
        return v___x_1622_;
    } else {
        let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
        v___x_1623_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1617_, v_t_1618_, v_k_1619_, v_v_1620_);
        v___x_1624_ = l_Lean_RBNode_setBlack___redArg(v___x_1623_);
        return v___x_1624_;
    }
}
pub unsafe fn l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
    mut v_cmp_1625_: *mut LeanObject,
    mut v_x_1626_: *mut LeanObject,
    mut v_x_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1627_) == 0 {
                    lean_dec_ref(v_cmp_1625_);
                    return v_x_1626_;
                } else {
                    v_head_1628_ = lean_ctor_get(v_x_1627_, 0);
                    lean_inc(v_head_1628_);
                    v_tail_1629_ = lean_ctor_get(v_x_1627_, 1);
                    lean_inc(v_tail_1629_);
                    lean_dec_ref_known(v_x_1627_, 2);
                    v___x_1630_ = lean_box(0);
                    lean_inc_ref(v_cmp_1625_);
                    v___x_1631_ =
                        l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
                            v_cmp_1625_,
                            v_x_1626_,
                            v_head_1628_,
                            v___x_1630_,
                        );
                    v_x_1626_ = v___x_1631_;
                    v_x_1627_ = v_tail_1629_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_fromList___redArg(
    mut v_l_1633_: *mut LeanObject,
    mut v_cmp_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = lean_box(0);
    v___x_1636_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
        v_cmp_1634_,
        v___x_1635_,
        v_l_1633_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Lean_RBTree_fromList(
    mut v_00_u03b1_1637_: *mut LeanObject,
    mut v_l_1638_: *mut LeanObject,
    mut v_cmp_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_RBTree_fromList___redArg(v_l_1638_, v_cmp_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(
    mut v_00_u03b1_1641_: *mut LeanObject,
    mut v_cmp_1642_: *mut LeanObject,
    mut v_00_u03b2_1643_: *mut LeanObject,
    mut v_t_1644_: *mut LeanObject,
    mut v_k_1645_: *mut LeanObject,
    mut v_v_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
        v_cmp_1642_,
        v_t_1644_,
        v_k_1645_,
        v_v_1646_,
    );
    return v___x_1647_;
}
pub unsafe fn l_List_foldl___at___00Lean_RBTree_fromList_spec__1(
    mut v_00_u03b1_1648_: *mut LeanObject,
    mut v_cmp_1649_: *mut LeanObject,
    mut v_x_1650_: *mut LeanObject,
    mut v_x_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
        v_cmp_1649_,
        v_x_1650_,
        v_x_1651_,
    );
    return v___x_1652_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(
    mut v_00_u03b1_1653_: *mut LeanObject,
    mut v_cmp_1654_: *mut LeanObject,
    mut v_00_u03b2_1655_: *mut LeanObject,
    mut v_x_1656_: *mut LeanObject,
    mut v_x_1657_: *mut LeanObject,
    mut v_x_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1654_, v_x_1656_, v_x_1657_, v_x_1658_);
    return v___x_1659_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(
    mut v_cmp_1660_: *mut LeanObject,
    mut v_as_1661_: *mut LeanObject,
    mut v_i_1662_: usize,
    mut v_stop_1663_: usize,
    mut v_b_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: usize = 0;
    let mut v___x_1670_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1665_ = lean_usize_dec_eq(v_i_1662_, v_stop_1663_);
                if v___x_1665_ == 0 {
                    v___x_1666_ = lean_array_uget_borrowed(v_as_1661_, v_i_1662_);
                    v___x_1667_ = lean_box(0);
                    lean_inc(v___x_1666_);
                    lean_inc_ref(v_cmp_1660_);
                    v___x_1668_ =
                        l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
                            v_cmp_1660_,
                            v_b_1664_,
                            v___x_1666_,
                            v___x_1667_,
                        );
                    v___x_1669_ = 1usize;
                    v___x_1670_ = lean_usize_add(v_i_1662_, v___x_1669_);
                    v_i_1662_ = v___x_1670_;
                    v_b_1664_ = v___x_1668_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_cmp_1660_);
                    return v_b_1664_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(
    mut v_cmp_1672_: *mut LeanObject,
    mut v_as_1673_: *mut LeanObject,
    mut v_i_1674_: *mut LeanObject,
    mut v_stop_1675_: *mut LeanObject,
    mut v_b_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1677_: usize = 0;
    let mut v_stop_boxed_1678_: usize = 0;
    let mut v_res_1679_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1677_ = lean_unbox_usize(v_i_1674_);
    lean_dec(v_i_1674_);
    v_stop_boxed_1678_ = lean_unbox_usize(v_stop_1675_);
    lean_dec(v_stop_1675_);
    v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1672_, v_as_1673_, v_i_boxed_1677_, v_stop_boxed_1678_, v_b_1676_);
    lean_dec_ref(v_as_1673_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_RBTree_fromArray___redArg(
    mut v_l_1680_: *mut LeanObject,
    mut v_cmp_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1682_ = lean_box(0);
    v___x_1683_ = lean_unsigned_to_nat(0);
    v___x_1684_ = lean_array_get_size(v_l_1680_);
    v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
    if v___x_1685_ == 0 {
        lean_dec_ref(v_cmp_1681_);
        return v___x_1682_;
    } else {
        let mut v___x_1686_: u8 = 0;
        v___x_1686_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
        if v___x_1686_ == 0 {
            if v___x_1685_ == 0 {
                lean_dec_ref(v_cmp_1681_);
                return v___x_1682_;
            } else {
                let mut v___x_1687_: usize = 0;
                let mut v___x_1688_: usize = 0;
                let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
                v___x_1687_ = 0usize;
                v___x_1688_ = lean_usize_of_nat(v___x_1684_);
                v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1681_, v_l_1680_, v___x_1687_, v___x_1688_, v___x_1682_);
                return v___x_1689_;
            }
        } else {
            let mut v___x_1690_: usize = 0;
            let mut v___x_1691_: usize = 0;
            let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
            v___x_1690_ = 0usize;
            v___x_1691_ = lean_usize_of_nat(v___x_1684_);
            v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1681_, v_l_1680_, v___x_1690_, v___x_1691_, v___x_1682_);
            return v___x_1692_;
        }
    }
}
pub unsafe fn l_Lean_RBTree_fromArray___redArg___boxed(
    mut v_l_1693_: *mut LeanObject,
    mut v_cmp_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1695_: *mut LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_RBTree_fromArray___redArg(v_l_1693_, v_cmp_1694_);
    lean_dec_ref(v_l_1693_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_RBTree_fromArray(
    mut v_00_u03b1_1696_: *mut LeanObject,
    mut v_l_1697_: *mut LeanObject,
    mut v_cmp_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_RBTree_fromArray___redArg(v_l_1697_, v_cmp_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lean_RBTree_fromArray___boxed(
    mut v_00_u03b1_1700_: *mut LeanObject,
    mut v_l_1701_: *mut LeanObject,
    mut v_cmp_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_RBTree_fromArray(v_00_u03b1_1700_, v_l_1701_, v_cmp_1702_);
    lean_dec_ref(v_l_1701_);
    return v_res_1703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(
    mut v_00_u03b1_1704_: *mut LeanObject,
    mut v_cmp_1705_: *mut LeanObject,
    mut v_as_1706_: *mut LeanObject,
    mut v_i_1707_: usize,
    mut v_stop_1708_: usize,
    mut v_b_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1705_, v_as_1706_, v_i_1707_, v_stop_1708_, v_b_1709_);
    return v___x_1710_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(
    mut v_00_u03b1_1711_: *mut LeanObject,
    mut v_cmp_1712_: *mut LeanObject,
    mut v_as_1713_: *mut LeanObject,
    mut v_i_1714_: *mut LeanObject,
    mut v_stop_1715_: *mut LeanObject,
    mut v_b_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1717_: usize = 0;
    let mut v_stop_boxed_1718_: usize = 0;
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1717_ = lean_unbox_usize(v_i_1714_);
    lean_dec(v_i_1714_);
    v_stop_boxed_1718_ = lean_unbox_usize(v_stop_1715_);
    lean_dec(v_stop_1715_);
    v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(v_00_u03b1_1711_, v_cmp_1712_, v_as_1713_, v_i_boxed_1717_, v_stop_boxed_1718_, v_b_1716_);
    lean_dec_ref(v_as_1713_);
    return v_res_1719_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___lam__0(
    mut v_p_1720_: *mut LeanObject,
    mut v_a_1721_: *mut LeanObject,
    mut v_x_1722_: *mut LeanObject,
) -> u8 {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    v___x_1723_ = lean_apply_1(v_p_1720_, v_a_1721_);
    v___x_1724_ = (lean_unbox(v___x_1723_) as u8);
    return v___x_1724_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___lam__0___boxed(
    mut v_p_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
    mut v_x_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1728_: u8 = 0;
    let mut v_r_1729_: *mut LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lean_RBTree_all___redArg___lam__0(v_p_1725_, v_a_1726_, v_x_1727_);
    v_r_1729_ = lean_box((v_res_1728_) as usize);
    return v_r_1729_;
}
pub unsafe fn l_Lean_RBTree_all___redArg(
    mut v_t_1730_: *mut LeanObject,
    mut v_p_1731_: *mut LeanObject,
) -> u8 {
    let mut v___f_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    v___f_1732_ = lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1732_, 0, v_p_1731_);
    v___x_1733_ = l_Lean_RBNode_all___redArg(v___f_1732_, v_t_1730_);
    return v___x_1733_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___boxed(
    mut v_t_1734_: *mut LeanObject,
    mut v_p_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: u8 = 0;
    let mut v_r_1737_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_RBTree_all___redArg(v_t_1734_, v_p_1735_);
    v_r_1737_ = lean_box((v_res_1736_) as usize);
    return v_r_1737_;
}
pub unsafe fn l_Lean_RBTree_all(
    mut v_00_u03b1_1738_: *mut LeanObject,
    mut v_cmp_1739_: *mut LeanObject,
    mut v_t_1740_: *mut LeanObject,
    mut v_p_1741_: *mut LeanObject,
) -> u8 {
    let mut v___f_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    v___f_1742_ = lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1742_, 0, v_p_1741_);
    v___x_1743_ = l_Lean_RBNode_all___redArg(v___f_1742_, v_t_1740_);
    return v___x_1743_;
}
pub unsafe fn l_Lean_RBTree_all___boxed(
    mut v_00_u03b1_1744_: *mut LeanObject,
    mut v_cmp_1745_: *mut LeanObject,
    mut v_t_1746_: *mut LeanObject,
    mut v_p_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1748_: u8 = 0;
    let mut v_r_1749_: *mut LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lean_RBTree_all(v_00_u03b1_1744_, v_cmp_1745_, v_t_1746_, v_p_1747_);
    lean_dec_ref(v_cmp_1745_);
    v_r_1749_ = lean_box((v_res_1748_) as usize);
    return v_r_1749_;
}
pub unsafe fn l_Lean_RBTree_any___redArg(
    mut v_t_1750_: *mut LeanObject,
    mut v_p_1751_: *mut LeanObject,
) -> u8 {
    let mut v___f_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    v___f_1752_ = lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1752_, 0, v_p_1751_);
    v___x_1753_ = l_Lean_RBNode_any___redArg(v___f_1752_, v_t_1750_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_RBTree_any___redArg___boxed(
    mut v_t_1754_: *mut LeanObject,
    mut v_p_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1756_: u8 = 0;
    let mut v_r_1757_: *mut LeanObject = core::ptr::null_mut();
    v_res_1756_ = l_Lean_RBTree_any___redArg(v_t_1754_, v_p_1755_);
    v_r_1757_ = lean_box((v_res_1756_) as usize);
    return v_r_1757_;
}
pub unsafe fn l_Lean_RBTree_any(
    mut v_00_u03b1_1758_: *mut LeanObject,
    mut v_cmp_1759_: *mut LeanObject,
    mut v_t_1760_: *mut LeanObject,
    mut v_p_1761_: *mut LeanObject,
) -> u8 {
    let mut v___f_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    v___f_1762_ = lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1762_, 0, v_p_1761_);
    v___x_1763_ = l_Lean_RBNode_any___redArg(v___f_1762_, v_t_1760_);
    return v___x_1763_;
}
pub unsafe fn l_Lean_RBTree_any___boxed(
    mut v_00_u03b1_1764_: *mut LeanObject,
    mut v_cmp_1765_: *mut LeanObject,
    mut v_t_1766_: *mut LeanObject,
    mut v_p_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Lean_RBTree_any(v_00_u03b1_1764_, v_cmp_1765_, v_t_1766_, v_p_1767_);
    lean_dec_ref(v_cmp_1765_);
    v_r_1769_ = lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
    mut v_cmp_1770_: *mut LeanObject,
    mut v_x_1771_: *mut LeanObject,
    mut v_x_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lchild_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1771_) == 0 {
                    lean_dec(v_x_1772_);
                    lean_dec_ref(v_cmp_1770_);
                    v___x_1773_ = lean_box(0);
                    return v___x_1773_;
                } else {
                    v_lchild_1774_ = lean_ctor_get(v_x_1771_, 0);
                    lean_inc(v_lchild_1774_);
                    v_key_1775_ = lean_ctor_get(v_x_1771_, 1);
                    lean_inc_n(v_key_1775_, 2);
                    v_val_1776_ = lean_ctor_get(v_x_1771_, 2);
                    lean_inc(v_val_1776_);
                    v_rchild_1777_ = lean_ctor_get(v_x_1771_, 3);
                    lean_inc(v_rchild_1777_);
                    lean_dec_ref_known(v_x_1771_, 4);
                    lean_inc_ref(v_cmp_1770_);
                    lean_inc(v_x_1772_);
                    v___x_1778_ = lean_apply_2(v_cmp_1770_, v_x_1772_, v_key_1775_);
                    v___x_1779_ = (lean_unbox(v___x_1778_) as u8);
                    match v___x_1779_ {
                        0 => {
                            lean_dec(v_rchild_1777_);
                            lean_dec(v_val_1776_);
                            lean_dec(v_key_1775_);
                            v_x_1771_ = v_lchild_1774_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_rchild_1777_);
                            lean_dec(v_lchild_1774_);
                            lean_dec(v_x_1772_);
                            lean_dec_ref(v_cmp_1770_);
                            v___x_1781_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1781_, 0, v_key_1775_);
                            lean_ctor_set(v___x_1781_, 1, v_val_1776_);
                            v___x_1782_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1782_, 0, v___x_1781_);
                            return v___x_1782_;
                        }
                        _ => {
                            lean_dec(v_val_1776_);
                            lean_dec(v_key_1775_);
                            lean_dec(v_lchild_1774_);
                            v_x_1771_ = v_rchild_1777_;
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
pub unsafe fn l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
    mut v_t_u2082_1784_: *mut LeanObject,
    mut v_cmp_1785_: *mut LeanObject,
    mut v_x_1786_: *mut LeanObject,
) -> u8 {
    let mut v___x_1787_: u8 = 0;
    let mut v_lchild_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1786_) == 0 {
                    lean_dec_ref(v_cmp_1785_);
                    lean_dec(v_t_u2082_1784_);
                    v___x_1787_ = 1;
                    return v___x_1787_;
                } else {
                    v_lchild_1788_ = lean_ctor_get(v_x_1786_, 0);
                    lean_inc(v_lchild_1788_);
                    v_key_1789_ = lean_ctor_get(v_x_1786_, 1);
                    lean_inc(v_key_1789_);
                    v_rchild_1790_ = lean_ctor_get(v_x_1786_, 3);
                    lean_inc(v_rchild_1790_);
                    lean_dec_ref_known(v_x_1786_, 4);
                    lean_inc(v_t_u2082_1784_);
                    lean_inc_ref(v_cmp_1785_);
                    v___x_1791_ =
                        l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
                            v_cmp_1785_,
                            v_t_u2082_1784_,
                            v_key_1789_,
                        );
                    if lean_obj_tag(v___x_1791_) == 0 {
                        lean_dec(v_rchild_1790_);
                        lean_dec(v_lchild_1788_);
                        lean_dec_ref(v_cmp_1785_);
                        lean_dec(v_t_u2082_1784_);
                        v___x_1792_ = 0;
                        return v___x_1792_;
                    } else {
                        lean_dec_ref_known(v___x_1791_, 1);
                        lean_inc_ref(v_cmp_1785_);
                        lean_inc(v_t_u2082_1784_);
                        v___x_1793_ =
                            l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
                                v_t_u2082_1784_,
                                v_cmp_1785_,
                                v_lchild_1788_,
                            );
                        if v___x_1793_ == 0 {
                            lean_dec(v_rchild_1790_);
                            lean_dec_ref(v_cmp_1785_);
                            lean_dec(v_t_u2082_1784_);
                            return v___x_1793_;
                        } else {
                            v_x_1786_ = v_rchild_1790_;
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
pub unsafe fn l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(
    mut v_t_u2082_1795_: *mut LeanObject,
    mut v_cmp_1796_: *mut LeanObject,
    mut v_x_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: u8 = 0;
    let mut v_r_1799_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1795_,
        v_cmp_1796_,
        v_x_1797_,
    );
    v_r_1799_ = lean_box((v_res_1798_) as usize);
    return v_r_1799_;
}
pub unsafe fn l_Lean_RBTree_subset___redArg(
    mut v_cmp_1800_: *mut LeanObject,
    mut v_t_u2081_1801_: *mut LeanObject,
    mut v_t_u2082_1802_: *mut LeanObject,
) -> u8 {
    let mut v___x_1803_: u8 = 0;
    v___x_1803_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1802_,
        v_cmp_1800_,
        v_t_u2081_1801_,
    );
    return v___x_1803_;
}
pub unsafe fn l_Lean_RBTree_subset___redArg___boxed(
    mut v_cmp_1804_: *mut LeanObject,
    mut v_t_u2081_1805_: *mut LeanObject,
    mut v_t_u2082_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1807_: u8 = 0;
    let mut v_r_1808_: *mut LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lean_RBTree_subset___redArg(v_cmp_1804_, v_t_u2081_1805_, v_t_u2082_1806_);
    v_r_1808_ = lean_box((v_res_1807_) as usize);
    return v_r_1808_;
}
pub unsafe fn l_Lean_RBTree_subset(
    mut v_00_u03b1_1809_: *mut LeanObject,
    mut v_cmp_1810_: *mut LeanObject,
    mut v_t_u2081_1811_: *mut LeanObject,
    mut v_t_u2082_1812_: *mut LeanObject,
) -> u8 {
    let mut v___x_1813_: u8 = 0;
    v___x_1813_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1812_,
        v_cmp_1810_,
        v_t_u2081_1811_,
    );
    return v___x_1813_;
}
pub unsafe fn l_Lean_RBTree_subset___boxed(
    mut v_00_u03b1_1814_: *mut LeanObject,
    mut v_cmp_1815_: *mut LeanObject,
    mut v_t_u2081_1816_: *mut LeanObject,
    mut v_t_u2082_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1818_: u8 = 0;
    let mut v_r_1819_: *mut LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_RBTree_subset(
        v_00_u03b1_1814_,
        v_cmp_1815_,
        v_t_u2081_1816_,
        v_t_u2082_1817_,
    );
    v_r_1819_ = lean_box((v_res_1818_) as usize);
    return v_r_1819_;
}
pub unsafe fn l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(
    mut v_00_u03b1_1820_: *mut LeanObject,
    mut v_cmp_1821_: *mut LeanObject,
    mut v_00_u03b2_1822_: *mut LeanObject,
    mut v_x_1823_: *mut LeanObject,
    mut v_x_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
        v_cmp_1821_,
        v_x_1823_,
        v_x_1824_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(
    mut v_00_u03b1_1826_: *mut LeanObject,
    mut v_t_u2082_1827_: *mut LeanObject,
    mut v_cmp_1828_: *mut LeanObject,
    mut v_x_1829_: *mut LeanObject,
) -> u8 {
    let mut v___x_1830_: u8 = 0;
    v___x_1830_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1827_,
        v_cmp_1828_,
        v_x_1829_,
    );
    return v___x_1830_;
}
pub unsafe fn l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(
    mut v_00_u03b1_1831_: *mut LeanObject,
    mut v_t_u2082_1832_: *mut LeanObject,
    mut v_cmp_1833_: *mut LeanObject,
    mut v_x_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1835_: u8 = 0;
    let mut v_r_1836_: *mut LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(
        v_00_u03b1_1831_,
        v_t_u2082_1832_,
        v_cmp_1833_,
        v_x_1834_,
    );
    v_r_1836_ = lean_box((v_res_1835_) as usize);
    return v_r_1836_;
}
pub unsafe fn l_Lean_RBTree_seteq___redArg(
    mut v_cmp_1837_: *mut LeanObject,
    mut v_t_u2081_1838_: *mut LeanObject,
    mut v_t_u2082_1839_: *mut LeanObject,
) -> u8 {
    let mut v___x_1840_: u8 = 0;
    lean_inc(v_t_u2081_1838_);
    lean_inc_ref(v_cmp_1837_);
    lean_inc(v_t_u2082_1839_);
    v___x_1840_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1839_,
        v_cmp_1837_,
        v_t_u2081_1838_,
    );
    if v___x_1840_ == 0 {
        lean_dec(v_t_u2082_1839_);
        lean_dec(v_t_u2081_1838_);
        lean_dec_ref(v_cmp_1837_);
        return v___x_1840_;
    } else {
        let mut v___x_1841_: u8 = 0;
        v___x_1841_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
            v_t_u2081_1838_,
            v_cmp_1837_,
            v_t_u2082_1839_,
        );
        return v___x_1841_;
    }
}
pub unsafe fn l_Lean_RBTree_seteq___redArg___boxed(
    mut v_cmp_1842_: *mut LeanObject,
    mut v_t_u2081_1843_: *mut LeanObject,
    mut v_t_u2082_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1845_: u8 = 0;
    let mut v_r_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_RBTree_seteq___redArg(v_cmp_1842_, v_t_u2081_1843_, v_t_u2082_1844_);
    v_r_1846_ = lean_box((v_res_1845_) as usize);
    return v_r_1846_;
}
pub unsafe fn l_Lean_RBTree_seteq(
    mut v_00_u03b1_1847_: *mut LeanObject,
    mut v_cmp_1848_: *mut LeanObject,
    mut v_t_u2081_1849_: *mut LeanObject,
    mut v_t_u2082_1850_: *mut LeanObject,
) -> u8 {
    let mut v___x_1851_: u8 = 0;
    v___x_1851_ = l_Lean_RBTree_seteq___redArg(v_cmp_1848_, v_t_u2081_1849_, v_t_u2082_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_RBTree_seteq___boxed(
    mut v_00_u03b1_1852_: *mut LeanObject,
    mut v_cmp_1853_: *mut LeanObject,
    mut v_t_u2081_1854_: *mut LeanObject,
    mut v_t_u2082_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: u8 = 0;
    let mut v_r_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_RBTree_seteq(
        v_00_u03b1_1852_,
        v_cmp_1853_,
        v_t_u2081_1854_,
        v_t_u2082_1855_,
    );
    v_r_1857_ = lean_box((v_res_1856_) as usize);
    return v_r_1857_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
    mut v_cmp_1858_: *mut LeanObject,
    mut v_x_1859_: *mut LeanObject,
    mut v_x_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lchild_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1860_) == 0 {
                    lean_dec_ref(v_cmp_1858_);
                    return v_x_1859_;
                } else {
                    v_lchild_1861_ = lean_ctor_get(v_x_1860_, 0);
                    lean_inc(v_lchild_1861_);
                    v_key_1862_ = lean_ctor_get(v_x_1860_, 1);
                    lean_inc(v_key_1862_);
                    v_rchild_1863_ = lean_ctor_get(v_x_1860_, 3);
                    lean_inc(v_rchild_1863_);
                    lean_dec_ref_known(v_x_1860_, 4);
                    lean_inc_ref_n(v_cmp_1858_, 2);
                    v_val_1864_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
                        v_cmp_1858_,
                        v_x_1859_,
                        v_lchild_1861_,
                    );
                    v___x_1865_ = lean_box(0);
                    v___x_1866_ =
                        l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
                            v_cmp_1858_,
                            v_val_1864_,
                            v_key_1862_,
                            v___x_1865_,
                        );
                    v_x_1859_ = v___x_1866_;
                    v_x_1860_ = v_rchild_1863_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_union___redArg(
    mut v_cmp_1868_: *mut LeanObject,
    mut v_t_u2081_1869_: *mut LeanObject,
    mut v_t_u2082_1870_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_u2081_1869_) == 0 {
        lean_dec_ref(v_cmp_1868_);
        return v_t_u2082_1870_;
    } else {
        let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
        v___x_1871_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
            v_cmp_1868_,
            v_t_u2081_1869_,
            v_t_u2082_1870_,
        );
        return v___x_1871_;
    }
}
pub unsafe fn l_Lean_RBTree_union(
    mut v_00_u03b1_1872_: *mut LeanObject,
    mut v_cmp_1873_: *mut LeanObject,
    mut v_t_u2081_1874_: *mut LeanObject,
    mut v_t_u2082_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_RBTree_union___redArg(v_cmp_1873_, v_t_u2081_1874_, v_t_u2082_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(
    mut v_00_u03b1_1877_: *mut LeanObject,
    mut v_cmp_1878_: *mut LeanObject,
    mut v_x_1879_: *mut LeanObject,
    mut v_x_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
        v_cmp_1878_,
        v_x_1879_,
        v_x_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(
    mut v_cmp_1882_: *mut LeanObject,
    mut v_x_1883_: *mut LeanObject,
    mut v_x_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lchild_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1884_) == 0 {
                    lean_dec(v_x_1883_);
                    lean_dec_ref(v_cmp_1882_);
                    return v_x_1884_;
                } else {
                    v_lchild_1885_ = lean_ctor_get(v_x_1884_, 0);
                    v_key_1886_ = lean_ctor_get(v_x_1884_, 1);
                    v_val_1887_ = lean_ctor_get(v_x_1884_, 2);
                    v_rchild_1888_ = lean_ctor_get(v_x_1884_, 3);
                    v_isSharedCheck_1911_ = (!lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1890_ = v_x_1884_;
                        v_isShared_1891_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_rchild_1888_);
                        lean_inc(v_val_1887_);
                        lean_inc(v_key_1886_);
                        lean_inc(v_lchild_1885_);
                        lean_dec(v_x_1884_);
                        v___x_1890_ = lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_cmp_1882_);
                lean_inc(v_key_1886_);
                lean_inc(v_x_1883_);
                v___x_1892_ = lean_apply_2(v_cmp_1882_, v_x_1883_, v_key_1886_);
                v___x_1893_ = (lean_unbox(v___x_1892_) as u8);
                match v___x_1893_ {
                    0 => {
                        v___x_1894_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1885_);
                        if v___x_1894_ == 0 {
                            v___x_1895_ = 0;
                            v___x_1896_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1882_, v_x_1883_, v_lchild_1885_);
                            if v_isShared_1891_ == 0 {
                                lean_ctor_set(v___x_1890_, 0, v___x_1896_);
                                v___x_1898_ = v___x_1890_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
                                lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_key_1886_);
                                lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_val_1887_);
                                lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_rchild_1888_);
                                v___x_1898_ = v_reuseFailAlloc_1899_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1890_);
                            v___x_1900_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1882_, v_x_1883_, v_lchild_1885_);
                            v___x_1901_ = l_Lean_RBNode_balLeft___redArg(
                                v___x_1900_,
                                v_key_1886_,
                                v_val_1887_,
                                v_rchild_1888_,
                            );
                            return v___x_1901_;
                        }
                    }
                    1 => {
                        lean_del_object(v___x_1890_);
                        lean_dec(v_val_1887_);
                        lean_dec(v_key_1886_);
                        lean_dec(v_x_1883_);
                        lean_dec_ref(v_cmp_1882_);
                        v___x_1902_ =
                            l_Lean_RBNode_appendTrees___redArg(v_lchild_1885_, v_rchild_1888_);
                        return v___x_1902_;
                    }
                    _ => {
                        v___x_1903_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1888_);
                        if v___x_1903_ == 0 {
                            v___x_1904_ = 0;
                            v___x_1905_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1882_, v_x_1883_, v_rchild_1888_);
                            if v_isShared_1891_ == 0 {
                                lean_ctor_set(v___x_1890_, 3, v___x_1905_);
                                v___x_1907_ = v___x_1890_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 4, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_lchild_1885_);
                                lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_key_1886_);
                                lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_val_1887_);
                                lean_ctor_set(v_reuseFailAlloc_1908_, 3, v___x_1905_);
                                v___x_1907_ = v_reuseFailAlloc_1908_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1890_);
                            v___x_1909_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1882_, v_x_1883_, v_rchild_1888_);
                            v___x_1910_ = l_Lean_RBNode_balRight___redArg(
                                v_lchild_1885_,
                                v_key_1886_,
                                v_val_1887_,
                                v___x_1909_,
                            );
                            return v___x_1910_;
                        }
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1898_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_1895_,
                );
                return v___x_1898_;
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_1907_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_1904_,
                );
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(
    mut v_cmp_1912_: *mut LeanObject,
    mut v_x_1913_: *mut LeanObject,
    mut v_t_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v_t_1915_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1912_, v_x_1913_, v_t_1914_);
    v___x_1916_ = l_Lean_RBNode_setBlack___redArg(v_t_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
    mut v_cmp_1917_: *mut LeanObject,
    mut v_x_1918_: *mut LeanObject,
    mut v_x_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lchild_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rchild_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1919_) == 0 {
                    lean_dec_ref(v_cmp_1917_);
                    return v_x_1918_;
                } else {
                    v_lchild_1920_ = lean_ctor_get(v_x_1919_, 0);
                    lean_inc(v_lchild_1920_);
                    v_key_1921_ = lean_ctor_get(v_x_1919_, 1);
                    lean_inc(v_key_1921_);
                    v_rchild_1922_ = lean_ctor_get(v_x_1919_, 3);
                    lean_inc(v_rchild_1922_);
                    lean_dec_ref_known(v_x_1919_, 4);
                    lean_inc_ref_n(v_cmp_1917_, 2);
                    v_val_1923_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
                        v_cmp_1917_,
                        v_x_1918_,
                        v_lchild_1920_,
                    );
                    v___x_1924_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(
                        v_cmp_1917_,
                        v_key_1921_,
                        v_val_1923_,
                    );
                    v_x_1918_ = v___x_1924_;
                    v_x_1919_ = v_rchild_1922_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBTree_diff___redArg(
    mut v_cmp_1926_: *mut LeanObject,
    mut v_t_u2081_1927_: *mut LeanObject,
    mut v_t_u2082_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1926_,
        v_t_u2081_1927_,
        v_t_u2082_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Lean_RBTree_diff(
    mut v_00_u03b1_1930_: *mut LeanObject,
    mut v_cmp_1931_: *mut LeanObject,
    mut v_t_u2081_1932_: *mut LeanObject,
    mut v_t_u2082_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1931_,
        v_t_u2081_1932_,
        v_t_u2082_1933_,
    );
    return v___x_1934_;
}
pub unsafe fn l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(
    mut v_00_u03b1_1935_: *mut LeanObject,
    mut v_cmp_1936_: *mut LeanObject,
    mut v_00_u03b2_1937_: *mut LeanObject,
    mut v_x_1938_: *mut LeanObject,
    mut v_t_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(
        v_cmp_1936_,
        v_x_1938_,
        v_t_1939_,
    );
    return v___x_1940_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(
    mut v_00_u03b1_1941_: *mut LeanObject,
    mut v_cmp_1942_: *mut LeanObject,
    mut v_x_1943_: *mut LeanObject,
    mut v_x_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1942_,
        v_x_1943_,
        v_x_1944_,
    );
    return v___x_1945_;
}
pub unsafe fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(
    mut v_00_u03b1_1946_: *mut LeanObject,
    mut v_cmp_1947_: *mut LeanObject,
    mut v_00_u03b2_1948_: *mut LeanObject,
    mut v_x_1949_: *mut LeanObject,
    mut v_x_1950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    v___x_1951_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1947_, v_x_1949_, v_x_1950_);
    return v___x_1951_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg___lam__0(
    mut v_f_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_x_1954_: *mut LeanObject,
) -> u8 {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    v___x_1955_ = lean_apply_1(v_f_1952_, v_a_1953_);
    v___x_1956_ = (lean_unbox(v___x_1955_) as u8);
    return v___x_1956_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg___lam__0___boxed(
    mut v_f_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_x_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1960_: u8 = 0;
    let mut v_r_1961_: *mut LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_1957_, v_a_1958_, v_x_1959_);
    v_r_1961_ = lean_box((v_res_1960_) as usize);
    return v_r_1961_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg(
    mut v_cmp_1962_: *mut LeanObject,
    mut v_f_1963_: *mut LeanObject,
    mut v_m_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___f_1965_ = lean_alloc_closure(
        l_Lean_RBTree_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1965_, 0, v_f_1963_);
    v___x_1966_ = l_Lean_RBMap_filter___redArg(v_cmp_1962_, v___f_1965_, v_m_1964_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_RBTree_filter(
    mut v_00_u03b1_1967_: *mut LeanObject,
    mut v_cmp_1968_: *mut LeanObject,
    mut v_f_1969_: *mut LeanObject,
    mut v_m_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Lean_RBTree_filter___redArg(v_cmp_1968_, v_f_1969_, v_m_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Lean_rbtreeOf___redArg(
    mut v_l_1972_: *mut LeanObject,
    mut v_cmp_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    v___x_1974_ = l_Lean_RBTree_fromList___redArg(v_l_1972_, v_cmp_1973_);
    return v___x_1974_;
}
pub unsafe fn l_Lean_rbtreeOf(
    mut v_00_u03b1_1975_: *mut LeanObject,
    mut v_l_1976_: *mut LeanObject,
    mut v_cmp_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v___x_1978_ = l_Lean_RBTree_fromList___redArg(v_l_1976_, v_cmp_1977_);
    return v___x_1978_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_RBTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_RBMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_RBTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_RBTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_RBMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RBTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_RBTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_RBTree(builtin);
}
