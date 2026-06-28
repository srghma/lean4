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
pub static l_Lean_RBTree_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_RBTree_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBTree_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBTree_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_RBTree_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_RBTree_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBTree_toArray___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_RBTree_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_RBTree_instRepr___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_RBTree_instRepr___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instInhabitedRBTree(
    mut v_00_u03b1_990_: *mut crate::leanh::LeanObject,
    mut v_p_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_box(0);
    return v___x_992_;
}
pub unsafe fn l_Lean_instInhabitedRBTree___boxed(
    mut v_00_u03b1_993_: *mut crate::leanh::LeanObject,
    mut v_p_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l_Lean_instInhabitedRBTree(v_00_u03b1_993_, v_p_994_);
    crate::leanh::lean_dec_ref(v_p_994_);
    return v_res_995_;
}
pub unsafe fn l_Lean_mkRBTree(
    mut v_00_u03b1_996_: *mut crate::leanh::LeanObject,
    mut v_cmp_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_box(0);
    return v___x_998_;
}
pub unsafe fn l_Lean_mkRBTree___boxed(
    mut v_00_u03b1_999_: *mut crate::leanh::LeanObject,
    mut v_cmp_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_mkRBTree(v_00_u03b1_999_, v_cmp_1000_);
    crate::leanh::lean_dec_ref(v_cmp_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBTree(
    mut v_00_u03b1_1002_: *mut crate::leanh::LeanObject,
    mut v_cmp_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = crate::leanh::lean_box(0);
    return v___x_1004_;
}
pub unsafe fn l_Lean_instEmptyCollectionRBTree___boxed(
    mut v_00_u03b1_1005_: *mut crate::leanh::LeanObject,
    mut v_cmp_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Lean_instEmptyCollectionRBTree(v_00_u03b1_1005_, v_cmp_1006_);
    crate::leanh::lean_dec_ref(v_cmp_1006_);
    return v_res_1007_;
}
pub unsafe fn l_Lean_RBTree_empty(
    mut v_00_u03b1_1008_: *mut crate::leanh::LeanObject,
    mut v_cmp_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_box(0);
    return v___x_1010_;
}
pub unsafe fn l_Lean_RBTree_empty___boxed(
    mut v_00_u03b1_1011_: *mut crate::leanh::LeanObject,
    mut v_cmp_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_RBTree_empty(v_00_u03b1_1011_, v_cmp_1012_);
    crate::leanh::lean_dec_ref(v_cmp_1012_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_RBTree_depth___redArg(
    mut v_f_1014_: *mut crate::leanh::LeanObject,
    mut v_t_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Lean_RBNode_depth___redArg(v_f_1014_, v_t_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Lean_RBTree_depth___redArg___boxed(
    mut v_f_1017_: *mut crate::leanh::LeanObject,
    mut v_t_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_RBTree_depth___redArg(v_f_1017_, v_t_1018_);
    crate::leanh::lean_dec(v_t_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_RBTree_depth(
    mut v_00_u03b1_1020_: *mut crate::leanh::LeanObject,
    mut v_cmp_1021_: *mut crate::leanh::LeanObject,
    mut v_f_1022_: *mut crate::leanh::LeanObject,
    mut v_t_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1024_ = l_Lean_RBNode_depth___redArg(v_f_1022_, v_t_1023_);
    return v___x_1024_;
}
pub unsafe fn l_Lean_RBTree_depth___boxed(
    mut v_00_u03b1_1025_: *mut crate::leanh::LeanObject,
    mut v_cmp_1026_: *mut crate::leanh::LeanObject,
    mut v_f_1027_: *mut crate::leanh::LeanObject,
    mut v_t_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_RBTree_depth(v_00_u03b1_1025_, v_cmp_1026_, v_f_1027_, v_t_1028_);
    crate::leanh::lean_dec(v_t_1028_);
    crate::leanh::lean_dec_ref(v_cmp_1026_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_RBTree_fold___redArg___lam__0(
    mut v_f_1030_: *mut crate::leanh::LeanObject,
    mut v_r_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = crate::leanh::lean_apply_2(v_f_1030_, v_r_1031_, v_a_1032_);
    return v___x_1034_;
}
pub unsafe fn l_Lean_RBTree_fold___redArg(
    mut v_f_1035_: *mut crate::leanh::LeanObject,
    mut v_init_1036_: *mut crate::leanh::LeanObject,
    mut v_t_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1038_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1038_, 0, v_f_1035_);
    v___x_1039_ = l_Lean_RBNode_fold___redArg(v___f_1038_, v_init_1036_, v_t_1037_);
    return v___x_1039_;
}
pub unsafe fn l_Lean_RBTree_fold(
    mut v_00_u03b1_1040_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1041_: *mut crate::leanh::LeanObject,
    mut v_cmp_1042_: *mut crate::leanh::LeanObject,
    mut v_f_1043_: *mut crate::leanh::LeanObject,
    mut v_init_1044_: *mut crate::leanh::LeanObject,
    mut v_t_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1046_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1046_, 0, v_f_1043_);
    v___x_1047_ = l_Lean_RBNode_fold___redArg(v___f_1046_, v_init_1044_, v_t_1045_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_RBTree_fold___boxed(
    mut v_00_u03b1_1048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1049_: *mut crate::leanh::LeanObject,
    mut v_cmp_1050_: *mut crate::leanh::LeanObject,
    mut v_f_1051_: *mut crate::leanh::LeanObject,
    mut v_init_1052_: *mut crate::leanh::LeanObject,
    mut v_t_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_RBTree_fold(
        v_00_u03b1_1048_,
        v_00_u03b2_1049_,
        v_cmp_1050_,
        v_f_1051_,
        v_init_1052_,
        v_t_1053_,
    );
    crate::leanh::lean_dec_ref(v_cmp_1050_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_RBTree_revFold___redArg(
    mut v_f_1055_: *mut crate::leanh::LeanObject,
    mut v_init_1056_: *mut crate::leanh::LeanObject,
    mut v_t_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1058_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1058_, 0, v_f_1055_);
    v___x_1059_ = l_Lean_RBNode_revFold___redArg(v___f_1058_, v_init_1056_, v_t_1057_);
    return v___x_1059_;
}
pub unsafe fn l_Lean_RBTree_revFold(
    mut v_00_u03b1_1060_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1061_: *mut crate::leanh::LeanObject,
    mut v_cmp_1062_: *mut crate::leanh::LeanObject,
    mut v_f_1063_: *mut crate::leanh::LeanObject,
    mut v_init_1064_: *mut crate::leanh::LeanObject,
    mut v_t_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1066_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1066_, 0, v_f_1063_);
    v___x_1067_ = l_Lean_RBNode_revFold___redArg(v___f_1066_, v_init_1064_, v_t_1065_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_RBTree_revFold___boxed(
    mut v_00_u03b1_1068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1069_: *mut crate::leanh::LeanObject,
    mut v_cmp_1070_: *mut crate::leanh::LeanObject,
    mut v_f_1071_: *mut crate::leanh::LeanObject,
    mut v_init_1072_: *mut crate::leanh::LeanObject,
    mut v_t_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_RBTree_revFold(
        v_00_u03b1_1068_,
        v_00_u03b2_1069_,
        v_cmp_1070_,
        v_f_1071_,
        v_init_1072_,
        v_t_1073_,
    );
    crate::leanh::lean_dec_ref(v_cmp_1070_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_RBTree_foldM___redArg(
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_f_1076_: *mut crate::leanh::LeanObject,
    mut v_init_1077_: *mut crate::leanh::LeanObject,
    mut v_t_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1079_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1079_, 0, v_f_1076_);
    v___x_1080_ = l_Lean_RBNode_foldM___redArg(v_inst_1075_, v___f_1079_, v_init_1077_, v_t_1078_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_RBTree_foldM(
    mut v_00_u03b1_1081_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1082_: *mut crate::leanh::LeanObject,
    mut v_cmp_1083_: *mut crate::leanh::LeanObject,
    mut v_m_1084_: *mut crate::leanh::LeanObject,
    mut v_inst_1085_: *mut crate::leanh::LeanObject,
    mut v_f_1086_: *mut crate::leanh::LeanObject,
    mut v_init_1087_: *mut crate::leanh::LeanObject,
    mut v_t_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1089_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1089_, 0, v_f_1086_);
    v___x_1090_ = l_Lean_RBNode_foldM___redArg(v_inst_1085_, v___f_1089_, v_init_1087_, v_t_1088_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_RBTree_foldM___boxed(
    mut v_00_u03b1_1091_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1092_: *mut crate::leanh::LeanObject,
    mut v_cmp_1093_: *mut crate::leanh::LeanObject,
    mut v_m_1094_: *mut crate::leanh::LeanObject,
    mut v_inst_1095_: *mut crate::leanh::LeanObject,
    mut v_f_1096_: *mut crate::leanh::LeanObject,
    mut v_init_1097_: *mut crate::leanh::LeanObject,
    mut v_t_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_1093_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_RBTree_forM___redArg___lam__0(
    mut v_f_1100_: *mut crate::leanh::LeanObject,
    mut v_r_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = crate::leanh::lean_apply_1(v_f_1100_, v_a_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_RBTree_forM___redArg(
    mut v_inst_1105_: *mut crate::leanh::LeanObject,
    mut v_f_1106_: *mut crate::leanh::LeanObject,
    mut v_t_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1108_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1108_, 0, v_f_1106_);
    v___x_1109_ = crate::leanh::lean_box(0);
    v___x_1110_ = l_Lean_RBNode_foldM___redArg(v_inst_1105_, v___f_1108_, v___x_1109_, v_t_1107_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_RBTree_forM(
    mut v_00_u03b1_1111_: *mut crate::leanh::LeanObject,
    mut v_cmp_1112_: *mut crate::leanh::LeanObject,
    mut v_m_1113_: *mut crate::leanh::LeanObject,
    mut v_inst_1114_: *mut crate::leanh::LeanObject,
    mut v_f_1115_: *mut crate::leanh::LeanObject,
    mut v_t_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1117_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1117_, 0, v_f_1115_);
    v___x_1118_ = crate::leanh::lean_box(0);
    v___x_1119_ = l_Lean_RBNode_foldM___redArg(v_inst_1114_, v___f_1117_, v___x_1118_, v_t_1116_);
    return v___x_1119_;
}
pub unsafe fn l_Lean_RBTree_forM___boxed(
    mut v_00_u03b1_1120_: *mut crate::leanh::LeanObject,
    mut v_cmp_1121_: *mut crate::leanh::LeanObject,
    mut v_m_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_f_1124_: *mut crate::leanh::LeanObject,
    mut v_t_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lean_RBTree_forM(
        v_00_u03b1_1120_,
        v_cmp_1121_,
        v_m_1122_,
        v_inst_1123_,
        v_f_1124_,
        v_t_1125_,
    );
    crate::leanh::lean_dec_ref(v_cmp_1121_);
    return v_res_1126_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg___lam__0(
    mut v_f_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_x_1129_: *mut crate::leanh::LeanObject,
    mut v_acc_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = crate::leanh::lean_apply_2(v_f_1127_, v_a_1128_, v_acc_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg___lam__1(
    mut v_toPure_1132_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1134_ = crate::leanh::lean_ctor_get(v_____do__lift_1133_, 0);
    crate::leanh::lean_inc(v_a_1134_);
    crate::leanh::lean_dec_ref(v_____do__lift_1133_);
    v___x_1135_ = crate::leanh::lean_apply_2(v_toPure_1132_, crate::leanh::lean_box(0), v_a_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Lean_RBTree_forIn___redArg(
    mut v_inst_1136_: *mut crate::leanh::LeanObject,
    mut v_t_1137_: *mut crate::leanh::LeanObject,
    mut v_init_1138_: *mut crate::leanh::LeanObject,
    mut v_f_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1140_ = crate::leanh::lean_ctor_get(v_inst_1136_, 0);
    v_toBind_1141_ = crate::leanh::lean_ctor_get(v_inst_1136_, 1);
    crate::leanh::lean_inc(v_toBind_1141_);
    v_toPure_1142_ = crate::leanh::lean_ctor_get(v_toApplicative_1140_, 1);
    crate::leanh::lean_inc(v_toPure_1142_);
    v___f_1143_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1143_, 0, v_f_1139_);
    v___x_1144_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1136_,
        v___f_1143_,
        v_t_1137_,
        v_init_1138_,
    );
    v___f_1145_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1145_, 0, v_toPure_1142_);
    v___x_1146_ = crate::leanh::lean_apply_4(
        v_toBind_1141_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1144_,
        v___f_1145_,
    );
    return v___x_1146_;
}
pub unsafe fn l_Lean_RBTree_forIn(
    mut v_00_u03b1_1147_: *mut crate::leanh::LeanObject,
    mut v_cmp_1148_: *mut crate::leanh::LeanObject,
    mut v_m_1149_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1150_: *mut crate::leanh::LeanObject,
    mut v_inst_1151_: *mut crate::leanh::LeanObject,
    mut v_t_1152_: *mut crate::leanh::LeanObject,
    mut v_init_1153_: *mut crate::leanh::LeanObject,
    mut v_f_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1155_ = crate::leanh::lean_ctor_get(v_inst_1151_, 0);
    v_toBind_1156_ = crate::leanh::lean_ctor_get(v_inst_1151_, 1);
    crate::leanh::lean_inc(v_toBind_1156_);
    v_toPure_1157_ = crate::leanh::lean_ctor_get(v_toApplicative_1155_, 1);
    crate::leanh::lean_inc(v_toPure_1157_);
    v___f_1158_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1158_, 0, v_f_1154_);
    v___x_1159_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1151_,
        v___f_1158_,
        v_t_1152_,
        v_init_1153_,
    );
    v___f_1160_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1160_, 0, v_toPure_1157_);
    v___x_1161_ = crate::leanh::lean_apply_4(
        v_toBind_1156_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1159_,
        v___f_1160_,
    );
    return v___x_1161_;
}
pub unsafe fn l_Lean_RBTree_forIn___boxed(
    mut v_00_u03b1_1162_: *mut crate::leanh::LeanObject,
    mut v_cmp_1163_: *mut crate::leanh::LeanObject,
    mut v_m_1164_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1165_: *mut crate::leanh::LeanObject,
    mut v_inst_1166_: *mut crate::leanh::LeanObject,
    mut v_t_1167_: *mut crate::leanh::LeanObject,
    mut v_init_1168_: *mut crate::leanh::LeanObject,
    mut v_f_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_1163_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg___lam__0(
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
    mut v_x_1173_: *mut crate::leanh::LeanObject,
    mut v_acc_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_apply_2(v___y_1171_, v_a_1172_, v_acc_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg___lam__2(
    mut v_inst_1176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1181_ = crate::leanh::lean_ctor_get(v_inst_1176_, 0);
    v_toBind_1182_ = crate::leanh::lean_ctor_get(v_inst_1176_, 1);
    crate::leanh::lean_inc(v_toBind_1182_);
    v_toPure_1183_ = crate::leanh::lean_ctor_get(v_toApplicative_1181_, 1);
    crate::leanh::lean_inc(v_toPure_1183_);
    v___f_1184_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1184_, 0, v___y_1180_);
    v___x_1185_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1176_,
        v___f_1184_,
        v___y_1178_,
        v___y_1179_,
    );
    v___f_1186_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1186_, 0, v_toPure_1183_);
    v___x_1187_ = crate::leanh::lean_apply_4(
        v_toBind_1182_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1185_,
        v___f_1186_,
    );
    return v___x_1187_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___redArg(
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1189_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1189_, 0, v_inst_1188_);
    return v___f_1189_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad(
    mut v_00_u03b1_1190_: *mut crate::leanh::LeanObject,
    mut v_cmp_1191_: *mut crate::leanh::LeanObject,
    mut v_m_1192_: *mut crate::leanh::LeanObject,
    mut v_inst_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1194_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1194_, 0, v_inst_1193_);
    return v___f_1194_;
}
pub unsafe fn l_Lean_RBTree_instForInOfMonad___boxed(
    mut v_00_u03b1_1195_: *mut crate::leanh::LeanObject,
    mut v_cmp_1196_: *mut crate::leanh::LeanObject,
    mut v_m_1197_: *mut crate::leanh::LeanObject,
    mut v_inst_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1199_ =
        l_Lean_RBTree_instForInOfMonad(v_00_u03b1_1195_, v_cmp_1196_, v_m_1197_, v_inst_1198_);
    crate::leanh::lean_dec_ref(v_cmp_1196_);
    return v_res_1199_;
}
pub unsafe fn l_Lean_RBTree_isEmpty___redArg(mut v_t_1200_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_1200_) == 0 {
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
    mut v_t_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1204_: u8 = 0;
    let mut v_r_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l_Lean_RBTree_isEmpty___redArg(v_t_1203_);
    crate::leanh::lean_dec(v_t_1203_);
    v_r_1205_ = crate::leanh::lean_box((v_res_1204_) as usize);
    return v_r_1205_;
}
pub unsafe fn l_Lean_RBTree_isEmpty(
    mut v_00_u03b1_1206_: *mut crate::leanh::LeanObject,
    mut v_cmp_1207_: *mut crate::leanh::LeanObject,
    mut v_t_1208_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_1208_) == 0 {
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
    mut v_00_u03b1_1211_: *mut crate::leanh::LeanObject,
    mut v_cmp_1212_: *mut crate::leanh::LeanObject,
    mut v_t_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1214_: u8 = 0;
    let mut v_r_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Lean_RBTree_isEmpty(v_00_u03b1_1211_, v_cmp_1212_, v_t_1213_);
    crate::leanh::lean_dec(v_t_1213_);
    crate::leanh::lean_dec_ref(v_cmp_1212_);
    v_r_1215_ = crate::leanh::lean_box((v_res_1214_) as usize);
    return v_r_1215_;
}
pub unsafe fn l_Lean_RBTree_toList___redArg___lam__0(
    mut v_r_1216_: *mut crate::leanh::LeanObject,
    mut v_a_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1219_, 0, v_a_1217_);
    crate::leanh::lean_ctor_set(v___x_1219_, 1, v_r_1216_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_RBTree_toList___redArg(
    mut v_t_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1222_ = l_Lean_RBTree_toList___redArg___closed__0;
    v___x_1223_ = crate::leanh::lean_box(0);
    v___x_1224_ = l_Lean_RBNode_revFold___redArg(v___f_1222_, v___x_1223_, v_t_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_RBTree_toList(
    mut v_00_u03b1_1225_: *mut crate::leanh::LeanObject,
    mut v_cmp_1226_: *mut crate::leanh::LeanObject,
    mut v_t_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_Lean_RBTree_toList___redArg(v_t_1227_);
    return v___x_1228_;
}
pub unsafe fn l_Lean_RBTree_toList___boxed(
    mut v_00_u03b1_1229_: *mut crate::leanh::LeanObject,
    mut v_cmp_1230_: *mut crate::leanh::LeanObject,
    mut v_t_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_RBTree_toList(v_00_u03b1_1229_, v_cmp_1230_, v_t_1231_);
    crate::leanh::lean_dec_ref(v_cmp_1230_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_RBTree_toArray___redArg___lam__0(
    mut v_r_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_x_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = lean_array_push(v_r_1233_, v_a_1234_);
    return v___x_1236_;
}
pub unsafe fn l_Lean_RBTree_toArray___redArg(
    mut v_t_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1241_ = l_Lean_RBTree_toArray___redArg___closed__0;
    v___x_1242_ = l_Lean_RBTree_toArray___redArg___closed__1;
    v___x_1243_ = l_Lean_RBNode_fold___redArg(v___f_1241_, v___x_1242_, v_t_1240_);
    return v___x_1243_;
}
pub unsafe fn l_Lean_RBTree_toArray(
    mut v_00_u03b1_1244_: *mut crate::leanh::LeanObject,
    mut v_cmp_1245_: *mut crate::leanh::LeanObject,
    mut v_t_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_RBTree_toArray___redArg(v_t_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Lean_RBTree_toArray___boxed(
    mut v_00_u03b1_1248_: *mut crate::leanh::LeanObject,
    mut v_cmp_1249_: *mut crate::leanh::LeanObject,
    mut v_t_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_RBTree_toArray(v_00_u03b1_1248_, v_cmp_1249_, v_t_1250_);
    crate::leanh::lean_dec_ref(v_cmp_1249_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_RBTree_min___redArg(
    mut v_t_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v_fst_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = l_Lean_RBNode_min___redArg(v_t_1252_);
                if crate::leanh::lean_obj_tag(v___x_1253_) == 0 {
                    v___x_1254_ = crate::leanh::lean_box(0);
                    return v___x_1254_;
                } else {
                    v_val_1255_ = crate::leanh::lean_ctor_get(v___x_1253_, 0);
                    v_isSharedCheck_1263_ = (!crate::leanh::lean_is_exclusive(v___x_1253_)) as u8;
                    if v_isSharedCheck_1263_ == 0 {
                        v___x_1257_ = v___x_1253_;
                        v_isShared_1258_ = v_isSharedCheck_1263_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1255_);
                        crate::leanh::lean_dec(v___x_1253_);
                        v___x_1257_ = crate::leanh::lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1259_ = crate::leanh::lean_ctor_get(v_val_1255_, 0);
                crate::leanh::lean_inc(v_fst_1259_);
                crate::leanh::lean_dec(v_val_1255_);
                if v_isShared_1258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1257_, 0, v_fst_1259_);
                    v___x_1261_ = v___x_1257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_fst_1259_);
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
    mut v_t_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_RBTree_min___redArg(v_t_1264_);
    crate::leanh::lean_dec(v_t_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_RBTree_min(
    mut v_00_u03b1_1266_: *mut crate::leanh::LeanObject,
    mut v_cmp_1267_: *mut crate::leanh::LeanObject,
    mut v_t_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v_fst_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = l_Lean_RBNode_min___redArg(v_t_1268_);
                if crate::leanh::lean_obj_tag(v___x_1269_) == 0 {
                    v___x_1270_ = crate::leanh::lean_box(0);
                    return v___x_1270_;
                } else {
                    v_val_1271_ = crate::leanh::lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1279_ = (!crate::leanh::lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1273_ = v___x_1269_;
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1271_);
                        crate::leanh::lean_dec(v___x_1269_);
                        v___x_1273_ = crate::leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1275_ = crate::leanh::lean_ctor_get(v_val_1271_, 0);
                crate::leanh::lean_inc(v_fst_1275_);
                crate::leanh::lean_dec(v_val_1271_);
                if v_isShared_1274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1273_, 0, v_fst_1275_);
                    v___x_1277_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_fst_1275_);
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
    mut v_00_u03b1_1280_: *mut crate::leanh::LeanObject,
    mut v_cmp_1281_: *mut crate::leanh::LeanObject,
    mut v_t_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Lean_RBTree_min(v_00_u03b1_1280_, v_cmp_1281_, v_t_1282_);
    crate::leanh::lean_dec(v_t_1282_);
    crate::leanh::lean_dec_ref(v_cmp_1281_);
    return v_res_1283_;
}
pub unsafe fn l_Lean_RBTree_max___redArg(
    mut v_t_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v_fst_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = l_Lean_RBNode_max___redArg(v_t_1284_);
                if crate::leanh::lean_obj_tag(v___x_1285_) == 0 {
                    v___x_1286_ = crate::leanh::lean_box(0);
                    return v___x_1286_;
                } else {
                    v_val_1287_ = crate::leanh::lean_ctor_get(v___x_1285_, 0);
                    v_isSharedCheck_1295_ = (!crate::leanh::lean_is_exclusive(v___x_1285_)) as u8;
                    if v_isSharedCheck_1295_ == 0 {
                        v___x_1289_ = v___x_1285_;
                        v_isShared_1290_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1287_);
                        crate::leanh::lean_dec(v___x_1285_);
                        v___x_1289_ = crate::leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1291_ = crate::leanh::lean_ctor_get(v_val_1287_, 0);
                crate::leanh::lean_inc(v_fst_1291_);
                crate::leanh::lean_dec(v_val_1287_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v_fst_1291_);
                    v___x_1293_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fst_1291_);
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
    mut v_t_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lean_RBTree_max___redArg(v_t_1296_);
    crate::leanh::lean_dec(v_t_1296_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_RBTree_max(
    mut v_00_u03b1_1298_: *mut crate::leanh::LeanObject,
    mut v_cmp_1299_: *mut crate::leanh::LeanObject,
    mut v_t_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1306_: u8 = 0;
    let mut v_fst_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1301_ = l_Lean_RBNode_max___redArg(v_t_1300_);
                if crate::leanh::lean_obj_tag(v___x_1301_) == 0 {
                    v___x_1302_ = crate::leanh::lean_box(0);
                    return v___x_1302_;
                } else {
                    v_val_1303_ = crate::leanh::lean_ctor_get(v___x_1301_, 0);
                    v_isSharedCheck_1311_ = (!crate::leanh::lean_is_exclusive(v___x_1301_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1305_ = v___x_1301_;
                        v_isShared_1306_ = v_isSharedCheck_1311_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1303_);
                        crate::leanh::lean_dec(v___x_1301_);
                        v___x_1305_ = crate::leanh::lean_box(0);
                        v_isShared_1306_ = v_isSharedCheck_1311_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1307_ = crate::leanh::lean_ctor_get(v_val_1303_, 0);
                crate::leanh::lean_inc(v_fst_1307_);
                crate::leanh::lean_dec(v_val_1303_);
                if v_isShared_1306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1305_, 0, v_fst_1307_);
                    v___x_1309_ = v___x_1305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_fst_1307_);
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
    mut v_00_u03b1_1312_: *mut crate::leanh::LeanObject,
    mut v_cmp_1313_: *mut crate::leanh::LeanObject,
    mut v_t_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_RBTree_max(v_00_u03b1_1312_, v_cmp_1313_, v_t_1314_);
    crate::leanh::lean_dec(v_t_1314_);
    crate::leanh::lean_dec_ref(v_cmp_1313_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg___lam__0(
    mut v_inst_1319_: *mut crate::leanh::LeanObject,
    mut v_t_1320_: *mut crate::leanh::LeanObject,
    mut v_prec_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_RBTree_instRepr___redArg___lam__0___closed__1;
    v___x_1323_ = l_Lean_RBTree_toList___redArg(v_t_1320_);
    v___x_1324_ = l_List_repr___redArg(v_inst_1319_, v___x_1323_);
    v___x_1325_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1322_);
    crate::leanh::lean_ctor_set(v___x_1325_, 1, v___x_1324_);
    v___x_1326_ = l_Repr_addAppParen(v___x_1325_, v_prec_1321_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg___lam__0___boxed(
    mut v_inst_1327_: *mut crate::leanh::LeanObject,
    mut v_t_1328_: *mut crate::leanh::LeanObject,
    mut v_prec_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_RBTree_instRepr___redArg___lam__0(v_inst_1327_, v_t_1328_, v_prec_1329_);
    crate::leanh::lean_dec(v_prec_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_RBTree_instRepr___redArg(
    mut v_inst_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1332_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1332_, 0, v_inst_1331_);
    return v___f_1332_;
}
pub unsafe fn l_Lean_RBTree_instRepr(
    mut v_00_u03b1_1333_: *mut crate::leanh::LeanObject,
    mut v_cmp_1334_: *mut crate::leanh::LeanObject,
    mut v_inst_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1336_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_instRepr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1336_, 0, v_inst_1335_);
    return v___f_1336_;
}
pub unsafe fn l_Lean_RBTree_instRepr___boxed(
    mut v_00_u03b1_1337_: *mut crate::leanh::LeanObject,
    mut v_cmp_1338_: *mut crate::leanh::LeanObject,
    mut v_inst_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_RBTree_instRepr(v_00_u03b1_1337_, v_cmp_1338_, v_inst_1339_);
    crate::leanh::lean_dec_ref(v_cmp_1338_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_RBTree_insert___redArg(
    mut v_cmp_1341_: *mut crate::leanh::LeanObject,
    mut v_t_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = crate::leanh::lean_box(0);
    v___x_1345_ = l_Lean_RBNode_insert___redArg(v_cmp_1341_, v_t_1342_, v_a_1343_, v___x_1344_);
    return v___x_1345_;
}
pub unsafe fn l_Lean_RBTree_insert(
    mut v_00_u03b1_1346_: *mut crate::leanh::LeanObject,
    mut v_cmp_1347_: *mut crate::leanh::LeanObject,
    mut v_t_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = crate::leanh::lean_box(0);
    v___x_1351_ = l_Lean_RBNode_insert___redArg(v_cmp_1347_, v_t_1348_, v_a_1349_, v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_RBTree_erase___redArg(
    mut v_cmp_1352_: *mut crate::leanh::LeanObject,
    mut v_t_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_RBNode_erase___redArg(v_cmp_1352_, v_a_1354_, v_t_1353_);
    return v___x_1355_;
}
pub unsafe fn l_Lean_RBTree_erase(
    mut v_00_u03b1_1356_: *mut crate::leanh::LeanObject,
    mut v_cmp_1357_: *mut crate::leanh::LeanObject,
    mut v_t_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_RBNode_erase___redArg(v_cmp_1357_, v_a_1359_, v_t_1358_);
    return v___x_1360_;
}
pub unsafe fn l_Lean_RBTree_ofList___redArg(
    mut v_cmp_1361_: *mut crate::leanh::LeanObject,
    mut v_x_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1362_) == 0 {
        let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_cmp_1361_);
        v___x_1363_ = crate::leanh::lean_box(0);
        return v___x_1363_;
    } else {
        let mut v_head_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1364_ = crate::leanh::lean_ctor_get(v_x_1362_, 0);
        crate::leanh::lean_inc(v_head_1364_);
        v_tail_1365_ = crate::leanh::lean_ctor_get(v_x_1362_, 1);
        crate::leanh::lean_inc(v_tail_1365_);
        crate::leanh::lean_dec_ref_known(v_x_1362_, 2);
        crate::leanh::lean_inc_ref(v_cmp_1361_);
        v_val_1366_ = l_Lean_RBTree_ofList___redArg(v_cmp_1361_, v_tail_1365_);
        v___x_1367_ = crate::leanh::lean_box(0);
        v___x_1368_ =
            l_Lean_RBNode_insert___redArg(v_cmp_1361_, v_val_1366_, v_head_1364_, v___x_1367_);
        return v___x_1368_;
    }
}
pub unsafe fn l_Lean_RBTree_ofList(
    mut v_00_u03b1_1369_: *mut crate::leanh::LeanObject,
    mut v_cmp_1370_: *mut crate::leanh::LeanObject,
    mut v_x_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_RBTree_ofList___redArg(v_cmp_1370_, v_x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Lean_RBTree_find_x3f___redArg(
    mut v_cmp_1373_: *mut crate::leanh::LeanObject,
    mut v_t_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v_fst_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1376_ = l_Lean_RBNode_findCore___redArg(v_cmp_1373_, v_t_1374_, v_a_1375_);
                if crate::leanh::lean_obj_tag(v___x_1376_) == 0 {
                    v___x_1377_ = crate::leanh::lean_box(0);
                    return v___x_1377_;
                } else {
                    v_val_1378_ = crate::leanh::lean_ctor_get(v___x_1376_, 0);
                    v_isSharedCheck_1386_ = (!crate::leanh::lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1380_ = v___x_1376_;
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1378_);
                        crate::leanh::lean_dec(v___x_1376_);
                        v___x_1380_ = crate::leanh::lean_box(0);
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1382_ = crate::leanh::lean_ctor_get(v_val_1378_, 0);
                crate::leanh::lean_inc(v_fst_1382_);
                crate::leanh::lean_dec(v_val_1378_);
                if v_isShared_1381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1380_, 0, v_fst_1382_);
                    v___x_1384_ = v___x_1380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_fst_1382_);
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
    mut v_00_u03b1_1387_: *mut crate::leanh::LeanObject,
    mut v_cmp_1388_: *mut crate::leanh::LeanObject,
    mut v_t_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1396_: u8 = 0;
    let mut v_fst_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1391_ = l_Lean_RBNode_findCore___redArg(v_cmp_1388_, v_t_1389_, v_a_1390_);
                if crate::leanh::lean_obj_tag(v___x_1391_) == 0 {
                    v___x_1392_ = crate::leanh::lean_box(0);
                    return v___x_1392_;
                } else {
                    v_val_1393_ = crate::leanh::lean_ctor_get(v___x_1391_, 0);
                    v_isSharedCheck_1401_ = (!crate::leanh::lean_is_exclusive(v___x_1391_)) as u8;
                    if v_isSharedCheck_1401_ == 0 {
                        v___x_1395_ = v___x_1391_;
                        v_isShared_1396_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1393_);
                        crate::leanh::lean_dec(v___x_1391_);
                        v___x_1395_ = crate::leanh::lean_box(0);
                        v_isShared_1396_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1397_ = crate::leanh::lean_ctor_get(v_val_1393_, 0);
                crate::leanh::lean_inc(v_fst_1397_);
                crate::leanh::lean_dec(v_val_1393_);
                if v_isShared_1396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1395_, 0, v_fst_1397_);
                    v___x_1399_ = v___x_1395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_fst_1397_);
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
    mut v_cmp_1402_: *mut crate::leanh::LeanObject,
    mut v_t_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Lean_RBNode_findCore___redArg(v_cmp_1402_, v_t_1403_, v_a_1404_);
    if crate::leanh::lean_obj_tag(v___x_1405_) == 0 {
        let mut v___x_1406_: u8 = 0;
        v___x_1406_ = 0;
        return v___x_1406_;
    } else {
        let mut v___x_1407_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_1405_, 1);
        v___x_1407_ = 1;
        return v___x_1407_;
    }
}
pub unsafe fn l_Lean_RBTree_contains___redArg___boxed(
    mut v_cmp_1408_: *mut crate::leanh::LeanObject,
    mut v_t_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1411_: u8 = 0;
    let mut v_r_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_RBTree_contains___redArg(v_cmp_1408_, v_t_1409_, v_a_1410_);
    v_r_1412_ = crate::leanh::lean_box((v_res_1411_) as usize);
    return v_r_1412_;
}
pub unsafe fn l_Lean_RBTree_contains(
    mut v_00_u03b1_1413_: *mut crate::leanh::LeanObject,
    mut v_cmp_1414_: *mut crate::leanh::LeanObject,
    mut v_t_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_RBNode_findCore___redArg(v_cmp_1414_, v_t_1415_, v_a_1416_);
    if crate::leanh::lean_obj_tag(v___x_1417_) == 0 {
        let mut v___x_1418_: u8 = 0;
        v___x_1418_ = 0;
        return v___x_1418_;
    } else {
        let mut v___x_1419_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_1417_, 1);
        v___x_1419_ = 1;
        return v___x_1419_;
    }
}
pub unsafe fn l_Lean_RBTree_contains___boxed(
    mut v_00_u03b1_1420_: *mut crate::leanh::LeanObject,
    mut v_cmp_1421_: *mut crate::leanh::LeanObject,
    mut v_t_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lean_RBTree_contains(v_00_u03b1_1420_, v_cmp_1421_, v_t_1422_, v_a_1423_);
    v_r_1425_ = crate::leanh::lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(
    mut v_cmp_1426_: *mut crate::leanh::LeanObject,
    mut v_x_1427_: *mut crate::leanh::LeanObject,
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v_x_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1432_: u8 = 0;
    let mut v_lchild_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_lchild_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1464_: u8 = 0;
    let mut v_lchild_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1485_: u8 = 0;
    let mut v_lchild_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1490_: u8 = 0;
    let mut v_lchild_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1517_: u8 = 0;
    let mut v_lchild_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v_unused_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1542_: u8 = 0;
    let mut v_lchild_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kx_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vx_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ky_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vy_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kz_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vz_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1563_: u8 = 0;
    let mut v_lchild_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1568_: u8 = 0;
    let mut v_lchild_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_unused_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_unused_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_color_1595_: u8 = 0;
    let mut v_lchild_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1427_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1426_);
                    v___x_1430_ = 0;
                    v___x_1431_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1431_, 0, v_x_1427_);
                    crate::leanh::lean_ctor_set(v___x_1431_, 1, v_x_1428_);
                    crate::leanh::lean_ctor_set(v___x_1431_, 2, v_x_1429_);
                    crate::leanh::lean_ctor_set(v___x_1431_, 3, v_x_1427_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1431_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_1430_,
                    );
                    return v___x_1431_;
                } else {
                    v_color_1432_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_1427_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    if v_color_1432_ == 0 {
                        v_lchild_1433_ = crate::leanh::lean_ctor_get(v_x_1427_, 0);
                        v_key_1434_ = crate::leanh::lean_ctor_get(v_x_1427_, 1);
                        v_val_1435_ = crate::leanh::lean_ctor_get(v_x_1427_, 2);
                        v_rchild_1436_ = crate::leanh::lean_ctor_get(v_x_1427_, 3);
                        v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v_x_1427_)) as u8;
                        if v_isSharedCheck_1453_ == 0 {
                            v___x_1438_ = v_x_1427_;
                            v_isShared_1439_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_1436_);
                            crate::leanh::lean_inc(v_val_1435_);
                            crate::leanh::lean_inc(v_key_1434_);
                            crate::leanh::lean_inc(v_lchild_1433_);
                            crate::leanh::lean_dec(v_x_1427_);
                            v___x_1438_ = crate::leanh::lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_lchild_1454_ = crate::leanh::lean_ctor_get(v_x_1427_, 0);
                        v_key_1455_ = crate::leanh::lean_ctor_get(v_x_1427_, 1);
                        v_val_1456_ = crate::leanh::lean_ctor_get(v_x_1427_, 2);
                        v_rchild_1457_ = crate::leanh::lean_ctor_get(v_x_1427_, 3);
                        v_isSharedCheck_1616_ = (!crate::leanh::lean_is_exclusive(v_x_1427_)) as u8;
                        if v_isSharedCheck_1616_ == 0 {
                            v___x_1459_ = v_x_1427_;
                            v_isShared_1460_ = v_isSharedCheck_1616_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_rchild_1457_);
                            crate::leanh::lean_inc(v_val_1456_);
                            crate::leanh::lean_inc(v_key_1455_);
                            crate::leanh::lean_inc(v_lchild_1454_);
                            crate::leanh::lean_dec(v_x_1427_);
                            v___x_1459_ = crate::leanh::lean_box(0);
                            v_isShared_1460_ = v_isSharedCheck_1616_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_1426_);
                crate::leanh::lean_inc(v_key_1434_);
                crate::leanh::lean_inc(v_x_1428_);
                v___x_1440_ = crate::leanh::lean_apply_2(v_cmp_1426_, v_x_1428_, v_key_1434_);
                v___x_1441_ = (crate::leanh::lean_unbox(v___x_1440_) as u8);
                match v___x_1441_ {
                    0 => {
                        v___x_1442_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_lchild_1433_, v_x_1428_, v_x_1429_);
                        if v_isShared_1439_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1442_);
                            v___x_1444_ = v___x_1438_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1445_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_key_1434_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_val_1435_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_rchild_1436_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_1445_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1444_ = v_reuseFailAlloc_1445_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_1435_);
                        crate::leanh::lean_dec(v_key_1434_);
                        crate::leanh::lean_dec_ref(v_cmp_1426_);
                        if v_isShared_1439_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1438_, 2, v_x_1429_);
                            crate::leanh::lean_ctor_set(v___x_1438_, 1, v_x_1428_);
                            v___x_1447_ = v___x_1438_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1448_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_lchild_1433_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_x_1428_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_x_1429_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_rchild_1436_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_1448_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
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
                            crate::leanh::lean_ctor_set(v___x_1438_, 3, v___x_1449_);
                            v___x_1451_ = v___x_1438_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1452_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_lchild_1433_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_key_1434_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_val_1435_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 3, v___x_1449_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_1452_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
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
                crate::leanh::lean_inc_ref(v_cmp_1426_);
                crate::leanh::lean_inc(v_key_1455_);
                crate::leanh::lean_inc(v_x_1428_);
                v___x_1461_ = crate::leanh::lean_apply_2(v_cmp_1426_, v_x_1428_, v_key_1455_);
                v___x_1462_ = (crate::leanh::lean_unbox(v___x_1461_) as u8);
                match v___x_1462_ {
                    0 => {
                        v___x_1463_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_lchild_1454_, v_x_1428_, v_x_1429_);
                        if crate::leanh::lean_obj_tag(v___x_1463_) == 1 {
                            v_color_1464_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_1463_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_1465_ = crate::leanh::lean_ctor_get(v___x_1463_, 0);
                            crate::leanh::lean_inc(v_lchild_1465_);
                            v_key_1466_ = crate::leanh::lean_ctor_get(v___x_1463_, 1);
                            crate::leanh::lean_inc(v_key_1466_);
                            v_val_1467_ = crate::leanh::lean_ctor_get(v___x_1463_, 2);
                            crate::leanh::lean_inc(v_val_1467_);
                            v_rchild_1468_ = crate::leanh::lean_ctor_get(v___x_1463_, 3);
                            crate::leanh::lean_inc(v_rchild_1468_);
                            if v_color_1464_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_1465_) == 1 {
                                    v_color_1485_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_1465_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_1485_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1463_, 4);
                                        v_lchild_1486_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1465_, 0);
                                        crate::leanh::lean_inc(v_lchild_1486_);
                                        v_key_1487_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1465_, 1);
                                        crate::leanh::lean_inc(v_key_1487_);
                                        v_val_1488_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1465_, 2);
                                        crate::leanh::lean_inc(v_val_1488_);
                                        v_rchild_1489_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1465_, 3);
                                        crate::leanh::lean_inc(v_rchild_1489_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_1465_, 4);
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
                                        if crate::leanh::lean_obj_tag(v_rchild_1468_) == 1 {
                                            v_color_1490_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_1468_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_1490_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_1463_, 4);
                                                v_lchild_1491_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 0);
                                                crate::leanh::lean_inc(v_lchild_1491_);
                                                v_key_1492_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 1);
                                                crate::leanh::lean_inc(v_key_1492_);
                                                v_val_1493_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 2);
                                                crate::leanh::lean_inc(v_val_1493_);
                                                v_rchild_1494_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 3);
                                                crate::leanh::lean_inc(v_rchild_1494_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_1468_, 4);
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
                                                crate::leanh::lean_dec_ref_known(v_lchild_1465_, 4);
                                                crate::leanh::lean_dec(v_val_1467_);
                                                crate::leanh::lean_dec(v_key_1466_);
                                                crate::leanh::lean_del_object(v___x_1459_);
                                                v_isSharedCheck_1501_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_1468_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_1501_ == 0 {
                                                    v_unused_1502_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1468_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1502_);
                                                    v_unused_1503_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1468_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1503_);
                                                    v_unused_1504_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1468_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1504_);
                                                    v_unused_1505_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1468_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1505_);
                                                    v___x_1496_ = v_rchild_1468_;
                                                    v_isShared_1497_ = v_isSharedCheck_1501_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_1468_);
                                                    v___x_1496_ = crate::leanh::lean_box(0);
                                                    v_isShared_1497_ = v_isSharedCheck_1501_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_1468_);
                                            crate::leanh::lean_dec(v_val_1467_);
                                            crate::leanh::lean_dec(v_key_1466_);
                                            crate::leanh::lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1512_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_1465_))
                                                    as u8;
                                            if v_isSharedCheck_1512_ == 0 {
                                                v_unused_1513_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1465_, 3);
                                                crate::leanh::lean_dec(v_unused_1513_);
                                                v_unused_1514_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1465_, 2);
                                                crate::leanh::lean_dec(v_unused_1514_);
                                                v_unused_1515_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1465_, 1);
                                                crate::leanh::lean_dec(v_unused_1515_);
                                                v_unused_1516_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1465_, 0);
                                                crate::leanh::lean_dec(v_unused_1516_);
                                                v___x_1507_ = v_lchild_1465_;
                                                v_isShared_1508_ = v_isSharedCheck_1512_;
                                                state = 10;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_1465_);
                                                v___x_1507_ = crate::leanh::lean_box(0);
                                                v_isShared_1508_ = v_isSharedCheck_1512_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_1468_) == 1 {
                                        v_color_1517_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_1468_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_1517_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_1463_, 4);
                                            v_lchild_1518_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1468_, 0);
                                            crate::leanh::lean_inc(v_lchild_1518_);
                                            v_key_1519_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1468_, 1);
                                            crate::leanh::lean_inc(v_key_1519_);
                                            v_val_1520_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1468_, 2);
                                            crate::leanh::lean_inc(v_val_1520_);
                                            v_rchild_1521_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1468_, 3);
                                            crate::leanh::lean_inc(v_rchild_1521_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_1468_, 4);
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
                                            crate::leanh::lean_dec(v_val_1467_);
                                            crate::leanh::lean_dec(v_key_1466_);
                                            crate::leanh::lean_dec(v_lchild_1465_);
                                            crate::leanh::lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1528_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_1468_))
                                                    as u8;
                                            if v_isSharedCheck_1528_ == 0 {
                                                v_unused_1529_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 3);
                                                crate::leanh::lean_dec(v_unused_1529_);
                                                v_unused_1530_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 2);
                                                crate::leanh::lean_dec(v_unused_1530_);
                                                v_unused_1531_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 1);
                                                crate::leanh::lean_dec(v_unused_1531_);
                                                v_unused_1532_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1468_, 0);
                                                crate::leanh::lean_dec(v_unused_1532_);
                                                v___x_1523_ = v_rchild_1468_;
                                                v_isShared_1524_ = v_isSharedCheck_1528_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_1468_);
                                                v___x_1523_ = crate::leanh::lean_box(0);
                                                v_isShared_1524_ = v_isSharedCheck_1528_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_1468_);
                                        crate::leanh::lean_dec(v_val_1467_);
                                        crate::leanh::lean_dec(v_key_1466_);
                                        crate::leanh::lean_dec(v_lchild_1465_);
                                        crate::leanh::lean_del_object(v___x_1459_);
                                        v___x_1533_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1463_);
                                        crate::leanh::lean_ctor_set(v___x_1533_, 1, v_key_1455_);
                                        crate::leanh::lean_ctor_set(v___x_1533_, 2, v_val_1456_);
                                        crate::leanh::lean_ctor_set(v___x_1533_, 3, v_rchild_1457_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_1533_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_1432_,
                                        );
                                        return v___x_1533_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_1468_);
                                crate::leanh::lean_dec(v_val_1467_);
                                crate::leanh::lean_dec(v_key_1466_);
                                crate::leanh::lean_dec(v_lchild_1465_);
                                crate::leanh::lean_del_object(v___x_1459_);
                                v___x_1534_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1463_);
                                crate::leanh::lean_ctor_set(v___x_1534_, 1, v_key_1455_);
                                crate::leanh::lean_ctor_set(v___x_1534_, 2, v_val_1456_);
                                crate::leanh::lean_ctor_set(v___x_1534_, 3, v_rchild_1457_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_1534_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_1432_,
                                );
                                return v___x_1534_;
                            }
                        } else {
                            if v_isShared_1460_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1459_, 0, v___x_1463_);
                                v___x_1536_ = v___x_1459_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_1537_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1463_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_key_1455_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_val_1456_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1537_,
                                    3,
                                    v_rchild_1457_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_1537_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_1432_,
                                );
                                v___x_1536_ = v_reuseFailAlloc_1537_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_val_1456_);
                        crate::leanh::lean_dec(v_key_1455_);
                        crate::leanh::lean_dec_ref(v_cmp_1426_);
                        if v_isShared_1460_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1459_, 2, v_x_1429_);
                            crate::leanh::lean_ctor_set(v___x_1459_, 1, v_x_1428_);
                            v___x_1539_ = v___x_1459_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_1540_ =
                                crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_lchild_1454_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_x_1428_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_x_1429_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_rchild_1457_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_1540_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_color_1432_,
                            );
                            v___x_1539_ = v_reuseFailAlloc_1540_;
                            state = 15;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1541_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1426_, v_rchild_1457_, v_x_1428_, v_x_1429_);
                        if crate::leanh::lean_obj_tag(v___x_1541_) == 1 {
                            v_color_1542_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_1541_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_lchild_1543_ = crate::leanh::lean_ctor_get(v___x_1541_, 0);
                            crate::leanh::lean_inc(v_lchild_1543_);
                            v_key_1544_ = crate::leanh::lean_ctor_get(v___x_1541_, 1);
                            crate::leanh::lean_inc(v_key_1544_);
                            v_val_1545_ = crate::leanh::lean_ctor_get(v___x_1541_, 2);
                            crate::leanh::lean_inc(v_val_1545_);
                            v_rchild_1546_ = crate::leanh::lean_ctor_get(v___x_1541_, 3);
                            crate::leanh::lean_inc(v_rchild_1546_);
                            if v_color_1542_ == 0 {
                                if crate::leanh::lean_obj_tag(v_lchild_1543_) == 1 {
                                    v_color_1563_ = crate::leanh::lean_ctor_get_uint8(
                                        v_lchild_1543_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    if v_color_1563_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1541_, 4);
                                        v_lchild_1564_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1543_, 0);
                                        crate::leanh::lean_inc(v_lchild_1564_);
                                        v_key_1565_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1543_, 1);
                                        crate::leanh::lean_inc(v_key_1565_);
                                        v_val_1566_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1543_, 2);
                                        crate::leanh::lean_inc(v_val_1566_);
                                        v_rchild_1567_ =
                                            crate::leanh::lean_ctor_get(v_lchild_1543_, 3);
                                        crate::leanh::lean_inc(v_rchild_1567_);
                                        crate::leanh::lean_dec_ref_known(v_lchild_1543_, 4);
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
                                        if crate::leanh::lean_obj_tag(v_rchild_1546_) == 1 {
                                            v_color_1568_ = crate::leanh::lean_ctor_get_uint8(
                                                v_rchild_1546_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 4)
                                                    as u32,
                                            );
                                            if v_color_1568_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_1541_, 4);
                                                v_lchild_1569_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 0);
                                                crate::leanh::lean_inc(v_lchild_1569_);
                                                v_key_1570_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 1);
                                                crate::leanh::lean_inc(v_key_1570_);
                                                v_val_1571_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 2);
                                                crate::leanh::lean_inc(v_val_1571_);
                                                v_rchild_1572_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 3);
                                                crate::leanh::lean_inc(v_rchild_1572_);
                                                crate::leanh::lean_dec_ref_known(v_rchild_1546_, 4);
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
                                                crate::leanh::lean_dec_ref_known(v_lchild_1543_, 4);
                                                crate::leanh::lean_dec(v_val_1545_);
                                                crate::leanh::lean_dec(v_key_1544_);
                                                crate::leanh::lean_del_object(v___x_1459_);
                                                v_isSharedCheck_1579_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_rchild_1546_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_1579_ == 0 {
                                                    v_unused_1580_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1546_,
                                                        3,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1580_);
                                                    v_unused_1581_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1546_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1581_);
                                                    v_unused_1582_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1546_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1582_);
                                                    v_unused_1583_ = crate::leanh::lean_ctor_get(
                                                        v_rchild_1546_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_1583_);
                                                    v___x_1574_ = v_rchild_1546_;
                                                    v_isShared_1575_ = v_isSharedCheck_1579_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_rchild_1546_);
                                                    v___x_1574_ = crate::leanh::lean_box(0);
                                                    v_isShared_1575_ = v_isSharedCheck_1579_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_rchild_1546_);
                                            crate::leanh::lean_dec(v_val_1545_);
                                            crate::leanh::lean_dec(v_key_1544_);
                                            crate::leanh::lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1590_ =
                                                (!crate::leanh::lean_is_exclusive(v_lchild_1543_))
                                                    as u8;
                                            if v_isSharedCheck_1590_ == 0 {
                                                v_unused_1591_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1543_, 3);
                                                crate::leanh::lean_dec(v_unused_1591_);
                                                v_unused_1592_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1543_, 2);
                                                crate::leanh::lean_dec(v_unused_1592_);
                                                v_unused_1593_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1543_, 1);
                                                crate::leanh::lean_dec(v_unused_1593_);
                                                v_unused_1594_ =
                                                    crate::leanh::lean_ctor_get(v_lchild_1543_, 0);
                                                crate::leanh::lean_dec(v_unused_1594_);
                                                v___x_1585_ = v_lchild_1543_;
                                                v_isShared_1586_ = v_isSharedCheck_1590_;
                                                state = 20;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_lchild_1543_);
                                                v___x_1585_ = crate::leanh::lean_box(0);
                                                v_isShared_1586_ = v_isSharedCheck_1590_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_rchild_1546_) == 1 {
                                        v_color_1595_ = crate::leanh::lean_ctor_get_uint8(
                                            v_rchild_1546_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                        );
                                        if v_color_1595_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_1541_, 4);
                                            v_lchild_1596_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1546_, 0);
                                            crate::leanh::lean_inc(v_lchild_1596_);
                                            v_key_1597_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1546_, 1);
                                            crate::leanh::lean_inc(v_key_1597_);
                                            v_val_1598_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1546_, 2);
                                            crate::leanh::lean_inc(v_val_1598_);
                                            v_rchild_1599_ =
                                                crate::leanh::lean_ctor_get(v_rchild_1546_, 3);
                                            crate::leanh::lean_inc(v_rchild_1599_);
                                            crate::leanh::lean_dec_ref_known(v_rchild_1546_, 4);
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
                                            crate::leanh::lean_dec(v_val_1545_);
                                            crate::leanh::lean_dec(v_key_1544_);
                                            crate::leanh::lean_dec(v_lchild_1543_);
                                            crate::leanh::lean_del_object(v___x_1459_);
                                            v_isSharedCheck_1606_ =
                                                (!crate::leanh::lean_is_exclusive(v_rchild_1546_))
                                                    as u8;
                                            if v_isSharedCheck_1606_ == 0 {
                                                v_unused_1607_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 3);
                                                crate::leanh::lean_dec(v_unused_1607_);
                                                v_unused_1608_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 2);
                                                crate::leanh::lean_dec(v_unused_1608_);
                                                v_unused_1609_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 1);
                                                crate::leanh::lean_dec(v_unused_1609_);
                                                v_unused_1610_ =
                                                    crate::leanh::lean_ctor_get(v_rchild_1546_, 0);
                                                crate::leanh::lean_dec(v_unused_1610_);
                                                v___x_1601_ = v_rchild_1546_;
                                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                                state = 22;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_rchild_1546_);
                                                v___x_1601_ = crate::leanh::lean_box(0);
                                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                                state = 22;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_rchild_1546_);
                                        crate::leanh::lean_dec(v_val_1545_);
                                        crate::leanh::lean_dec(v_key_1544_);
                                        crate::leanh::lean_dec(v_lchild_1543_);
                                        crate::leanh::lean_del_object(v___x_1459_);
                                        v___x_1611_ =
                                            crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1611_, 0, v_lchild_1454_);
                                        crate::leanh::lean_ctor_set(v___x_1611_, 1, v_key_1455_);
                                        crate::leanh::lean_ctor_set(v___x_1611_, 2, v_val_1456_);
                                        crate::leanh::lean_ctor_set(v___x_1611_, 3, v___x_1541_);
                                        crate::leanh::lean_ctor_set_uint8(
                                            v___x_1611_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 4)
                                                as u32,
                                            v_color_1432_,
                                        );
                                        return v___x_1611_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_rchild_1546_);
                                crate::leanh::lean_dec(v_val_1545_);
                                crate::leanh::lean_dec(v_key_1544_);
                                crate::leanh::lean_dec(v_lchild_1543_);
                                crate::leanh::lean_del_object(v___x_1459_);
                                v___x_1612_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_1612_, 0, v_lchild_1454_);
                                crate::leanh::lean_ctor_set(v___x_1612_, 1, v_key_1455_);
                                crate::leanh::lean_ctor_set(v___x_1612_, 2, v_val_1456_);
                                crate::leanh::lean_ctor_set(v___x_1612_, 3, v___x_1541_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_1612_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_color_1432_,
                                );
                                return v___x_1612_;
                            }
                        } else {
                            if v_isShared_1460_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1459_, 3, v___x_1541_);
                                v___x_1614_ = v___x_1459_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_1615_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1615_,
                                    0,
                                    v_lchild_1454_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_key_1455_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_val_1456_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 3, v___x_1541_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_1615_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
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
                    crate::leanh::lean_ctor_set(v___x_1459_, 3, v_b_1473_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 2, v_vx_1472_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 1, v_kx_1471_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 0, v_a_1470_);
                    v___x_1481_ = v___x_1459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_kx_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_vx_1472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_b_1473_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1484_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_1432_,
                    );
                    v___x_1481_ = v_reuseFailAlloc_1484_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1482_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1482_, 0, v_c_1476_);
                crate::leanh::lean_ctor_set(v___x_1482_, 1, v_kz_1477_);
                crate::leanh::lean_ctor_set(v___x_1482_, 2, v_vz_1478_);
                crate::leanh::lean_ctor_set(v___x_1482_, 3, v_d_1479_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1482_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                v___x_1483_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1483_, 0, v___x_1481_);
                crate::leanh::lean_ctor_set(v___x_1483_, 1, v_ky_1474_);
                crate::leanh::lean_ctor_set(v___x_1483_, 2, v_vy_1475_);
                crate::leanh::lean_ctor_set(v___x_1483_, 3, v___x_1482_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1483_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1464_,
                );
                return v___x_1483_;
            }
            8 => {
                if v_isShared_1497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1496_, 3, v_rchild_1457_);
                    crate::leanh::lean_ctor_set(v___x_1496_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1496_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1463_);
                    v___x_1499_ = v___x_1496_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_rchild_1457_);
                    v___x_1499_ = v_reuseFailAlloc_1500_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1499_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1499_;
            }
            10 => {
                if v_isShared_1508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1507_, 3, v_rchild_1457_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1463_);
                    v___x_1510_ = v___x_1507_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_rchild_1457_);
                    v___x_1510_ = v_reuseFailAlloc_1511_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1510_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1510_;
            }
            12 => {
                if v_isShared_1524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1523_, 3, v_rchild_1457_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 0, v___x_1463_);
                    v___x_1526_ = v___x_1523_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_rchild_1457_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
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
                    crate::leanh::lean_ctor_set(v___x_1459_, 3, v_b_1551_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 2, v_vx_1550_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 1, v_kx_1549_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 0, v_a_1548_);
                    v___x_1559_ = v___x_1459_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_kx_1549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_vx_1550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_b_1551_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1562_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_color_1432_,
                    );
                    v___x_1559_ = v_reuseFailAlloc_1562_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1560_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1560_, 0, v_c_1554_);
                crate::leanh::lean_ctor_set(v___x_1560_, 1, v_kz_1555_);
                crate::leanh::lean_ctor_set(v___x_1560_, 2, v_vz_1556_);
                crate::leanh::lean_ctor_set(v___x_1560_, 3, v_d_1557_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                v___x_1561_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1559_);
                crate::leanh::lean_ctor_set(v___x_1561_, 1, v_ky_1552_);
                crate::leanh::lean_ctor_set(v___x_1561_, 2, v_vy_1553_);
                crate::leanh::lean_ctor_set(v___x_1561_, 3, v___x_1560_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1561_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1542_,
                );
                return v___x_1561_;
            }
            18 => {
                if v_isShared_1575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1574_, 3, v___x_1541_);
                    crate::leanh::lean_ctor_set(v___x_1574_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1574_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1574_, 0, v_lchild_1454_);
                    v___x_1577_ = v___x_1574_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_lchild_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 3, v___x_1541_);
                    v___x_1577_ = v_reuseFailAlloc_1578_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1577_;
            }
            20 => {
                if v_isShared_1586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1585_, 3, v___x_1541_);
                    crate::leanh::lean_ctor_set(v___x_1585_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1585_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1585_, 0, v_lchild_1454_);
                    v___x_1588_ = v___x_1585_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_lchild_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1541_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1588_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_color_1432_,
                );
                return v___x_1588_;
            }
            22 => {
                if v_isShared_1602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1601_, 3, v___x_1541_);
                    crate::leanh::lean_ctor_set(v___x_1601_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v___x_1601_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_lchild_1454_);
                    v___x_1604_ = v___x_1601_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_lchild_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_key_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_val_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___x_1541_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
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
    mut v_cmp_1617_: *mut crate::leanh::LeanObject,
    mut v_t_1618_: *mut crate::leanh::LeanObject,
    mut v_k_1619_: *mut crate::leanh::LeanObject,
    mut v_v_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: u8 = 0;
    v___x_1621_ = l_Lean_RBNode_isRed___redArg(v_t_1618_);
    if v___x_1621_ == 0 {
        let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1622_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1617_, v_t_1618_, v_k_1619_, v_v_1620_);
        return v___x_1622_;
    } else {
        let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1623_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1617_, v_t_1618_, v_k_1619_, v_v_1620_);
        v___x_1624_ = l_Lean_RBNode_setBlack___redArg(v___x_1623_);
        return v___x_1624_;
    }
}
pub unsafe fn l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
    mut v_cmp_1625_: *mut crate::leanh::LeanObject,
    mut v_x_1626_: *mut crate::leanh::LeanObject,
    mut v_x_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1627_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1625_);
                    return v_x_1626_;
                } else {
                    v_head_1628_ = crate::leanh::lean_ctor_get(v_x_1627_, 0);
                    crate::leanh::lean_inc(v_head_1628_);
                    v_tail_1629_ = crate::leanh::lean_ctor_get(v_x_1627_, 1);
                    crate::leanh::lean_inc(v_tail_1629_);
                    crate::leanh::lean_dec_ref_known(v_x_1627_, 2);
                    v___x_1630_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_cmp_1625_);
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
    mut v_l_1633_: *mut crate::leanh::LeanObject,
    mut v_cmp_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = crate::leanh::lean_box(0);
    v___x_1636_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
        v_cmp_1634_,
        v___x_1635_,
        v_l_1633_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Lean_RBTree_fromList(
    mut v_00_u03b1_1637_: *mut crate::leanh::LeanObject,
    mut v_l_1638_: *mut crate::leanh::LeanObject,
    mut v_cmp_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_RBTree_fromList___redArg(v_l_1638_, v_cmp_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(
    mut v_00_u03b1_1641_: *mut crate::leanh::LeanObject,
    mut v_cmp_1642_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1643_: *mut crate::leanh::LeanObject,
    mut v_t_1644_: *mut crate::leanh::LeanObject,
    mut v_k_1645_: *mut crate::leanh::LeanObject,
    mut v_v_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(
        v_cmp_1642_,
        v_t_1644_,
        v_k_1645_,
        v_v_1646_,
    );
    return v___x_1647_;
}
pub unsafe fn l_List_foldl___at___00Lean_RBTree_fromList_spec__1(
    mut v_00_u03b1_1648_: *mut crate::leanh::LeanObject,
    mut v_cmp_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: *mut crate::leanh::LeanObject,
    mut v_x_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(
        v_cmp_1649_,
        v_x_1650_,
        v_x_1651_,
    );
    return v___x_1652_;
}
pub unsafe fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(
    mut v_00_u03b1_1653_: *mut crate::leanh::LeanObject,
    mut v_cmp_1654_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1655_: *mut crate::leanh::LeanObject,
    mut v_x_1656_: *mut crate::leanh::LeanObject,
    mut v_x_1657_: *mut crate::leanh::LeanObject,
    mut v_x_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_1654_, v_x_1656_, v_x_1657_, v_x_1658_);
    return v___x_1659_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(
    mut v_cmp_1660_: *mut crate::leanh::LeanObject,
    mut v_as_1661_: *mut crate::leanh::LeanObject,
    mut v_i_1662_: usize,
    mut v_stop_1663_: usize,
    mut v_b_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: usize = 0;
    let mut v___x_1670_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1665_ = lean_usize_dec_eq(v_i_1662_, v_stop_1663_);
                if v___x_1665_ == 0 {
                    v___x_1666_ = lean_array_uget_borrowed(v_as_1661_, v_i_1662_);
                    v___x_1667_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_1666_);
                    crate::leanh::lean_inc_ref(v_cmp_1660_);
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
                    crate::leanh::lean_dec_ref(v_cmp_1660_);
                    return v_b_1664_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(
    mut v_cmp_1672_: *mut crate::leanh::LeanObject,
    mut v_as_1673_: *mut crate::leanh::LeanObject,
    mut v_i_1674_: *mut crate::leanh::LeanObject,
    mut v_stop_1675_: *mut crate::leanh::LeanObject,
    mut v_b_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1677_: usize = 0;
    let mut v_stop_boxed_1678_: usize = 0;
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1677_ = crate::leanh::lean_unbox_usize(v_i_1674_);
    crate::leanh::lean_dec(v_i_1674_);
    v_stop_boxed_1678_ = crate::leanh::lean_unbox_usize(v_stop_1675_);
    crate::leanh::lean_dec(v_stop_1675_);
    v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1672_, v_as_1673_, v_i_boxed_1677_, v_stop_boxed_1678_, v_b_1676_);
    crate::leanh::lean_dec_ref(v_as_1673_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_RBTree_fromArray___redArg(
    mut v_l_1680_: *mut crate::leanh::LeanObject,
    mut v_cmp_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1682_ = crate::leanh::lean_box(0);
    v___x_1683_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1684_ = lean_array_get_size(v_l_1680_);
    v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
    if v___x_1685_ == 0 {
        crate::leanh::lean_dec_ref(v_cmp_1681_);
        return v___x_1682_;
    } else {
        let mut v___x_1686_: u8 = 0;
        v___x_1686_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
        if v___x_1686_ == 0 {
            if v___x_1685_ == 0 {
                crate::leanh::lean_dec_ref(v_cmp_1681_);
                return v___x_1682_;
            } else {
                let mut v___x_1687_: usize = 0;
                let mut v___x_1688_: usize = 0;
                let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1687_ = 0usize;
                v___x_1688_ = lean_usize_of_nat(v___x_1684_);
                v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1681_, v_l_1680_, v___x_1687_, v___x_1688_, v___x_1682_);
                return v___x_1689_;
            }
        } else {
            let mut v___x_1690_: usize = 0;
            let mut v___x_1691_: usize = 0;
            let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1690_ = 0usize;
            v___x_1691_ = lean_usize_of_nat(v___x_1684_);
            v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1681_, v_l_1680_, v___x_1690_, v___x_1691_, v___x_1682_);
            return v___x_1692_;
        }
    }
}
pub unsafe fn l_Lean_RBTree_fromArray___redArg___boxed(
    mut v_l_1693_: *mut crate::leanh::LeanObject,
    mut v_cmp_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_RBTree_fromArray___redArg(v_l_1693_, v_cmp_1694_);
    crate::leanh::lean_dec_ref(v_l_1693_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_RBTree_fromArray(
    mut v_00_u03b1_1696_: *mut crate::leanh::LeanObject,
    mut v_l_1697_: *mut crate::leanh::LeanObject,
    mut v_cmp_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_RBTree_fromArray___redArg(v_l_1697_, v_cmp_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lean_RBTree_fromArray___boxed(
    mut v_00_u03b1_1700_: *mut crate::leanh::LeanObject,
    mut v_l_1701_: *mut crate::leanh::LeanObject,
    mut v_cmp_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_RBTree_fromArray(v_00_u03b1_1700_, v_l_1701_, v_cmp_1702_);
    crate::leanh::lean_dec_ref(v_l_1701_);
    return v_res_1703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(
    mut v_00_u03b1_1704_: *mut crate::leanh::LeanObject,
    mut v_cmp_1705_: *mut crate::leanh::LeanObject,
    mut v_as_1706_: *mut crate::leanh::LeanObject,
    mut v_i_1707_: usize,
    mut v_stop_1708_: usize,
    mut v_b_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_1705_, v_as_1706_, v_i_1707_, v_stop_1708_, v_b_1709_);
    return v___x_1710_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(
    mut v_00_u03b1_1711_: *mut crate::leanh::LeanObject,
    mut v_cmp_1712_: *mut crate::leanh::LeanObject,
    mut v_as_1713_: *mut crate::leanh::LeanObject,
    mut v_i_1714_: *mut crate::leanh::LeanObject,
    mut v_stop_1715_: *mut crate::leanh::LeanObject,
    mut v_b_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1717_: usize = 0;
    let mut v_stop_boxed_1718_: usize = 0;
    let mut v_res_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1717_ = crate::leanh::lean_unbox_usize(v_i_1714_);
    crate::leanh::lean_dec(v_i_1714_);
    v_stop_boxed_1718_ = crate::leanh::lean_unbox_usize(v_stop_1715_);
    crate::leanh::lean_dec(v_stop_1715_);
    v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(v_00_u03b1_1711_, v_cmp_1712_, v_as_1713_, v_i_boxed_1717_, v_stop_boxed_1718_, v_b_1716_);
    crate::leanh::lean_dec_ref(v_as_1713_);
    return v_res_1719_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___lam__0(
    mut v_p_1720_: *mut crate::leanh::LeanObject,
    mut v_a_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    v___x_1723_ = crate::leanh::lean_apply_1(v_p_1720_, v_a_1721_);
    v___x_1724_ = (crate::leanh::lean_unbox(v___x_1723_) as u8);
    return v___x_1724_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___lam__0___boxed(
    mut v_p_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_x_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1728_: u8 = 0;
    let mut v_r_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lean_RBTree_all___redArg___lam__0(v_p_1725_, v_a_1726_, v_x_1727_);
    v_r_1729_ = crate::leanh::lean_box((v_res_1728_) as usize);
    return v_r_1729_;
}
pub unsafe fn l_Lean_RBTree_all___redArg(
    mut v_t_1730_: *mut crate::leanh::LeanObject,
    mut v_p_1731_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    v___f_1732_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1732_, 0, v_p_1731_);
    v___x_1733_ = l_Lean_RBNode_all___redArg(v___f_1732_, v_t_1730_);
    return v___x_1733_;
}
pub unsafe fn l_Lean_RBTree_all___redArg___boxed(
    mut v_t_1734_: *mut crate::leanh::LeanObject,
    mut v_p_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1736_: u8 = 0;
    let mut v_r_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_RBTree_all___redArg(v_t_1734_, v_p_1735_);
    v_r_1737_ = crate::leanh::lean_box((v_res_1736_) as usize);
    return v_r_1737_;
}
pub unsafe fn l_Lean_RBTree_all(
    mut v_00_u03b1_1738_: *mut crate::leanh::LeanObject,
    mut v_cmp_1739_: *mut crate::leanh::LeanObject,
    mut v_t_1740_: *mut crate::leanh::LeanObject,
    mut v_p_1741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    v___f_1742_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1742_, 0, v_p_1741_);
    v___x_1743_ = l_Lean_RBNode_all___redArg(v___f_1742_, v_t_1740_);
    return v___x_1743_;
}
pub unsafe fn l_Lean_RBTree_all___boxed(
    mut v_00_u03b1_1744_: *mut crate::leanh::LeanObject,
    mut v_cmp_1745_: *mut crate::leanh::LeanObject,
    mut v_t_1746_: *mut crate::leanh::LeanObject,
    mut v_p_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1748_: u8 = 0;
    let mut v_r_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lean_RBTree_all(v_00_u03b1_1744_, v_cmp_1745_, v_t_1746_, v_p_1747_);
    crate::leanh::lean_dec_ref(v_cmp_1745_);
    v_r_1749_ = crate::leanh::lean_box((v_res_1748_) as usize);
    return v_r_1749_;
}
pub unsafe fn l_Lean_RBTree_any___redArg(
    mut v_t_1750_: *mut crate::leanh::LeanObject,
    mut v_p_1751_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    v___f_1752_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1752_, 0, v_p_1751_);
    v___x_1753_ = l_Lean_RBNode_any___redArg(v___f_1752_, v_t_1750_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_RBTree_any___redArg___boxed(
    mut v_t_1754_: *mut crate::leanh::LeanObject,
    mut v_p_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1756_: u8 = 0;
    let mut v_r_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1756_ = l_Lean_RBTree_any___redArg(v_t_1754_, v_p_1755_);
    v_r_1757_ = crate::leanh::lean_box((v_res_1756_) as usize);
    return v_r_1757_;
}
pub unsafe fn l_Lean_RBTree_any(
    mut v_00_u03b1_1758_: *mut crate::leanh::LeanObject,
    mut v_cmp_1759_: *mut crate::leanh::LeanObject,
    mut v_t_1760_: *mut crate::leanh::LeanObject,
    mut v_p_1761_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    v___f_1762_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1762_, 0, v_p_1761_);
    v___x_1763_ = l_Lean_RBNode_any___redArg(v___f_1762_, v_t_1760_);
    return v___x_1763_;
}
pub unsafe fn l_Lean_RBTree_any___boxed(
    mut v_00_u03b1_1764_: *mut crate::leanh::LeanObject,
    mut v_cmp_1765_: *mut crate::leanh::LeanObject,
    mut v_t_1766_: *mut crate::leanh::LeanObject,
    mut v_p_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Lean_RBTree_any(v_00_u03b1_1764_, v_cmp_1765_, v_t_1766_, v_p_1767_);
    crate::leanh::lean_dec_ref(v_cmp_1765_);
    v_r_1769_ = crate::leanh::lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
    mut v_cmp_1770_: *mut crate::leanh::LeanObject,
    mut v_x_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lchild_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1771_) == 0 {
                    crate::leanh::lean_dec(v_x_1772_);
                    crate::leanh::lean_dec_ref(v_cmp_1770_);
                    v___x_1773_ = crate::leanh::lean_box(0);
                    return v___x_1773_;
                } else {
                    v_lchild_1774_ = crate::leanh::lean_ctor_get(v_x_1771_, 0);
                    crate::leanh::lean_inc(v_lchild_1774_);
                    v_key_1775_ = crate::leanh::lean_ctor_get(v_x_1771_, 1);
                    crate::leanh::lean_inc_n(v_key_1775_, 2);
                    v_val_1776_ = crate::leanh::lean_ctor_get(v_x_1771_, 2);
                    crate::leanh::lean_inc(v_val_1776_);
                    v_rchild_1777_ = crate::leanh::lean_ctor_get(v_x_1771_, 3);
                    crate::leanh::lean_inc(v_rchild_1777_);
                    crate::leanh::lean_dec_ref_known(v_x_1771_, 4);
                    crate::leanh::lean_inc_ref(v_cmp_1770_);
                    crate::leanh::lean_inc(v_x_1772_);
                    v___x_1778_ = crate::leanh::lean_apply_2(v_cmp_1770_, v_x_1772_, v_key_1775_);
                    v___x_1779_ = (crate::leanh::lean_unbox(v___x_1778_) as u8);
                    match v___x_1779_ {
                        0 => {
                            crate::leanh::lean_dec(v_rchild_1777_);
                            crate::leanh::lean_dec(v_val_1776_);
                            crate::leanh::lean_dec(v_key_1775_);
                            v_x_1771_ = v_lchild_1774_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_rchild_1777_);
                            crate::leanh::lean_dec(v_lchild_1774_);
                            crate::leanh::lean_dec(v_x_1772_);
                            crate::leanh::lean_dec_ref(v_cmp_1770_);
                            v___x_1781_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1781_, 0, v_key_1775_);
                            crate::leanh::lean_ctor_set(v___x_1781_, 1, v_val_1776_);
                            v___x_1782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
                            return v___x_1782_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_val_1776_);
                            crate::leanh::lean_dec(v_key_1775_);
                            crate::leanh::lean_dec(v_lchild_1774_);
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
    mut v_t_u2082_1784_: *mut crate::leanh::LeanObject,
    mut v_cmp_1785_: *mut crate::leanh::LeanObject,
    mut v_x_1786_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1787_: u8 = 0;
    let mut v_lchild_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1786_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1785_);
                    crate::leanh::lean_dec(v_t_u2082_1784_);
                    v___x_1787_ = 1;
                    return v___x_1787_;
                } else {
                    v_lchild_1788_ = crate::leanh::lean_ctor_get(v_x_1786_, 0);
                    crate::leanh::lean_inc(v_lchild_1788_);
                    v_key_1789_ = crate::leanh::lean_ctor_get(v_x_1786_, 1);
                    crate::leanh::lean_inc(v_key_1789_);
                    v_rchild_1790_ = crate::leanh::lean_ctor_get(v_x_1786_, 3);
                    crate::leanh::lean_inc(v_rchild_1790_);
                    crate::leanh::lean_dec_ref_known(v_x_1786_, 4);
                    crate::leanh::lean_inc(v_t_u2082_1784_);
                    crate::leanh::lean_inc_ref(v_cmp_1785_);
                    v___x_1791_ =
                        l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
                            v_cmp_1785_,
                            v_t_u2082_1784_,
                            v_key_1789_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                        crate::leanh::lean_dec(v_rchild_1790_);
                        crate::leanh::lean_dec(v_lchild_1788_);
                        crate::leanh::lean_dec_ref(v_cmp_1785_);
                        crate::leanh::lean_dec(v_t_u2082_1784_);
                        v___x_1792_ = 0;
                        return v___x_1792_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1791_, 1);
                        crate::leanh::lean_inc_ref(v_cmp_1785_);
                        crate::leanh::lean_inc(v_t_u2082_1784_);
                        v___x_1793_ =
                            l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
                                v_t_u2082_1784_,
                                v_cmp_1785_,
                                v_lchild_1788_,
                            );
                        if v___x_1793_ == 0 {
                            crate::leanh::lean_dec(v_rchild_1790_);
                            crate::leanh::lean_dec_ref(v_cmp_1785_);
                            crate::leanh::lean_dec(v_t_u2082_1784_);
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
    mut v_t_u2082_1795_: *mut crate::leanh::LeanObject,
    mut v_cmp_1796_: *mut crate::leanh::LeanObject,
    mut v_x_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: u8 = 0;
    let mut v_r_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1795_,
        v_cmp_1796_,
        v_x_1797_,
    );
    v_r_1799_ = crate::leanh::lean_box((v_res_1798_) as usize);
    return v_r_1799_;
}
pub unsafe fn l_Lean_RBTree_subset___redArg(
    mut v_cmp_1800_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1801_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1802_: *mut crate::leanh::LeanObject,
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
    mut v_cmp_1804_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1805_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1807_: u8 = 0;
    let mut v_r_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lean_RBTree_subset___redArg(v_cmp_1804_, v_t_u2081_1805_, v_t_u2082_1806_);
    v_r_1808_ = crate::leanh::lean_box((v_res_1807_) as usize);
    return v_r_1808_;
}
pub unsafe fn l_Lean_RBTree_subset(
    mut v_00_u03b1_1809_: *mut crate::leanh::LeanObject,
    mut v_cmp_1810_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1811_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1812_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_1814_: *mut crate::leanh::LeanObject,
    mut v_cmp_1815_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1816_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: u8 = 0;
    let mut v_r_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_RBTree_subset(
        v_00_u03b1_1814_,
        v_cmp_1815_,
        v_t_u2081_1816_,
        v_t_u2082_1817_,
    );
    v_r_1819_ = crate::leanh::lean_box((v_res_1818_) as usize);
    return v_r_1819_;
}
pub unsafe fn l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(
    mut v_00_u03b1_1820_: *mut crate::leanh::LeanObject,
    mut v_cmp_1821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1822_: *mut crate::leanh::LeanObject,
    mut v_x_1823_: *mut crate::leanh::LeanObject,
    mut v_x_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(
        v_cmp_1821_,
        v_x_1823_,
        v_x_1824_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(
    mut v_00_u03b1_1826_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1827_: *mut crate::leanh::LeanObject,
    mut v_cmp_1828_: *mut crate::leanh::LeanObject,
    mut v_x_1829_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_1831_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1832_: *mut crate::leanh::LeanObject,
    mut v_cmp_1833_: *mut crate::leanh::LeanObject,
    mut v_x_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: u8 = 0;
    let mut v_r_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(
        v_00_u03b1_1831_,
        v_t_u2082_1832_,
        v_cmp_1833_,
        v_x_1834_,
    );
    v_r_1836_ = crate::leanh::lean_box((v_res_1835_) as usize);
    return v_r_1836_;
}
pub unsafe fn l_Lean_RBTree_seteq___redArg(
    mut v_cmp_1837_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1838_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1839_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1840_: u8 = 0;
    crate::leanh::lean_inc(v_t_u2081_1838_);
    crate::leanh::lean_inc_ref(v_cmp_1837_);
    crate::leanh::lean_inc(v_t_u2082_1839_);
    v___x_1840_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(
        v_t_u2082_1839_,
        v_cmp_1837_,
        v_t_u2081_1838_,
    );
    if v___x_1840_ == 0 {
        crate::leanh::lean_dec(v_t_u2082_1839_);
        crate::leanh::lean_dec(v_t_u2081_1838_);
        crate::leanh::lean_dec_ref(v_cmp_1837_);
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
    mut v_cmp_1842_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1843_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: u8 = 0;
    let mut v_r_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_RBTree_seteq___redArg(v_cmp_1842_, v_t_u2081_1843_, v_t_u2082_1844_);
    v_r_1846_ = crate::leanh::lean_box((v_res_1845_) as usize);
    return v_r_1846_;
}
pub unsafe fn l_Lean_RBTree_seteq(
    mut v_00_u03b1_1847_: *mut crate::leanh::LeanObject,
    mut v_cmp_1848_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1849_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1850_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1851_: u8 = 0;
    v___x_1851_ = l_Lean_RBTree_seteq___redArg(v_cmp_1848_, v_t_u2081_1849_, v_t_u2082_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_RBTree_seteq___boxed(
    mut v_00_u03b1_1852_: *mut crate::leanh::LeanObject,
    mut v_cmp_1853_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1854_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: u8 = 0;
    let mut v_r_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_RBTree_seteq(
        v_00_u03b1_1852_,
        v_cmp_1853_,
        v_t_u2081_1854_,
        v_t_u2082_1855_,
    );
    v_r_1857_ = crate::leanh::lean_box((v_res_1856_) as usize);
    return v_r_1857_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
    mut v_cmp_1858_: *mut crate::leanh::LeanObject,
    mut v_x_1859_: *mut crate::leanh::LeanObject,
    mut v_x_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1860_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1858_);
                    return v_x_1859_;
                } else {
                    v_lchild_1861_ = crate::leanh::lean_ctor_get(v_x_1860_, 0);
                    crate::leanh::lean_inc(v_lchild_1861_);
                    v_key_1862_ = crate::leanh::lean_ctor_get(v_x_1860_, 1);
                    crate::leanh::lean_inc(v_key_1862_);
                    v_rchild_1863_ = crate::leanh::lean_ctor_get(v_x_1860_, 3);
                    crate::leanh::lean_inc(v_rchild_1863_);
                    crate::leanh::lean_dec_ref_known(v_x_1860_, 4);
                    crate::leanh::lean_inc_ref_n(v_cmp_1858_, 2);
                    v_val_1864_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
                        v_cmp_1858_,
                        v_x_1859_,
                        v_lchild_1861_,
                    );
                    v___x_1865_ = crate::leanh::lean_box(0);
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
    mut v_cmp_1868_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1869_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_u2081_1869_) == 0 {
        crate::leanh::lean_dec_ref(v_cmp_1868_);
        return v_t_u2082_1870_;
    } else {
        let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1871_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
            v_cmp_1868_,
            v_t_u2081_1869_,
            v_t_u2082_1870_,
        );
        return v___x_1871_;
    }
}
pub unsafe fn l_Lean_RBTree_union(
    mut v_00_u03b1_1872_: *mut crate::leanh::LeanObject,
    mut v_cmp_1873_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1874_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_RBTree_union___redArg(v_cmp_1873_, v_t_u2081_1874_, v_t_u2082_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(
    mut v_00_u03b1_1877_: *mut crate::leanh::LeanObject,
    mut v_cmp_1878_: *mut crate::leanh::LeanObject,
    mut v_x_1879_: *mut crate::leanh::LeanObject,
    mut v_x_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(
        v_cmp_1878_,
        v_x_1879_,
        v_x_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(
    mut v_cmp_1882_: *mut crate::leanh::LeanObject,
    mut v_x_1883_: *mut crate::leanh::LeanObject,
    mut v_x_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1884_) == 0 {
                    crate::leanh::lean_dec(v_x_1883_);
                    crate::leanh::lean_dec_ref(v_cmp_1882_);
                    return v_x_1884_;
                } else {
                    v_lchild_1885_ = crate::leanh::lean_ctor_get(v_x_1884_, 0);
                    v_key_1886_ = crate::leanh::lean_ctor_get(v_x_1884_, 1);
                    v_val_1887_ = crate::leanh::lean_ctor_get(v_x_1884_, 2);
                    v_rchild_1888_ = crate::leanh::lean_ctor_get(v_x_1884_, 3);
                    v_isSharedCheck_1911_ = (!crate::leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1890_ = v_x_1884_;
                        v_isShared_1891_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rchild_1888_);
                        crate::leanh::lean_inc(v_val_1887_);
                        crate::leanh::lean_inc(v_key_1886_);
                        crate::leanh::lean_inc(v_lchild_1885_);
                        crate::leanh::lean_dec(v_x_1884_);
                        v___x_1890_ = crate::leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_1882_);
                crate::leanh::lean_inc(v_key_1886_);
                crate::leanh::lean_inc(v_x_1883_);
                v___x_1892_ = crate::leanh::lean_apply_2(v_cmp_1882_, v_x_1883_, v_key_1886_);
                v___x_1893_ = (crate::leanh::lean_unbox(v___x_1892_) as u8);
                match v___x_1893_ {
                    0 => {
                        v___x_1894_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1885_);
                        if v___x_1894_ == 0 {
                            v___x_1895_ = 0;
                            v___x_1896_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1882_, v_x_1883_, v_lchild_1885_);
                            if v_isShared_1891_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1890_, 0, v___x_1896_);
                                v___x_1898_ = v___x_1890_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1899_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_key_1886_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_val_1887_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1899_,
                                    3,
                                    v_rchild_1888_,
                                );
                                v___x_1898_ = v_reuseFailAlloc_1899_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1890_);
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
                        crate::leanh::lean_del_object(v___x_1890_);
                        crate::leanh::lean_dec(v_val_1887_);
                        crate::leanh::lean_dec(v_key_1886_);
                        crate::leanh::lean_dec(v_x_1883_);
                        crate::leanh::lean_dec_ref(v_cmp_1882_);
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
                                crate::leanh::lean_ctor_set(v___x_1890_, 3, v___x_1905_);
                                v___x_1907_ = v___x_1890_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1908_ =
                                    crate::leanh::lean_alloc_ctor(1, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1908_,
                                    0,
                                    v_lchild_1885_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_key_1886_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_val_1887_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 3, v___x_1905_);
                                v___x_1907_ = v_reuseFailAlloc_1908_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1890_);
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
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1898_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_1895_,
                );
                return v___x_1898_;
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1907_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_1904_,
                );
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(
    mut v_cmp_1912_: *mut crate::leanh::LeanObject,
    mut v_x_1913_: *mut crate::leanh::LeanObject,
    mut v_t_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_1915_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1912_, v_x_1913_, v_t_1914_);
    v___x_1916_ = l_Lean_RBNode_setBlack___redArg(v_t_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
    mut v_cmp_1917_: *mut crate::leanh::LeanObject,
    mut v_x_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lchild_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rchild_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1919_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1917_);
                    return v_x_1918_;
                } else {
                    v_lchild_1920_ = crate::leanh::lean_ctor_get(v_x_1919_, 0);
                    crate::leanh::lean_inc(v_lchild_1920_);
                    v_key_1921_ = crate::leanh::lean_ctor_get(v_x_1919_, 1);
                    crate::leanh::lean_inc(v_key_1921_);
                    v_rchild_1922_ = crate::leanh::lean_ctor_get(v_x_1919_, 3);
                    crate::leanh::lean_inc(v_rchild_1922_);
                    crate::leanh::lean_dec_ref_known(v_x_1919_, 4);
                    crate::leanh::lean_inc_ref_n(v_cmp_1917_, 2);
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
    mut v_cmp_1926_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1927_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1926_,
        v_t_u2081_1927_,
        v_t_u2082_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Lean_RBTree_diff(
    mut v_00_u03b1_1930_: *mut crate::leanh::LeanObject,
    mut v_cmp_1931_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_1932_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1931_,
        v_t_u2081_1932_,
        v_t_u2082_1933_,
    );
    return v___x_1934_;
}
pub unsafe fn l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_cmp_1936_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
    mut v_t_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(
        v_cmp_1936_,
        v_x_1938_,
        v_t_1939_,
    );
    return v___x_1940_;
}
pub unsafe fn l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(
    mut v_00_u03b1_1941_: *mut crate::leanh::LeanObject,
    mut v_cmp_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: *mut crate::leanh::LeanObject,
    mut v_x_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(
        v_cmp_1942_,
        v_x_1943_,
        v_x_1944_,
    );
    return v___x_1945_;
}
pub unsafe fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(
    mut v_00_u03b1_1946_: *mut crate::leanh::LeanObject,
    mut v_cmp_1947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_1947_, v_x_1949_, v_x_1950_);
    return v___x_1951_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg___lam__0(
    mut v_f_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
    mut v_x_1954_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    v___x_1955_ = crate::leanh::lean_apply_1(v_f_1952_, v_a_1953_);
    v___x_1956_ = (crate::leanh::lean_unbox(v___x_1955_) as u8);
    return v___x_1956_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg___lam__0___boxed(
    mut v_f_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_x_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: u8 = 0;
    let mut v_r_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_1957_, v_a_1958_, v_x_1959_);
    v_r_1961_ = crate::leanh::lean_box((v_res_1960_) as usize);
    return v_r_1961_;
}
pub unsafe fn l_Lean_RBTree_filter___redArg(
    mut v_cmp_1962_: *mut crate::leanh::LeanObject,
    mut v_f_1963_: *mut crate::leanh::LeanObject,
    mut v_m_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1965_ = crate::leanh::lean_alloc_closure(
        l_Lean_RBTree_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1965_, 0, v_f_1963_);
    v___x_1966_ = l_Lean_RBMap_filter___redArg(v_cmp_1962_, v___f_1965_, v_m_1964_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_RBTree_filter(
    mut v_00_u03b1_1967_: *mut crate::leanh::LeanObject,
    mut v_cmp_1968_: *mut crate::leanh::LeanObject,
    mut v_f_1969_: *mut crate::leanh::LeanObject,
    mut v_m_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Lean_RBTree_filter___redArg(v_cmp_1968_, v_f_1969_, v_m_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Lean_rbtreeOf___redArg(
    mut v_l_1972_: *mut crate::leanh::LeanObject,
    mut v_cmp_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = l_Lean_RBTree_fromList___redArg(v_l_1972_, v_cmp_1973_);
    return v___x_1974_;
}
pub unsafe fn l_Lean_rbtreeOf(
    mut v_00_u03b1_1975_: *mut crate::leanh::LeanObject,
    mut v_l_1976_: *mut crate::leanh::LeanObject,
    mut v_cmp_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1978_ = l_Lean_RBTree_fromList___redArg(v_l_1976_, v_cmp_1977_);
    return v___x_1978_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_RBTree(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_RBMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_RBTree(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_RBTree(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_RBMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RBTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_RBTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_RBTree(builtin);
}
