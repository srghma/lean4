// Lean compiler output
// Module: Lake.Build.Targets
// Imports: Lake.Config.Monad Lake.Config.InputFile Lake.Build.Infos
use crate::ffi::{lean_array_get_size, lean_array_push, lean_string_append};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_InputDir_defaultFacet, l_Lake_InputFile_defaultFacet, l_Lake_LeanExe_exeFacet,
    l_Lake_LeanLib_defaultFacet,
};
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Config::InputFile::{
    initialize_Lake_Config_InputFile, runtime_initialize_Lake_Config_InputFile,
};
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_InputDir_keyword, l_Lake_InputFile_keyword, l_Lake_LeanExe_keyword,
    l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::Monad::{
    initialize_Lake_Config_Monad, runtime_initialize_Lake_Config_Monad,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_get_x3f___redArg;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 32, 111, 102, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0,
    ],
};
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [47, 0],
};
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 119, 111, 114, 107,
        115, 112, 97, 99, 101, 0,
    ],
};
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_KConfigDecl_get___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_KConfigDecl_get___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_KConfigDecl_get___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [112, 97, 99, 107, 97, 103, 101, 32, 39, 0],
    };
static mut l_Lake_TargetDecl_fetch___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__1_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [39, 32, 111, 102, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0],
    };
static mut l_Lake_TargetDecl_fetch___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__2_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            39, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 101, 120, 105, 115, 116, 32, 105,
            110, 32, 119, 111, 114, 107, 115, 112, 97, 99, 101, 0,
        ],
    };
static mut l_Lake_TargetDecl_fetch___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_fetch___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0],
    };
static mut l_Lake_LeanLib_fetch___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_fetch___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value)
                as *mut leanh::LeanObject,
            12295998048739818339 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_fetch___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0(
    mut v_x_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1034_);
    return v_x_1034_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0___boxed(
    mut v_x_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lake_KConfigDecl_get___redArg___lam__0(v_x_1035_);
    leanh::lean_dec(v_x_1035_);
    return v_res_1036_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1(
    mut v_name_1040_: *mut leanh::LeanObject,
    mut v_config_1041_: *mut leanh::LeanObject,
    mut v_toPure_1042_: *mut leanh::LeanObject,
    mut v_pkg_1043_: *mut leanh::LeanObject,
    mut v_inst_1044_: *mut leanh::LeanObject,
    mut v_____x_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_1045_) == 1 {
        let mut v_val_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_1044_);
        leanh::lean_dec(v_pkg_1043_);
        v_val_1046_ = leanh::lean_ctor_get(v_____x_1045_, 0);
        leanh::lean_inc(v_val_1046_);
        v___x_1047_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1047_, 0, v_val_1046_);
        leanh::lean_ctor_set(v___x_1047_, 1, v_name_1040_);
        leanh::lean_ctor_set(v___x_1047_, 2, v_config_1041_);
        v___x_1048_ =
            leanh::lean_apply_2(v_toPure_1042_, leanh::lean_box(0), v___x_1047_);
        return v___x_1048_;
    } else {
        let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: u8 = 0;
        let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1042_);
        leanh::lean_dec(v_config_1041_);
        v___x_1049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
        v___x_1050_ = 1;
        v___x_1051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1043_,
            v___x_1050_,
        );
        v___x_1052_ = lean_string_append(v___x_1049_, v___x_1051_);
        leanh::lean_dec_ref(v___x_1051_);
        v___x_1053_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
        v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
        v___x_1055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1040_,
            v___x_1050_,
        );
        v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
        leanh::lean_dec_ref(v___x_1055_);
        v___x_1057_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
        v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
        v___x_1059_ =
            leanh::lean_apply_2(v_inst_1044_, leanh::lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1___boxed(
    mut v_name_1060_: *mut leanh::LeanObject,
    mut v_config_1061_: *mut leanh::LeanObject,
    mut v_toPure_1062_: *mut leanh::LeanObject,
    mut v_pkg_1063_: *mut leanh::LeanObject,
    mut v_inst_1064_: *mut leanh::LeanObject,
    mut v_____x_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lake_KConfigDecl_get___redArg___lam__1(
        v_name_1060_,
        v_config_1061_,
        v_toPure_1062_,
        v_pkg_1063_,
        v_inst_1064_,
        v_____x_1065_,
    );
    leanh::lean_dec(v_____x_1065_);
    return v_res_1066_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__2(
    mut v_pkg_1068_: *mut leanh::LeanObject,
    mut v_x_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packageMap_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1070_ = leanh::lean_ctor_get(v_x_1069_, 5);
    leanh::lean_inc(v_packageMap_1070_);
    leanh::lean_dec_ref(v_x_1069_);
    v___x_1071_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    v___x_1072_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1071_, v_packageMap_1070_, v_pkg_1068_);
    return v___x_1072_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg(
    mut v_inst_1074_: *mut leanh::LeanObject,
    mut v_inst_1075_: *mut leanh::LeanObject,
    mut v_inst_1076_: *mut leanh::LeanObject,
    mut v_self_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1078_ = leanh::lean_ctor_get(v_inst_1074_, 0);
    leanh::lean_inc_ref(v_toApplicative_1078_);
    v_toFunctor_1079_ = leanh::lean_ctor_get(v_toApplicative_1078_, 0);
    leanh::lean_inc_ref(v_toFunctor_1079_);
    v_toBind_1080_ = leanh::lean_ctor_get(v_inst_1074_, 1);
    leanh::lean_inc(v_toBind_1080_);
    leanh::lean_dec_ref(v_inst_1074_);
    v_toPure_1081_ = leanh::lean_ctor_get(v_toApplicative_1078_, 1);
    leanh::lean_inc(v_toPure_1081_);
    leanh::lean_dec_ref(v_toApplicative_1078_);
    v_pkg_1082_ = leanh::lean_ctor_get(v_self_1077_, 0);
    leanh::lean_inc_n(v_pkg_1082_, 2);
    v_name_1083_ = leanh::lean_ctor_get(v_self_1077_, 1);
    leanh::lean_inc(v_name_1083_);
    v_config_1084_ = leanh::lean_ctor_get(v_self_1077_, 3);
    leanh::lean_inc(v_config_1084_);
    leanh::lean_dec_ref(v_self_1077_);
    v_map_1085_ = leanh::lean_ctor_get(v_toFunctor_1079_, 0);
    leanh::lean_inc_n(v_map_1085_, 2);
    leanh::lean_dec_ref(v_toFunctor_1079_);
    v___f_1086_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1087_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1087_, 0, v_name_1083_);
    leanh::lean_closure_set(v___f_1087_, 1, v_config_1084_);
    leanh::lean_closure_set(v___f_1087_, 2, v_toPure_1081_);
    leanh::lean_closure_set(v___f_1087_, 3, v_pkg_1082_);
    leanh::lean_closure_set(v___f_1087_, 4, v_inst_1075_);
    v___f_1088_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1088_, 0, v_pkg_1082_);
    v___x_1089_ = leanh::lean_apply_4(
        v_map_1085_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1086_,
        v_inst_1076_,
    );
    v___x_1090_ = leanh::lean_apply_4(
        v_map_1085_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1088_,
        v___x_1089_,
    );
    v___x_1091_ = leanh::lean_apply_4(
        v_toBind_1080_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1090_,
        v___f_1087_,
    );
    return v___x_1091_;
}
pub unsafe fn l_Lake_KConfigDecl_get(
    mut v_m_1092_: *mut leanh::LeanObject,
    mut v_kind_1093_: *mut leanh::LeanObject,
    mut v_inst_1094_: *mut leanh::LeanObject,
    mut v_inst_1095_: *mut leanh::LeanObject,
    mut v_inst_1096_: *mut leanh::LeanObject,
    mut v_self_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = leanh::lean_ctor_get(v_inst_1094_, 0);
    leanh::lean_inc_ref(v_toApplicative_1098_);
    v_toFunctor_1099_ = leanh::lean_ctor_get(v_toApplicative_1098_, 0);
    leanh::lean_inc_ref(v_toFunctor_1099_);
    v_toBind_1100_ = leanh::lean_ctor_get(v_inst_1094_, 1);
    leanh::lean_inc(v_toBind_1100_);
    leanh::lean_dec_ref(v_inst_1094_);
    v_toPure_1101_ = leanh::lean_ctor_get(v_toApplicative_1098_, 1);
    leanh::lean_inc(v_toPure_1101_);
    leanh::lean_dec_ref(v_toApplicative_1098_);
    v_pkg_1102_ = leanh::lean_ctor_get(v_self_1097_, 0);
    leanh::lean_inc_n(v_pkg_1102_, 2);
    v_name_1103_ = leanh::lean_ctor_get(v_self_1097_, 1);
    leanh::lean_inc(v_name_1103_);
    v_config_1104_ = leanh::lean_ctor_get(v_self_1097_, 3);
    leanh::lean_inc(v_config_1104_);
    leanh::lean_dec_ref(v_self_1097_);
    v_map_1105_ = leanh::lean_ctor_get(v_toFunctor_1099_, 0);
    leanh::lean_inc_n(v_map_1105_, 2);
    leanh::lean_dec_ref(v_toFunctor_1099_);
    v___f_1106_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1107_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1107_, 0, v_name_1103_);
    leanh::lean_closure_set(v___f_1107_, 1, v_config_1104_);
    leanh::lean_closure_set(v___f_1107_, 2, v_toPure_1101_);
    leanh::lean_closure_set(v___f_1107_, 3, v_pkg_1102_);
    leanh::lean_closure_set(v___f_1107_, 4, v_inst_1095_);
    v___f_1108_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1108_, 0, v_pkg_1102_);
    v___x_1109_ = leanh::lean_apply_4(
        v_map_1105_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1106_,
        v_inst_1096_,
    );
    v___x_1110_ = leanh::lean_apply_4(
        v_map_1105_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1108_,
        v___x_1109_,
    );
    v___x_1111_ = leanh::lean_apply_4(
        v_toBind_1100_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1110_,
        v___f_1107_,
    );
    return v___x_1111_;
}
pub unsafe fn l_Lake_KConfigDecl_get___boxed(
    mut v_m_1112_: *mut leanh::LeanObject,
    mut v_kind_1113_: *mut leanh::LeanObject,
    mut v_inst_1114_: *mut leanh::LeanObject,
    mut v_inst_1115_: *mut leanh::LeanObject,
    mut v_inst_1116_: *mut leanh::LeanObject,
    mut v_self_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lake_KConfigDecl_get(
        v_m_1112_,
        v_kind_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_inst_1116_,
        v_self_1117_,
    );
    leanh::lean_dec(v_kind_1113_);
    return v_res_1118_;
}
pub unsafe fn l_Lake_Package_fetchTargetJob(
    mut v_self_1119_: *mut leanh::LeanObject,
    mut v_target_1120_: *mut leanh::LeanObject,
    mut v_a_1121_: *mut leanh::LeanObject,
    mut v_a_1122_: *mut leanh::LeanObject,
    mut v_a_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_a_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1128_, 0, v_self_1119_);
                leanh::lean_ctor_set(v___x_1128_, 1, v_target_1120_);
                leanh::lean_inc_ref(v_a_1125_);
                leanh::lean_inc(v_a_1124_);
                leanh::lean_inc(v_a_1123_);
                leanh::lean_inc(v_a_1122_);
                v___x_1129_ = leanh::lean_apply_7(
                    v_a_1121_,
                    v___x_1128_,
                    v_a_1122_,
                    v_a_1123_,
                    v_a_1124_,
                    v_a_1125_,
                    v_a_1126_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1129_) == 0 {
                    v_a_1130_ = leanh::lean_ctor_get(v___x_1129_, 0);
                    v_a_1131_ = leanh::lean_ctor_get(v___x_1129_, 1);
                    v_isSharedCheck_1139_ = (!leanh::lean_is_exclusive(v___x_1129_)) as u8;
                    if v_isSharedCheck_1139_ == 0 {
                        v___x_1133_ = v___x_1129_;
                        v_isShared_1134_ = v_isSharedCheck_1139_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1131_);
                        leanh::lean_inc(v_a_1130_);
                        leanh::lean_dec(v___x_1129_);
                        v___x_1133_ = leanh::lean_box(0);
                        v_isShared_1134_ = v_isSharedCheck_1139_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1129_;
                }
            }
            1 => {
                v___x_1135_ = l_Lake_Job_toOpaque___redArg(v_a_1130_);
                if v_isShared_1134_ == 0 {
                    leanh::lean_ctor_set(v___x_1133_, 0, v___x_1135_);
                    v___x_1137_ = v___x_1133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1131_);
                    v___x_1137_ = v_reuseFailAlloc_1138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_fetchTargetJob___boxed(
    mut v_self_1140_: *mut leanh::LeanObject,
    mut v_target_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
    mut v_a_1144_: *mut leanh::LeanObject,
    mut v_a_1145_: *mut leanh::LeanObject,
    mut v_a_1146_: *mut leanh::LeanObject,
    mut v_a_1147_: *mut leanh::LeanObject,
    mut v_a_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lake_Package_fetchTargetJob(
        v_self_1140_,
        v_target_1141_,
        v_a_1142_,
        v_a_1143_,
        v_a_1144_,
        v_a_1145_,
        v_a_1146_,
        v_a_1147_,
    );
    leanh::lean_dec_ref(v_a_1146_);
    leanh::lean_dec(v_a_1145_);
    leanh::lean_dec(v_a_1144_);
    leanh::lean_dec(v_a_1143_);
    return v_res_1149_;
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg(
    mut v_self_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
    mut v_a_1157_: *mut leanh::LeanObject,
    mut v_a_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toContext_1161_ = leanh::lean_ctor_get(v_a_1158_, 1);
    v_pkg_1162_ = leanh::lean_ctor_get(v_self_1153_, 0);
    leanh::lean_inc_n(v_pkg_1162_, 2);
    v_name_1163_ = leanh::lean_ctor_get(v_self_1153_, 1);
    leanh::lean_inc(v_name_1163_);
    leanh::lean_dec_ref(v_self_1153_);
    v_packageMap_1164_ = leanh::lean_ctor_get(v_toContext_1161_, 5);
    v___x_1165_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    leanh::lean_inc(v_packageMap_1164_);
    v___x_1166_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1165_, v_packageMap_1164_, v_pkg_1162_);
    if leanh::lean_obj_tag(v___x_1166_) == 1 {
        let mut v_val_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_pkg_1162_);
        v_val_1167_ = leanh::lean_ctor_get(v___x_1166_, 0);
        leanh::lean_inc(v_val_1167_);
        leanh::lean_dec_ref_known(v___x_1166_, 1);
        v___x_1168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1168_, 0, v_val_1167_);
        leanh::lean_ctor_set(v___x_1168_, 1, v_name_1163_);
        leanh::lean_inc_ref(v_a_1158_);
        leanh::lean_inc(v_a_1157_);
        leanh::lean_inc(v_a_1156_);
        leanh::lean_inc(v_a_1155_);
        v___x_1169_ = leanh::lean_apply_7(
            v_a_1154_,
            v___x_1168_,
            v_a_1155_,
            v_a_1156_,
            v_a_1157_,
            v_a_1158_,
            v_a_1159_,
            leanh::lean_box(0),
        );
        return v___x_1169_;
    } else {
        let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: u8 = 0;
        let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: u8 = 0;
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1166_);
        leanh::lean_dec_ref(v_a_1154_);
        v___x_1170_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
        v___x_1171_ = 1;
        v___x_1172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1162_,
            v___x_1171_,
        );
        v___x_1173_ = lean_string_append(v___x_1170_, v___x_1172_);
        leanh::lean_dec_ref(v___x_1172_);
        v___x_1174_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
        v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
        v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1163_,
            v___x_1171_,
        );
        v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
        leanh::lean_dec_ref(v___x_1176_);
        v___x_1178_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
        v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
        v___x_1180_ = 3;
        v___x_1181_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1181_, 0, v___x_1179_);
        leanh::lean_ctor_set_uint8(
            v___x_1181_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1180_,
        );
        v___x_1182_ = lean_array_get_size(v_a_1159_);
        v___x_1183_ = lean_array_push(v_a_1159_, v___x_1181_);
        v___x_1184_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1184_, 0, v___x_1182_);
        leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
        return v___x_1184_;
    }
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg___boxed(
    mut v_self_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_a_1188_: *mut leanh::LeanObject,
    mut v_a_1189_: *mut leanh::LeanObject,
    mut v_a_1190_: *mut leanh::LeanObject,
    mut v_a_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_TargetDecl_fetch___redArg(
        v_self_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
        v_a_1189_,
        v_a_1190_,
        v_a_1191_,
    );
    leanh::lean_dec_ref(v_a_1190_);
    leanh::lean_dec(v_a_1189_);
    leanh::lean_dec(v_a_1188_);
    leanh::lean_dec(v_a_1187_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_TargetDecl_fetch(
    mut v_00_u03b1_1194_: *mut leanh::LeanObject,
    mut v_self_1195_: *mut leanh::LeanObject,
    mut v_inst_1196_: *mut leanh::LeanObject,
    mut v_a_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lake_TargetDecl_fetch___redArg(
        v_self_1195_,
        v_a_1197_,
        v_a_1198_,
        v_a_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
    );
    return v___x_1204_;
}
pub unsafe fn l_Lake_TargetDecl_fetch___boxed(
    mut v_00_u03b1_1205_: *mut leanh::LeanObject,
    mut v_self_1206_: *mut leanh::LeanObject,
    mut v_inst_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
    mut v_a_1211_: *mut leanh::LeanObject,
    mut v_a_1212_: *mut leanh::LeanObject,
    mut v_a_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Lake_TargetDecl_fetch(
        v_00_u03b1_1205_,
        v_self_1206_,
        v_inst_1207_,
        v_a_1208_,
        v_a_1209_,
        v_a_1210_,
        v_a_1211_,
        v_a_1212_,
        v_a_1213_,
    );
    leanh::lean_dec_ref(v_a_1212_);
    leanh::lean_dec(v_a_1211_);
    leanh::lean_dec(v_a_1210_);
    leanh::lean_dec(v_a_1209_);
    return v_res_1215_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
    mut v_t_1216_: *mut leanh::LeanObject,
    mut v_k_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1216_) == 0 {
                    v_k_1218_ = leanh::lean_ctor_get(v_t_1216_, 1);
                    v_v_1219_ = leanh::lean_ctor_get(v_t_1216_, 2);
                    v_l_1220_ = leanh::lean_ctor_get(v_t_1216_, 3);
                    v_r_1221_ = leanh::lean_ctor_get(v_t_1216_, 4);
                    v___x_1222_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1217_, v_k_1218_);
                    match v___x_1222_ {
                        0 => {
                            v_t_1216_ = v_l_1220_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_1219_);
                            v___x_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1224_, 0, v_v_1219_);
                            return v___x_1224_;
                        }
                        _ => {
                            v_t_1216_ = v_r_1221_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1226_ = leanh::lean_box(0);
                    return v___x_1226_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(
    mut v_t_1227_: *mut leanh::LeanObject,
    mut v_k_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1227_, v_k_1228_,
        );
    leanh::lean_dec(v_k_1228_);
    leanh::lean_dec(v_t_1227_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_TargetDecl_fetchJob(
    mut v_self_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
    mut v_a_1233_: *mut leanh::LeanObject,
    mut v_a_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1238_ = leanh::lean_ctor_get(v_a_1235_, 1);
                v_pkg_1239_ = leanh::lean_ctor_get(v_self_1230_, 0);
                leanh::lean_inc(v_pkg_1239_);
                v_name_1240_ = leanh::lean_ctor_get(v_self_1230_, 1);
                leanh::lean_inc(v_name_1240_);
                leanh::lean_dec_ref(v_self_1230_);
                v_packageMap_1241_ = leanh::lean_ctor_get(v_toContext_1238_, 5);
                v___x_1242_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_packageMap_1241_, v_pkg_1239_);
                if leanh::lean_obj_tag(v___x_1242_) == 1 {
                    leanh::lean_dec(v_pkg_1239_);
                    v_val_1243_ = leanh::lean_ctor_get(v___x_1242_, 0);
                    leanh::lean_inc(v_val_1243_);
                    leanh::lean_dec_ref_known(v___x_1242_, 1);
                    v___x_1244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1244_, 0, v_val_1243_);
                    leanh::lean_ctor_set(v___x_1244_, 1, v_name_1240_);
                    leanh::lean_inc_ref(v_a_1235_);
                    leanh::lean_inc(v_a_1234_);
                    leanh::lean_inc(v_a_1233_);
                    leanh::lean_inc(v_a_1232_);
                    v___x_1245_ = leanh::lean_apply_7(
                        v_a_1231_,
                        v___x_1244_,
                        v_a_1232_,
                        v_a_1233_,
                        v_a_1234_,
                        v_a_1235_,
                        v_a_1236_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1245_) == 0 {
                        v_a_1246_ = leanh::lean_ctor_get(v___x_1245_, 0);
                        v_a_1247_ = leanh::lean_ctor_get(v___x_1245_, 1);
                        v_isSharedCheck_1255_ =
                            (!leanh::lean_is_exclusive(v___x_1245_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1249_ = v___x_1245_;
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1247_);
                            leanh::lean_inc(v_a_1246_);
                            leanh::lean_dec(v___x_1245_);
                            v___x_1249_ = leanh::lean_box(0);
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1245_;
                    }
                } else {
                    leanh::lean_dec(v___x_1242_);
                    leanh::lean_dec_ref(v_a_1231_);
                    v___x_1256_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
                    v___x_1257_ = 1;
                    v___x_1258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1239_,
                        v___x_1257_,
                    );
                    v___x_1259_ = lean_string_append(v___x_1256_, v___x_1258_);
                    leanh::lean_dec_ref(v___x_1258_);
                    v___x_1260_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
                    v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
                    v___x_1262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1240_,
                        v___x_1257_,
                    );
                    v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
                    leanh::lean_dec_ref(v___x_1262_);
                    v___x_1264_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
                    v___x_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
                    v___x_1266_ = 3;
                    v___x_1267_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1267_, 0, v___x_1265_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1267_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1266_,
                    );
                    v___x_1268_ = lean_array_get_size(v_a_1236_);
                    v___x_1269_ = lean_array_push(v_a_1236_, v___x_1267_);
                    v___x_1270_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1270_, 0, v___x_1268_);
                    leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
                    return v___x_1270_;
                }
            }
            1 => {
                v___x_1251_ = l_Lake_Job_toOpaque___redArg(v_a_1246_);
                if v_isShared_1250_ == 0 {
                    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1247_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_TargetDecl_fetchJob___boxed(
    mut v_self_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v_a_1273_: *mut leanh::LeanObject,
    mut v_a_1274_: *mut leanh::LeanObject,
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lake_TargetDecl_fetchJob(
        v_self_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
        v_a_1275_,
        v_a_1276_,
        v_a_1277_,
    );
    leanh::lean_dec_ref(v_a_1276_);
    leanh::lean_dec(v_a_1275_);
    leanh::lean_dec(v_a_1274_);
    leanh::lean_dec(v_a_1273_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
    mut v_00_u03b2_1280_: *mut leanh::LeanObject,
    mut v_inst_1281_: *mut leanh::LeanObject,
    mut v_t_1282_: *mut leanh::LeanObject,
    mut v_k_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1282_, v_k_1283_,
        );
    return v___x_1284_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(
    mut v_00_u03b2_1285_: *mut leanh::LeanObject,
    mut v_inst_1286_: *mut leanh::LeanObject,
    mut v_t_1287_: *mut leanh::LeanObject,
    mut v_k_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
        v_00_u03b2_1285_,
        v_inst_1286_,
        v_t_1287_,
        v_k_1288_,
    );
    leanh::lean_dec(v_k_1288_);
    leanh::lean_dec(v_t_1287_);
    return v_res_1289_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg(
    mut v_pkg_1290_: *mut leanh::LeanObject,
    mut v_self_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_a_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1299_ = leanh::lean_ctor_get(v_self_1291_, 0);
    v_keyName_1300_ = leanh::lean_ctor_get(v_pkg_1290_, 2);
    leanh::lean_inc(v_keyName_1300_);
    v___x_1301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1301_, 0, v_keyName_1300_);
    v___x_1302_ = l_Lake_Package_keyword;
    leanh::lean_inc(v_name_1299_);
    v___x_1303_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1303_, 0, v___x_1301_);
    leanh::lean_ctor_set(v___x_1303_, 1, v___x_1302_);
    leanh::lean_ctor_set(v___x_1303_, 2, v_pkg_1290_);
    leanh::lean_ctor_set(v___x_1303_, 3, v_name_1299_);
    leanh::lean_inc_ref(v_a_1296_);
    leanh::lean_inc(v_a_1295_);
    leanh::lean_inc(v_a_1294_);
    leanh::lean_inc(v_a_1293_);
    v___x_1304_ = leanh::lean_apply_7(
        v_a_1292_,
        v___x_1303_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        leanh::lean_box(0),
    );
    return v___x_1304_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg___boxed(
    mut v_pkg_1305_: *mut leanh::LeanObject,
    mut v_self_1306_: *mut leanh::LeanObject,
    mut v_a_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
    mut v_a_1310_: *mut leanh::LeanObject,
    mut v_a_1311_: *mut leanh::LeanObject,
    mut v_a_1312_: *mut leanh::LeanObject,
    mut v_a_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lake_PackageFacetDecl_fetch___redArg(
        v_pkg_1305_,
        v_self_1306_,
        v_a_1307_,
        v_a_1308_,
        v_a_1309_,
        v_a_1310_,
        v_a_1311_,
        v_a_1312_,
    );
    leanh::lean_dec_ref(v_a_1311_);
    leanh::lean_dec(v_a_1310_);
    leanh::lean_dec(v_a_1309_);
    leanh::lean_dec(v_a_1308_);
    leanh::lean_dec_ref(v_self_1306_);
    return v_res_1314_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch(
    mut v_00_u03b1_1315_: *mut leanh::LeanObject,
    mut v_pkg_1316_: *mut leanh::LeanObject,
    mut v_self_1317_: *mut leanh::LeanObject,
    mut v_inst_1318_: *mut leanh::LeanObject,
    mut v_a_1319_: *mut leanh::LeanObject,
    mut v_a_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
    mut v_a_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1326_ = leanh::lean_ctor_get(v_self_1317_, 0);
    v_keyName_1327_ = leanh::lean_ctor_get(v_pkg_1316_, 2);
    leanh::lean_inc(v_keyName_1327_);
    v___x_1328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1328_, 0, v_keyName_1327_);
    v___x_1329_ = l_Lake_Package_keyword;
    leanh::lean_inc(v_name_1326_);
    v___x_1330_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1330_, 0, v___x_1328_);
    leanh::lean_ctor_set(v___x_1330_, 1, v___x_1329_);
    leanh::lean_ctor_set(v___x_1330_, 2, v_pkg_1316_);
    leanh::lean_ctor_set(v___x_1330_, 3, v_name_1326_);
    leanh::lean_inc_ref(v_a_1323_);
    leanh::lean_inc(v_a_1322_);
    leanh::lean_inc(v_a_1321_);
    leanh::lean_inc(v_a_1320_);
    v___x_1331_ = leanh::lean_apply_7(
        v_a_1319_,
        v___x_1330_,
        v_a_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        leanh::lean_box(0),
    );
    return v___x_1331_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___boxed(
    mut v_00_u03b1_1332_: *mut leanh::LeanObject,
    mut v_pkg_1333_: *mut leanh::LeanObject,
    mut v_self_1334_: *mut leanh::LeanObject,
    mut v_inst_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_Lake_PackageFacetDecl_fetch(
        v_00_u03b1_1332_,
        v_pkg_1333_,
        v_self_1334_,
        v_inst_1335_,
        v_a_1336_,
        v_a_1337_,
        v_a_1338_,
        v_a_1339_,
        v_a_1340_,
        v_a_1341_,
    );
    leanh::lean_dec_ref(v_a_1340_);
    leanh::lean_dec(v_a_1339_);
    leanh::lean_dec(v_a_1338_);
    leanh::lean_dec(v_a_1337_);
    leanh::lean_dec_ref(v_self_1334_);
    return v_res_1343_;
}
pub unsafe fn l_Lake_Package_fetchFacetJob(
    mut v_name_1344_: *mut leanh::LeanObject,
    mut v_self_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
    mut v_a_1350_: *mut leanh::LeanObject,
    mut v_a_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keyName_1353_ = leanh::lean_ctor_get(v_self_1345_, 2);
                v___x_1354_ = l_Lake_Package_keyword;
                v___x_1355_ = l_Lean_Name_append(v___x_1354_, v_name_1344_);
                leanh::lean_inc(v_keyName_1353_);
                v___x_1356_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1356_, 0, v_keyName_1353_);
                v___x_1357_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                leanh::lean_ctor_set(v___x_1357_, 1, v___x_1354_);
                leanh::lean_ctor_set(v___x_1357_, 2, v_self_1345_);
                leanh::lean_ctor_set(v___x_1357_, 3, v___x_1355_);
                leanh::lean_inc_ref(v_a_1350_);
                leanh::lean_inc(v_a_1349_);
                leanh::lean_inc(v_a_1348_);
                leanh::lean_inc(v_a_1347_);
                v___x_1358_ = leanh::lean_apply_7(
                    v_a_1346_,
                    v___x_1357_,
                    v_a_1347_,
                    v_a_1348_,
                    v_a_1349_,
                    v_a_1350_,
                    v_a_1351_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1358_) == 0 {
                    v_a_1359_ = leanh::lean_ctor_get(v___x_1358_, 0);
                    v_a_1360_ = leanh::lean_ctor_get(v___x_1358_, 1);
                    v_isSharedCheck_1368_ = (!leanh::lean_is_exclusive(v___x_1358_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1362_ = v___x_1358_;
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1360_);
                        leanh::lean_inc(v_a_1359_);
                        leanh::lean_dec(v___x_1358_);
                        v___x_1362_ = leanh::lean_box(0);
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1358_;
                }
            }
            1 => {
                v___x_1364_ = l_Lake_Job_toOpaque___redArg(v_a_1359_);
                if v_isShared_1363_ == 0 {
                    leanh::lean_ctor_set(v___x_1362_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1360_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_fetchFacetJob___boxed(
    mut v_name_1369_: *mut leanh::LeanObject,
    mut v_self_1370_: *mut leanh::LeanObject,
    mut v_a_1371_: *mut leanh::LeanObject,
    mut v_a_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_a_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Lake_Package_fetchFacetJob(
        v_name_1369_,
        v_self_1370_,
        v_a_1371_,
        v_a_1372_,
        v_a_1373_,
        v_a_1374_,
        v_a_1375_,
        v_a_1376_,
    );
    leanh::lean_dec_ref(v_a_1375_);
    leanh::lean_dec(v_a_1374_);
    leanh::lean_dec(v_a_1373_);
    leanh::lean_dec(v_a_1372_);
    return v_res_1378_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg(
    mut v_mod_1379_: *mut leanh::LeanObject,
    mut v_self_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v_name_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_unused_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1388_ = leanh::lean_ctor_get(v_mod_1379_, 0);
                v_pkg_1389_ = leanh::lean_ctor_get(v_lib_1388_, 0);
                v_name_1390_ = leanh::lean_ctor_get(v_self_1380_, 0);
                v_isSharedCheck_1402_ = (!leanh::lean_is_exclusive(v_self_1380_)) as u8;
                if v_isSharedCheck_1402_ == 0 {
                    v_unused_1403_ = leanh::lean_ctor_get(v_self_1380_, 1);
                    leanh::lean_dec(v_unused_1403_);
                    v___x_1392_ = v_self_1380_;
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_1390_);
                    leanh::lean_dec(v_self_1380_);
                    v___x_1392_ = leanh::lean_box(0);
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1394_ = leanh::lean_ctor_get(v_mod_1379_, 1);
                v_keyName_1395_ = leanh::lean_ctor_get(v_pkg_1389_, 2);
                leanh::lean_inc(v_name_1394_);
                leanh::lean_inc(v_keyName_1395_);
                if v_isShared_1393_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1392_, 2);
                    leanh::lean_ctor_set(v___x_1392_, 1, v_name_1394_);
                    leanh::lean_ctor_set(v___x_1392_, 0, v_keyName_1395_);
                    v___x_1397_ = v___x_1392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1401_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_keyName_1395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_name_1394_);
                    v___x_1397_ = v_reuseFailAlloc_1401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1398_ = l_Lake_Module_keyword;
                v___x_1399_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1399_, 0, v___x_1397_);
                leanh::lean_ctor_set(v___x_1399_, 1, v___x_1398_);
                leanh::lean_ctor_set(v___x_1399_, 2, v_mod_1379_);
                leanh::lean_ctor_set(v___x_1399_, 3, v_name_1390_);
                leanh::lean_inc_ref(v_a_1385_);
                leanh::lean_inc(v_a_1384_);
                leanh::lean_inc(v_a_1383_);
                leanh::lean_inc(v_a_1382_);
                v___x_1400_ = leanh::lean_apply_7(
                    v_a_1381_,
                    v___x_1399_,
                    v_a_1382_,
                    v_a_1383_,
                    v_a_1384_,
                    v_a_1385_,
                    v_a_1386_,
                    leanh::lean_box(0),
                );
                return v___x_1400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg___boxed(
    mut v_mod_1404_: *mut leanh::LeanObject,
    mut v_self_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
    mut v_a_1410_: *mut leanh::LeanObject,
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Lake_ModuleFacetDecl_fetch___redArg(
        v_mod_1404_,
        v_self_1405_,
        v_a_1406_,
        v_a_1407_,
        v_a_1408_,
        v_a_1409_,
        v_a_1410_,
        v_a_1411_,
    );
    leanh::lean_dec_ref(v_a_1410_);
    leanh::lean_dec(v_a_1409_);
    leanh::lean_dec(v_a_1408_);
    leanh::lean_dec(v_a_1407_);
    return v_res_1413_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch(
    mut v_00_u03b1_1414_: *mut leanh::LeanObject,
    mut v_mod_1415_: *mut leanh::LeanObject,
    mut v_self_1416_: *mut leanh::LeanObject,
    mut v_inst_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_name_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1439_: u8 = 0;
    let mut v_unused_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1425_ = leanh::lean_ctor_get(v_mod_1415_, 0);
                v_pkg_1426_ = leanh::lean_ctor_get(v_lib_1425_, 0);
                v_name_1427_ = leanh::lean_ctor_get(v_self_1416_, 0);
                v_isSharedCheck_1439_ = (!leanh::lean_is_exclusive(v_self_1416_)) as u8;
                if v_isSharedCheck_1439_ == 0 {
                    v_unused_1440_ = leanh::lean_ctor_get(v_self_1416_, 1);
                    leanh::lean_dec(v_unused_1440_);
                    v___x_1429_ = v_self_1416_;
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_1427_);
                    leanh::lean_dec(v_self_1416_);
                    v___x_1429_ = leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1431_ = leanh::lean_ctor_get(v_mod_1415_, 1);
                v_keyName_1432_ = leanh::lean_ctor_get(v_pkg_1426_, 2);
                leanh::lean_inc(v_name_1431_);
                leanh::lean_inc(v_keyName_1432_);
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1429_, 2);
                    leanh::lean_ctor_set(v___x_1429_, 1, v_name_1431_);
                    leanh::lean_ctor_set(v___x_1429_, 0, v_keyName_1432_);
                    v___x_1434_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_keyName_1432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_name_1431_);
                    v___x_1434_ = v_reuseFailAlloc_1438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1435_ = l_Lake_Module_keyword;
                v___x_1436_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1436_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1436_, 1, v___x_1435_);
                leanh::lean_ctor_set(v___x_1436_, 2, v_mod_1415_);
                leanh::lean_ctor_set(v___x_1436_, 3, v_name_1427_);
                leanh::lean_inc_ref(v_a_1422_);
                leanh::lean_inc(v_a_1421_);
                leanh::lean_inc(v_a_1420_);
                leanh::lean_inc(v_a_1419_);
                v___x_1437_ = leanh::lean_apply_7(
                    v_a_1418_,
                    v___x_1436_,
                    v_a_1419_,
                    v_a_1420_,
                    v_a_1421_,
                    v_a_1422_,
                    v_a_1423_,
                    leanh::lean_box(0),
                );
                return v___x_1437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___boxed(
    mut v_00_u03b1_1441_: *mut leanh::LeanObject,
    mut v_mod_1442_: *mut leanh::LeanObject,
    mut v_self_1443_: *mut leanh::LeanObject,
    mut v_inst_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
    mut v_a_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_a_1448_: *mut leanh::LeanObject,
    mut v_a_1449_: *mut leanh::LeanObject,
    mut v_a_1450_: *mut leanh::LeanObject,
    mut v_a_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lake_ModuleFacetDecl_fetch(
        v_00_u03b1_1441_,
        v_mod_1442_,
        v_self_1443_,
        v_inst_1444_,
        v_a_1445_,
        v_a_1446_,
        v_a_1447_,
        v_a_1448_,
        v_a_1449_,
        v_a_1450_,
    );
    leanh::lean_dec_ref(v_a_1449_);
    leanh::lean_dec(v_a_1448_);
    leanh::lean_dec(v_a_1447_);
    leanh::lean_dec(v_a_1446_);
    return v_res_1452_;
}
pub unsafe fn l_Lake_Module_fetchFacetJob(
    mut v_name_1453_: *mut leanh::LeanObject,
    mut v_self_1454_: *mut leanh::LeanObject,
    mut v_a_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1462_ = leanh::lean_ctor_get(v_self_1454_, 0);
                v_pkg_1463_ = leanh::lean_ctor_get(v_lib_1462_, 0);
                v_name_1464_ = leanh::lean_ctor_get(v_self_1454_, 1);
                v_keyName_1465_ = leanh::lean_ctor_get(v_pkg_1463_, 2);
                v___x_1466_ = l_Lake_Module_keyword;
                v___x_1467_ = l_Lean_Name_append(v___x_1466_, v_name_1453_);
                leanh::lean_inc(v_name_1464_);
                leanh::lean_inc(v_keyName_1465_);
                v___x_1468_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1468_, 0, v_keyName_1465_);
                leanh::lean_ctor_set(v___x_1468_, 1, v_name_1464_);
                v___x_1469_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                leanh::lean_ctor_set(v___x_1469_, 1, v___x_1466_);
                leanh::lean_ctor_set(v___x_1469_, 2, v_self_1454_);
                leanh::lean_ctor_set(v___x_1469_, 3, v___x_1467_);
                leanh::lean_inc_ref(v_a_1459_);
                leanh::lean_inc(v_a_1458_);
                leanh::lean_inc(v_a_1457_);
                leanh::lean_inc(v_a_1456_);
                v___x_1470_ = leanh::lean_apply_7(
                    v_a_1455_,
                    v___x_1469_,
                    v_a_1456_,
                    v_a_1457_,
                    v_a_1458_,
                    v_a_1459_,
                    v_a_1460_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1470_) == 0 {
                    v_a_1471_ = leanh::lean_ctor_get(v___x_1470_, 0);
                    v_a_1472_ = leanh::lean_ctor_get(v___x_1470_, 1);
                    v_isSharedCheck_1480_ = (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                    if v_isSharedCheck_1480_ == 0 {
                        v___x_1474_ = v___x_1470_;
                        v_isShared_1475_ = v_isSharedCheck_1480_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1472_);
                        leanh::lean_inc(v_a_1471_);
                        leanh::lean_dec(v___x_1470_);
                        v___x_1474_ = leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1480_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1470_;
                }
            }
            1 => {
                v___x_1476_ = l_Lake_Job_toOpaque___redArg(v_a_1471_);
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1472_);
                    v___x_1478_ = v_reuseFailAlloc_1479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Module_fetchFacetJob___boxed(
    mut v_name_1481_: *mut leanh::LeanObject,
    mut v_self_1482_: *mut leanh::LeanObject,
    mut v_a_1483_: *mut leanh::LeanObject,
    mut v_a_1484_: *mut leanh::LeanObject,
    mut v_a_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
    mut v_a_1487_: *mut leanh::LeanObject,
    mut v_a_1488_: *mut leanh::LeanObject,
    mut v_a_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1490_ = l_Lake_Module_fetchFacetJob(
        v_name_1481_,
        v_self_1482_,
        v_a_1483_,
        v_a_1484_,
        v_a_1485_,
        v_a_1486_,
        v_a_1487_,
        v_a_1488_,
    );
    leanh::lean_dec_ref(v_a_1487_);
    leanh::lean_dec(v_a_1486_);
    leanh::lean_dec(v_a_1485_);
    leanh::lean_dec(v_a_1484_);
    return v_res_1490_;
}
pub unsafe fn l_Lake_LeanLibDecl_get___redArg(
    mut v_self_1491_: *mut leanh::LeanObject,
    mut v_inst_1492_: *mut leanh::LeanObject,
    mut v_inst_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1495_ = leanh::lean_ctor_get(v_inst_1492_, 0);
    leanh::lean_inc_ref(v_toApplicative_1495_);
    v_toFunctor_1496_ = leanh::lean_ctor_get(v_toApplicative_1495_, 0);
    leanh::lean_inc_ref(v_toFunctor_1496_);
    v_toBind_1497_ = leanh::lean_ctor_get(v_inst_1492_, 1);
    leanh::lean_inc(v_toBind_1497_);
    leanh::lean_dec_ref(v_inst_1492_);
    v_toPure_1498_ = leanh::lean_ctor_get(v_toApplicative_1495_, 1);
    leanh::lean_inc(v_toPure_1498_);
    leanh::lean_dec_ref(v_toApplicative_1495_);
    v_pkg_1499_ = leanh::lean_ctor_get(v_self_1491_, 0);
    leanh::lean_inc_n(v_pkg_1499_, 2);
    v_name_1500_ = leanh::lean_ctor_get(v_self_1491_, 1);
    leanh::lean_inc(v_name_1500_);
    v_config_1501_ = leanh::lean_ctor_get(v_self_1491_, 3);
    leanh::lean_inc(v_config_1501_);
    leanh::lean_dec_ref(v_self_1491_);
    v_map_1502_ = leanh::lean_ctor_get(v_toFunctor_1496_, 0);
    leanh::lean_inc_n(v_map_1502_, 2);
    leanh::lean_dec_ref(v_toFunctor_1496_);
    v___f_1503_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1504_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1504_, 0, v_name_1500_);
    leanh::lean_closure_set(v___f_1504_, 1, v_config_1501_);
    leanh::lean_closure_set(v___f_1504_, 2, v_toPure_1498_);
    leanh::lean_closure_set(v___f_1504_, 3, v_pkg_1499_);
    leanh::lean_closure_set(v___f_1504_, 4, v_inst_1493_);
    v___f_1505_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1505_, 0, v_pkg_1499_);
    v___x_1506_ = leanh::lean_apply_4(
        v_map_1502_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1503_,
        v_inst_1494_,
    );
    v___x_1507_ = leanh::lean_apply_4(
        v_map_1502_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1505_,
        v___x_1506_,
    );
    v___x_1508_ = leanh::lean_apply_4(
        v_toBind_1497_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1507_,
        v___f_1504_,
    );
    return v___x_1508_;
}
pub unsafe fn l_Lake_LeanLibDecl_get(
    mut v_m_1509_: *mut leanh::LeanObject,
    mut v_self_1510_: *mut leanh::LeanObject,
    mut v_inst_1511_: *mut leanh::LeanObject,
    mut v_inst_1512_: *mut leanh::LeanObject,
    mut v_inst_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1514_ = leanh::lean_ctor_get(v_inst_1511_, 0);
    leanh::lean_inc_ref(v_toApplicative_1514_);
    v_toFunctor_1515_ = leanh::lean_ctor_get(v_toApplicative_1514_, 0);
    leanh::lean_inc_ref(v_toFunctor_1515_);
    v_toBind_1516_ = leanh::lean_ctor_get(v_inst_1511_, 1);
    leanh::lean_inc(v_toBind_1516_);
    leanh::lean_dec_ref(v_inst_1511_);
    v_toPure_1517_ = leanh::lean_ctor_get(v_toApplicative_1514_, 1);
    leanh::lean_inc(v_toPure_1517_);
    leanh::lean_dec_ref(v_toApplicative_1514_);
    v_pkg_1518_ = leanh::lean_ctor_get(v_self_1510_, 0);
    leanh::lean_inc_n(v_pkg_1518_, 2);
    v_name_1519_ = leanh::lean_ctor_get(v_self_1510_, 1);
    leanh::lean_inc(v_name_1519_);
    v_config_1520_ = leanh::lean_ctor_get(v_self_1510_, 3);
    leanh::lean_inc(v_config_1520_);
    leanh::lean_dec_ref(v_self_1510_);
    v_map_1521_ = leanh::lean_ctor_get(v_toFunctor_1515_, 0);
    leanh::lean_inc_n(v_map_1521_, 2);
    leanh::lean_dec_ref(v_toFunctor_1515_);
    v___f_1522_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1523_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1523_, 0, v_name_1519_);
    leanh::lean_closure_set(v___f_1523_, 1, v_config_1520_);
    leanh::lean_closure_set(v___f_1523_, 2, v_toPure_1517_);
    leanh::lean_closure_set(v___f_1523_, 3, v_pkg_1518_);
    leanh::lean_closure_set(v___f_1523_, 4, v_inst_1512_);
    v___f_1524_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1524_, 0, v_pkg_1518_);
    v___x_1525_ = leanh::lean_apply_4(
        v_map_1521_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1522_,
        v_inst_1513_,
    );
    v___x_1526_ = leanh::lean_apply_4(
        v_map_1521_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1524_,
        v___x_1525_,
    );
    v___x_1527_ = leanh::lean_apply_4(
        v_toBind_1516_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1526_,
        v___f_1523_,
    );
    return v___x_1527_;
}
pub unsafe fn l_Lake_LeanLib_fetch(
    mut v_self_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
    mut v_a_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1539_ = leanh::lean_ctor_get(v_self_1531_, 0);
    v_name_1540_ = leanh::lean_ctor_get(v_self_1531_, 1);
    v_keyName_1541_ = leanh::lean_ctor_get(v_pkg_1539_, 2);
    v___x_1542_ = l_Lake_LeanLib_defaultFacet;
    leanh::lean_inc(v_name_1540_);
    leanh::lean_inc(v_keyName_1541_);
    v___x_1543_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1543_, 0, v_keyName_1541_);
    leanh::lean_ctor_set(v___x_1543_, 1, v_name_1540_);
    v___x_1544_ = l_Lake_LeanLib_fetch___closed__1;
    v___x_1545_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
    leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    leanh::lean_ctor_set(v___x_1545_, 2, v_self_1531_);
    leanh::lean_ctor_set(v___x_1545_, 3, v___x_1542_);
    leanh::lean_inc_ref(v_a_1536_);
    leanh::lean_inc(v_a_1535_);
    leanh::lean_inc(v_a_1534_);
    leanh::lean_inc(v_a_1533_);
    v___x_1546_ = leanh::lean_apply_7(
        v_a_1532_,
        v___x_1545_,
        v_a_1533_,
        v_a_1534_,
        v_a_1535_,
        v_a_1536_,
        v_a_1537_,
        leanh::lean_box(0),
    );
    return v___x_1546_;
}
pub unsafe fn l_Lake_LeanLib_fetch___boxed(
    mut v_self_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
    mut v_a_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Lake_LeanLib_fetch(
        v_self_1547_,
        v_a_1548_,
        v_a_1549_,
        v_a_1550_,
        v_a_1551_,
        v_a_1552_,
        v_a_1553_,
    );
    leanh::lean_dec_ref(v_a_1552_);
    leanh::lean_dec(v_a_1551_);
    leanh::lean_dec(v_a_1550_);
    leanh::lean_dec(v_a_1549_);
    return v_res_1555_;
}
pub unsafe fn l_Lake_LeanLibDecl_fetch(
    mut v_self_1556_: *mut leanh::LeanObject,
    mut v_a_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_a_1559_: *mut leanh::LeanObject,
    mut v_a_1560_: *mut leanh::LeanObject,
    mut v_a_1561_: *mut leanh::LeanObject,
    mut v_a_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_packageMap_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_unused_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1564_ = leanh::lean_ctor_get(v_a_1561_, 1);
                v_pkg_1565_ = leanh::lean_ctor_get(v_self_1556_, 0);
                v_name_1566_ = leanh::lean_ctor_get(v_self_1556_, 1);
                v_config_1567_ = leanh::lean_ctor_get(v_self_1556_, 3);
                v_isSharedCheck_1599_ = (!leanh::lean_is_exclusive(v_self_1556_)) as u8;
                if v_isSharedCheck_1599_ == 0 {
                    v_unused_1600_ = leanh::lean_ctor_get(v_self_1556_, 2);
                    leanh::lean_dec(v_unused_1600_);
                    v___x_1569_ = v_self_1556_;
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_config_1567_);
                    leanh::lean_inc(v_name_1566_);
                    leanh::lean_inc(v_pkg_1565_);
                    leanh::lean_dec(v_self_1556_);
                    v___x_1569_ = leanh::lean_box(0);
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1571_ = leanh::lean_ctor_get(v_toContext_1564_, 5);
                v___x_1572_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                leanh::lean_inc(v_pkg_1565_);
                leanh::lean_inc(v_packageMap_1571_);
                v___x_1573_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1572_,
                    v_packageMap_1571_,
                    v_pkg_1565_,
                );
                if leanh::lean_obj_tag(v___x_1573_) == 1 {
                    leanh::lean_dec(v_pkg_1565_);
                    v_val_1574_ = leanh::lean_ctor_get(v___x_1573_, 0);
                    leanh::lean_inc(v_val_1574_);
                    leanh::lean_dec_ref_known(v___x_1573_, 1);
                    v_keyName_1575_ = leanh::lean_ctor_get(v_val_1574_, 2);
                    leanh::lean_inc(v_keyName_1575_);
                    v___x_1576_ = l_Lake_LeanLib_fetch___closed__1;
                    leanh::lean_inc(v_name_1566_);
                    v___x_1577_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1577_, 0, v_val_1574_);
                    leanh::lean_ctor_set(v___x_1577_, 1, v_name_1566_);
                    leanh::lean_ctor_set(v___x_1577_, 2, v_config_1567_);
                    v___x_1578_ = l_Lake_LeanLib_defaultFacet;
                    v___x_1579_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1579_, 0, v_keyName_1575_);
                    leanh::lean_ctor_set(v___x_1579_, 1, v_name_1566_);
                    if v_isShared_1570_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1569_, 1);
                        leanh::lean_ctor_set(v___x_1569_, 3, v___x_1578_);
                        leanh::lean_ctor_set(v___x_1569_, 2, v___x_1577_);
                        leanh::lean_ctor_set(v___x_1569_, 1, v___x_1576_);
                        leanh::lean_ctor_set(v___x_1569_, 0, v___x_1579_);
                        v___x_1581_ = v___x_1569_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1583_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1576_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 2, v___x_1577_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1578_);
                        v___x_1581_ = v_reuseFailAlloc_1583_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1573_);
                    leanh::lean_del_object(v___x_1569_);
                    leanh::lean_dec(v_config_1567_);
                    leanh::lean_dec_ref(v_a_1557_);
                    v___x_1584_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1585_ = 1;
                    v___x_1586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1565_,
                        v___x_1585_,
                    );
                    v___x_1587_ = lean_string_append(v___x_1584_, v___x_1586_);
                    leanh::lean_dec_ref(v___x_1586_);
                    v___x_1588_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
                    v___x_1590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1566_,
                        v___x_1585_,
                    );
                    v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
                    leanh::lean_dec_ref(v___x_1590_);
                    v___x_1592_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
                    v___x_1594_ = 3;
                    v___x_1595_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1595_, 0, v___x_1593_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1595_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1594_,
                    );
                    v___x_1596_ = lean_array_get_size(v_a_1562_);
                    v___x_1597_ = lean_array_push(v_a_1562_, v___x_1595_);
                    v___x_1598_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1598_, 0, v___x_1596_);
                    leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                    return v___x_1598_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_a_1561_);
                leanh::lean_inc(v_a_1560_);
                leanh::lean_inc(v_a_1559_);
                leanh::lean_inc(v_a_1558_);
                v___x_1582_ = leanh::lean_apply_7(
                    v_a_1557_,
                    v___x_1581_,
                    v_a_1558_,
                    v_a_1559_,
                    v_a_1560_,
                    v_a_1561_,
                    v_a_1562_,
                    leanh::lean_box(0),
                );
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibDecl_fetch___boxed(
    mut v_self_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
    mut v_a_1605_: *mut leanh::LeanObject,
    mut v_a_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lake_LeanLibDecl_fetch(
        v_self_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
    );
    leanh::lean_dec_ref(v_a_1606_);
    leanh::lean_dec(v_a_1605_);
    leanh::lean_dec(v_a_1604_);
    leanh::lean_dec(v_a_1603_);
    return v_res_1609_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg(
    mut v_lib_1610_: *mut leanh::LeanObject,
    mut v_self_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
    mut v_a_1614_: *mut leanh::LeanObject,
    mut v_a_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_a_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_name_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1619_ = leanh::lean_ctor_get(v_lib_1610_, 0);
                v_name_1620_ = leanh::lean_ctor_get(v_self_1611_, 0);
                v_isSharedCheck_1632_ = (!leanh::lean_is_exclusive(v_self_1611_)) as u8;
                if v_isSharedCheck_1632_ == 0 {
                    v_unused_1633_ = leanh::lean_ctor_get(v_self_1611_, 1);
                    leanh::lean_dec(v_unused_1633_);
                    v___x_1622_ = v_self_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_1620_);
                    leanh::lean_dec(v_self_1611_);
                    v___x_1622_ = leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1624_ = leanh::lean_ctor_get(v_lib_1610_, 1);
                v_keyName_1625_ = leanh::lean_ctor_get(v_pkg_1619_, 2);
                leanh::lean_inc(v_name_1624_);
                leanh::lean_inc(v_keyName_1625_);
                if v_isShared_1623_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1622_, 3);
                    leanh::lean_ctor_set(v___x_1622_, 1, v_name_1624_);
                    leanh::lean_ctor_set(v___x_1622_, 0, v_keyName_1625_);
                    v___x_1627_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_keyName_1625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_name_1624_);
                    v___x_1627_ = v_reuseFailAlloc_1631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1629_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1629_, 0, v___x_1627_);
                leanh::lean_ctor_set(v___x_1629_, 1, v___x_1628_);
                leanh::lean_ctor_set(v___x_1629_, 2, v_lib_1610_);
                leanh::lean_ctor_set(v___x_1629_, 3, v_name_1620_);
                leanh::lean_inc_ref(v_a_1616_);
                leanh::lean_inc(v_a_1615_);
                leanh::lean_inc(v_a_1614_);
                leanh::lean_inc(v_a_1613_);
                v___x_1630_ = leanh::lean_apply_7(
                    v_a_1612_,
                    v___x_1629_,
                    v_a_1613_,
                    v_a_1614_,
                    v_a_1615_,
                    v_a_1616_,
                    v_a_1617_,
                    leanh::lean_box(0),
                );
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg___boxed(
    mut v_lib_1634_: *mut leanh::LeanObject,
    mut v_self_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
    mut v_a_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
    mut v_a_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Lake_LibraryFacetDecl_fetch___redArg(
        v_lib_1634_,
        v_self_1635_,
        v_a_1636_,
        v_a_1637_,
        v_a_1638_,
        v_a_1639_,
        v_a_1640_,
        v_a_1641_,
    );
    leanh::lean_dec_ref(v_a_1640_);
    leanh::lean_dec(v_a_1639_);
    leanh::lean_dec(v_a_1638_);
    leanh::lean_dec(v_a_1637_);
    return v_res_1643_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch(
    mut v_00_u03b1_1644_: *mut leanh::LeanObject,
    mut v_lib_1645_: *mut leanh::LeanObject,
    mut v_self_1646_: *mut leanh::LeanObject,
    mut v_inst_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v_name_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1655_ = leanh::lean_ctor_get(v_lib_1645_, 0);
                v_name_1656_ = leanh::lean_ctor_get(v_self_1646_, 0);
                v_isSharedCheck_1668_ = (!leanh::lean_is_exclusive(v_self_1646_)) as u8;
                if v_isSharedCheck_1668_ == 0 {
                    v_unused_1669_ = leanh::lean_ctor_get(v_self_1646_, 1);
                    leanh::lean_dec(v_unused_1669_);
                    v___x_1658_ = v_self_1646_;
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_1656_);
                    leanh::lean_dec(v_self_1646_);
                    v___x_1658_ = leanh::lean_box(0);
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1660_ = leanh::lean_ctor_get(v_lib_1645_, 1);
                v_keyName_1661_ = leanh::lean_ctor_get(v_pkg_1655_, 2);
                leanh::lean_inc(v_name_1660_);
                leanh::lean_inc(v_keyName_1661_);
                if v_isShared_1659_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1658_, 3);
                    leanh::lean_ctor_set(v___x_1658_, 1, v_name_1660_);
                    leanh::lean_ctor_set(v___x_1658_, 0, v_keyName_1661_);
                    v___x_1663_ = v___x_1658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_keyName_1661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_name_1660_);
                    v___x_1663_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1664_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1665_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1665_, 0, v___x_1663_);
                leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                leanh::lean_ctor_set(v___x_1665_, 2, v_lib_1645_);
                leanh::lean_ctor_set(v___x_1665_, 3, v_name_1656_);
                leanh::lean_inc_ref(v_a_1652_);
                leanh::lean_inc(v_a_1651_);
                leanh::lean_inc(v_a_1650_);
                leanh::lean_inc(v_a_1649_);
                v___x_1666_ = leanh::lean_apply_7(
                    v_a_1648_,
                    v___x_1665_,
                    v_a_1649_,
                    v_a_1650_,
                    v_a_1651_,
                    v_a_1652_,
                    v_a_1653_,
                    leanh::lean_box(0),
                );
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___boxed(
    mut v_00_u03b1_1670_: *mut leanh::LeanObject,
    mut v_lib_1671_: *mut leanh::LeanObject,
    mut v_self_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_a_1674_: *mut leanh::LeanObject,
    mut v_a_1675_: *mut leanh::LeanObject,
    mut v_a_1676_: *mut leanh::LeanObject,
    mut v_a_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
    mut v_a_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1681_ = l_Lake_LibraryFacetDecl_fetch(
        v_00_u03b1_1670_,
        v_lib_1671_,
        v_self_1672_,
        v_inst_1673_,
        v_a_1674_,
        v_a_1675_,
        v_a_1676_,
        v_a_1677_,
        v_a_1678_,
        v_a_1679_,
    );
    leanh::lean_dec_ref(v_a_1678_);
    leanh::lean_dec(v_a_1677_);
    leanh::lean_dec(v_a_1676_);
    leanh::lean_dec(v_a_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Lake_LeanLib_fetchFacetJob(
    mut v_name_1682_: *mut leanh::LeanObject,
    mut v_self_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_a_1685_: *mut leanh::LeanObject,
    mut v_a_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1691_ = leanh::lean_ctor_get(v_self_1683_, 0);
                v_name_1692_ = leanh::lean_ctor_get(v_self_1683_, 1);
                v_keyName_1693_ = leanh::lean_ctor_get(v_pkg_1691_, 2);
                v___x_1694_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1695_ = l_Lean_Name_append(v___x_1694_, v_name_1682_);
                leanh::lean_inc(v_name_1692_);
                leanh::lean_inc(v_keyName_1693_);
                v___x_1696_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1696_, 0, v_keyName_1693_);
                leanh::lean_ctor_set(v___x_1696_, 1, v_name_1692_);
                v___x_1697_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                leanh::lean_ctor_set(v___x_1697_, 1, v___x_1694_);
                leanh::lean_ctor_set(v___x_1697_, 2, v_self_1683_);
                leanh::lean_ctor_set(v___x_1697_, 3, v___x_1695_);
                leanh::lean_inc_ref(v_a_1688_);
                leanh::lean_inc(v_a_1687_);
                leanh::lean_inc(v_a_1686_);
                leanh::lean_inc(v_a_1685_);
                v___x_1698_ = leanh::lean_apply_7(
                    v_a_1684_,
                    v___x_1697_,
                    v_a_1685_,
                    v_a_1686_,
                    v_a_1687_,
                    v_a_1688_,
                    v_a_1689_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1698_) == 0 {
                    v_a_1699_ = leanh::lean_ctor_get(v___x_1698_, 0);
                    v_a_1700_ = leanh::lean_ctor_get(v___x_1698_, 1);
                    v_isSharedCheck_1708_ = (!leanh::lean_is_exclusive(v___x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v___x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1700_);
                        leanh::lean_inc(v_a_1699_);
                        leanh::lean_dec(v___x_1698_);
                        v___x_1702_ = leanh::lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1698_;
                }
            }
            1 => {
                v___x_1704_ = l_Lake_Job_toOpaque___redArg(v_a_1699_);
                if v_isShared_1703_ == 0 {
                    leanh::lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_fetchFacetJob___boxed(
    mut v_name_1709_: *mut leanh::LeanObject,
    mut v_self_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
    mut v_a_1714_: *mut leanh::LeanObject,
    mut v_a_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1718_ = l_Lake_LeanLib_fetchFacetJob(
        v_name_1709_,
        v_self_1710_,
        v_a_1711_,
        v_a_1712_,
        v_a_1713_,
        v_a_1714_,
        v_a_1715_,
        v_a_1716_,
    );
    leanh::lean_dec_ref(v_a_1715_);
    leanh::lean_dec(v_a_1714_);
    leanh::lean_dec(v_a_1713_);
    leanh::lean_dec(v_a_1712_);
    return v_res_1718_;
}
pub unsafe fn l_Lake_LeanExeDecl_get___redArg(
    mut v_self_1719_: *mut leanh::LeanObject,
    mut v_inst_1720_: *mut leanh::LeanObject,
    mut v_inst_1721_: *mut leanh::LeanObject,
    mut v_inst_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1723_ = leanh::lean_ctor_get(v_inst_1720_, 0);
    leanh::lean_inc_ref(v_toApplicative_1723_);
    v_toFunctor_1724_ = leanh::lean_ctor_get(v_toApplicative_1723_, 0);
    leanh::lean_inc_ref(v_toFunctor_1724_);
    v_toBind_1725_ = leanh::lean_ctor_get(v_inst_1720_, 1);
    leanh::lean_inc(v_toBind_1725_);
    leanh::lean_dec_ref(v_inst_1720_);
    v_toPure_1726_ = leanh::lean_ctor_get(v_toApplicative_1723_, 1);
    leanh::lean_inc(v_toPure_1726_);
    leanh::lean_dec_ref(v_toApplicative_1723_);
    v_pkg_1727_ = leanh::lean_ctor_get(v_self_1719_, 0);
    leanh::lean_inc_n(v_pkg_1727_, 2);
    v_name_1728_ = leanh::lean_ctor_get(v_self_1719_, 1);
    leanh::lean_inc(v_name_1728_);
    v_config_1729_ = leanh::lean_ctor_get(v_self_1719_, 3);
    leanh::lean_inc(v_config_1729_);
    leanh::lean_dec_ref(v_self_1719_);
    v_map_1730_ = leanh::lean_ctor_get(v_toFunctor_1724_, 0);
    leanh::lean_inc_n(v_map_1730_, 2);
    leanh::lean_dec_ref(v_toFunctor_1724_);
    v___f_1731_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1732_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1732_, 0, v_name_1728_);
    leanh::lean_closure_set(v___f_1732_, 1, v_config_1729_);
    leanh::lean_closure_set(v___f_1732_, 2, v_toPure_1726_);
    leanh::lean_closure_set(v___f_1732_, 3, v_pkg_1727_);
    leanh::lean_closure_set(v___f_1732_, 4, v_inst_1721_);
    v___f_1733_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1733_, 0, v_pkg_1727_);
    v___x_1734_ = leanh::lean_apply_4(
        v_map_1730_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1731_,
        v_inst_1722_,
    );
    v___x_1735_ = leanh::lean_apply_4(
        v_map_1730_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1733_,
        v___x_1734_,
    );
    v___x_1736_ = leanh::lean_apply_4(
        v_toBind_1725_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1735_,
        v___f_1732_,
    );
    return v___x_1736_;
}
pub unsafe fn l_Lake_LeanExeDecl_get(
    mut v_m_1737_: *mut leanh::LeanObject,
    mut v_self_1738_: *mut leanh::LeanObject,
    mut v_inst_1739_: *mut leanh::LeanObject,
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_inst_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1742_ = leanh::lean_ctor_get(v_inst_1739_, 0);
    leanh::lean_inc_ref(v_toApplicative_1742_);
    v_toFunctor_1743_ = leanh::lean_ctor_get(v_toApplicative_1742_, 0);
    leanh::lean_inc_ref(v_toFunctor_1743_);
    v_toBind_1744_ = leanh::lean_ctor_get(v_inst_1739_, 1);
    leanh::lean_inc(v_toBind_1744_);
    leanh::lean_dec_ref(v_inst_1739_);
    v_toPure_1745_ = leanh::lean_ctor_get(v_toApplicative_1742_, 1);
    leanh::lean_inc(v_toPure_1745_);
    leanh::lean_dec_ref(v_toApplicative_1742_);
    v_pkg_1746_ = leanh::lean_ctor_get(v_self_1738_, 0);
    leanh::lean_inc_n(v_pkg_1746_, 2);
    v_name_1747_ = leanh::lean_ctor_get(v_self_1738_, 1);
    leanh::lean_inc(v_name_1747_);
    v_config_1748_ = leanh::lean_ctor_get(v_self_1738_, 3);
    leanh::lean_inc(v_config_1748_);
    leanh::lean_dec_ref(v_self_1738_);
    v_map_1749_ = leanh::lean_ctor_get(v_toFunctor_1743_, 0);
    leanh::lean_inc_n(v_map_1749_, 2);
    leanh::lean_dec_ref(v_toFunctor_1743_);
    v___f_1750_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1751_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1751_, 0, v_name_1747_);
    leanh::lean_closure_set(v___f_1751_, 1, v_config_1748_);
    leanh::lean_closure_set(v___f_1751_, 2, v_toPure_1745_);
    leanh::lean_closure_set(v___f_1751_, 3, v_pkg_1746_);
    leanh::lean_closure_set(v___f_1751_, 4, v_inst_1740_);
    v___f_1752_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1752_, 0, v_pkg_1746_);
    v___x_1753_ = leanh::lean_apply_4(
        v_map_1749_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1750_,
        v_inst_1741_,
    );
    v___x_1754_ = leanh::lean_apply_4(
        v_map_1749_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1752_,
        v___x_1753_,
    );
    v___x_1755_ = leanh::lean_apply_4(
        v_toBind_1744_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1754_,
        v___f_1751_,
    );
    return v___x_1755_;
}
pub unsafe fn l_Lake_LeanExe_fetch(
    mut v_self_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
    mut v_a_1759_: *mut leanh::LeanObject,
    mut v_a_1760_: *mut leanh::LeanObject,
    mut v_a_1761_: *mut leanh::LeanObject,
    mut v_a_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1764_ = leanh::lean_ctor_get(v_self_1756_, 0);
    v_name_1765_ = leanh::lean_ctor_get(v_self_1756_, 1);
    v_keyName_1766_ = leanh::lean_ctor_get(v_pkg_1764_, 2);
    v___x_1767_ = l_Lake_LeanExe_exeFacet;
    leanh::lean_inc(v_name_1765_);
    leanh::lean_inc(v_keyName_1766_);
    v___x_1768_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1768_, 0, v_keyName_1766_);
    leanh::lean_ctor_set(v___x_1768_, 1, v_name_1765_);
    v___x_1769_ = l_Lake_LeanExe_keyword;
    v___x_1770_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1770_, 0, v___x_1768_);
    leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
    leanh::lean_ctor_set(v___x_1770_, 2, v_self_1756_);
    leanh::lean_ctor_set(v___x_1770_, 3, v___x_1767_);
    leanh::lean_inc_ref(v_a_1761_);
    leanh::lean_inc(v_a_1760_);
    leanh::lean_inc(v_a_1759_);
    leanh::lean_inc(v_a_1758_);
    v___x_1771_ = leanh::lean_apply_7(
        v_a_1757_,
        v___x_1770_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
        v_a_1761_,
        v_a_1762_,
        leanh::lean_box(0),
    );
    return v___x_1771_;
}
pub unsafe fn l_Lake_LeanExe_fetch___boxed(
    mut v_self_1772_: *mut leanh::LeanObject,
    mut v_a_1773_: *mut leanh::LeanObject,
    mut v_a_1774_: *mut leanh::LeanObject,
    mut v_a_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1780_ = l_Lake_LeanExe_fetch(
        v_self_1772_,
        v_a_1773_,
        v_a_1774_,
        v_a_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
    );
    leanh::lean_dec_ref(v_a_1777_);
    leanh::lean_dec(v_a_1776_);
    leanh::lean_dec(v_a_1775_);
    leanh::lean_dec(v_a_1774_);
    return v_res_1780_;
}
pub unsafe fn l_Lake_LeanExeDecl_fetch(
    mut v_self_1781_: *mut leanh::LeanObject,
    mut v_a_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
    mut v_a_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v_packageMap_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut v_unused_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1789_ = leanh::lean_ctor_get(v_a_1786_, 1);
                v_pkg_1790_ = leanh::lean_ctor_get(v_self_1781_, 0);
                v_name_1791_ = leanh::lean_ctor_get(v_self_1781_, 1);
                v_config_1792_ = leanh::lean_ctor_get(v_self_1781_, 3);
                v_isSharedCheck_1824_ = (!leanh::lean_is_exclusive(v_self_1781_)) as u8;
                if v_isSharedCheck_1824_ == 0 {
                    v_unused_1825_ = leanh::lean_ctor_get(v_self_1781_, 2);
                    leanh::lean_dec(v_unused_1825_);
                    v___x_1794_ = v_self_1781_;
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_config_1792_);
                    leanh::lean_inc(v_name_1791_);
                    leanh::lean_inc(v_pkg_1790_);
                    leanh::lean_dec(v_self_1781_);
                    v___x_1794_ = leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1796_ = leanh::lean_ctor_get(v_toContext_1789_, 5);
                v___x_1797_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                leanh::lean_inc(v_pkg_1790_);
                leanh::lean_inc(v_packageMap_1796_);
                v___x_1798_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1797_,
                    v_packageMap_1796_,
                    v_pkg_1790_,
                );
                if leanh::lean_obj_tag(v___x_1798_) == 1 {
                    leanh::lean_dec(v_pkg_1790_);
                    v_val_1799_ = leanh::lean_ctor_get(v___x_1798_, 0);
                    leanh::lean_inc(v_val_1799_);
                    leanh::lean_dec_ref_known(v___x_1798_, 1);
                    v_keyName_1800_ = leanh::lean_ctor_get(v_val_1799_, 2);
                    leanh::lean_inc(v_keyName_1800_);
                    v___x_1801_ = l_Lake_LeanExe_keyword;
                    leanh::lean_inc(v_name_1791_);
                    v___x_1802_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1802_, 0, v_val_1799_);
                    leanh::lean_ctor_set(v___x_1802_, 1, v_name_1791_);
                    leanh::lean_ctor_set(v___x_1802_, 2, v_config_1792_);
                    v___x_1803_ = l_Lake_LeanExe_exeFacet;
                    v___x_1804_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1804_, 0, v_keyName_1800_);
                    leanh::lean_ctor_set(v___x_1804_, 1, v_name_1791_);
                    if v_isShared_1795_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1794_, 1);
                        leanh::lean_ctor_set(v___x_1794_, 3, v___x_1803_);
                        leanh::lean_ctor_set(v___x_1794_, 2, v___x_1802_);
                        leanh::lean_ctor_set(v___x_1794_, 1, v___x_1801_);
                        leanh::lean_ctor_set(v___x_1794_, 0, v___x_1804_);
                        v___x_1806_ = v___x_1794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1801_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 2, v___x_1802_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 3, v___x_1803_);
                        v___x_1806_ = v_reuseFailAlloc_1808_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1798_);
                    leanh::lean_del_object(v___x_1794_);
                    leanh::lean_dec(v_config_1792_);
                    leanh::lean_dec_ref(v_a_1782_);
                    v___x_1809_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1810_ = 1;
                    v___x_1811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1790_,
                        v___x_1810_,
                    );
                    v___x_1812_ = lean_string_append(v___x_1809_, v___x_1811_);
                    leanh::lean_dec_ref(v___x_1811_);
                    v___x_1813_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1814_ = lean_string_append(v___x_1812_, v___x_1813_);
                    v___x_1815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1791_,
                        v___x_1810_,
                    );
                    v___x_1816_ = lean_string_append(v___x_1814_, v___x_1815_);
                    leanh::lean_dec_ref(v___x_1815_);
                    v___x_1817_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
                    v___x_1819_ = 3;
                    v___x_1820_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1818_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1820_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1819_,
                    );
                    v___x_1821_ = lean_array_get_size(v_a_1787_);
                    v___x_1822_ = lean_array_push(v_a_1787_, v___x_1820_);
                    v___x_1823_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1823_, 0, v___x_1821_);
                    leanh::lean_ctor_set(v___x_1823_, 1, v___x_1822_);
                    return v___x_1823_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_a_1786_);
                leanh::lean_inc(v_a_1785_);
                leanh::lean_inc(v_a_1784_);
                leanh::lean_inc(v_a_1783_);
                v___x_1807_ = leanh::lean_apply_7(
                    v_a_1782_,
                    v___x_1806_,
                    v_a_1783_,
                    v_a_1784_,
                    v_a_1785_,
                    v_a_1786_,
                    v_a_1787_,
                    leanh::lean_box(0),
                );
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeDecl_fetch___boxed(
    mut v_self_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
    mut v_a_1828_: *mut leanh::LeanObject,
    mut v_a_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
    mut v_a_1831_: *mut leanh::LeanObject,
    mut v_a_1832_: *mut leanh::LeanObject,
    mut v_a_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lake_LeanExeDecl_fetch(
        v_self_1826_,
        v_a_1827_,
        v_a_1828_,
        v_a_1829_,
        v_a_1830_,
        v_a_1831_,
        v_a_1832_,
    );
    leanh::lean_dec_ref(v_a_1831_);
    leanh::lean_dec(v_a_1830_);
    leanh::lean_dec(v_a_1829_);
    leanh::lean_dec(v_a_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lake_InputFile_fetch(
    mut v_self_1835_: *mut leanh::LeanObject,
    mut v_a_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1843_ = leanh::lean_ctor_get(v_self_1835_, 0);
    v_name_1844_ = leanh::lean_ctor_get(v_self_1835_, 1);
    v_keyName_1845_ = leanh::lean_ctor_get(v_pkg_1843_, 2);
    v___x_1846_ = l_Lake_InputFile_defaultFacet;
    leanh::lean_inc(v_name_1844_);
    leanh::lean_inc(v_keyName_1845_);
    v___x_1847_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1847_, 0, v_keyName_1845_);
    leanh::lean_ctor_set(v___x_1847_, 1, v_name_1844_);
    v___x_1848_ = l_Lake_InputFile_keyword;
    v___x_1849_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1849_, 0, v___x_1847_);
    leanh::lean_ctor_set(v___x_1849_, 1, v___x_1848_);
    leanh::lean_ctor_set(v___x_1849_, 2, v_self_1835_);
    leanh::lean_ctor_set(v___x_1849_, 3, v___x_1846_);
    leanh::lean_inc_ref(v_a_1840_);
    leanh::lean_inc(v_a_1839_);
    leanh::lean_inc(v_a_1838_);
    leanh::lean_inc(v_a_1837_);
    v___x_1850_ = leanh::lean_apply_7(
        v_a_1836_,
        v___x_1849_,
        v_a_1837_,
        v_a_1838_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
        leanh::lean_box(0),
    );
    return v___x_1850_;
}
pub unsafe fn l_Lake_InputFile_fetch___boxed(
    mut v_self_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lake_InputFile_fetch(
        v_self_1851_,
        v_a_1852_,
        v_a_1853_,
        v_a_1854_,
        v_a_1855_,
        v_a_1856_,
        v_a_1857_,
    );
    leanh::lean_dec_ref(v_a_1856_);
    leanh::lean_dec(v_a_1855_);
    leanh::lean_dec(v_a_1854_);
    leanh::lean_dec(v_a_1853_);
    return v_res_1859_;
}
pub unsafe fn l_Lake_InputFileDecl_get___redArg(
    mut v_self_1860_: *mut leanh::LeanObject,
    mut v_inst_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_inst_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = leanh::lean_ctor_get(v_inst_1861_, 0);
    leanh::lean_inc_ref(v_toApplicative_1864_);
    v_toFunctor_1865_ = leanh::lean_ctor_get(v_toApplicative_1864_, 0);
    leanh::lean_inc_ref(v_toFunctor_1865_);
    v_toBind_1866_ = leanh::lean_ctor_get(v_inst_1861_, 1);
    leanh::lean_inc(v_toBind_1866_);
    leanh::lean_dec_ref(v_inst_1861_);
    v_toPure_1867_ = leanh::lean_ctor_get(v_toApplicative_1864_, 1);
    leanh::lean_inc(v_toPure_1867_);
    leanh::lean_dec_ref(v_toApplicative_1864_);
    v_pkg_1868_ = leanh::lean_ctor_get(v_self_1860_, 0);
    leanh::lean_inc_n(v_pkg_1868_, 2);
    v_name_1869_ = leanh::lean_ctor_get(v_self_1860_, 1);
    leanh::lean_inc(v_name_1869_);
    v_config_1870_ = leanh::lean_ctor_get(v_self_1860_, 3);
    leanh::lean_inc(v_config_1870_);
    leanh::lean_dec_ref(v_self_1860_);
    v_map_1871_ = leanh::lean_ctor_get(v_toFunctor_1865_, 0);
    leanh::lean_inc_n(v_map_1871_, 2);
    leanh::lean_dec_ref(v_toFunctor_1865_);
    v___f_1872_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1873_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1873_, 0, v_name_1869_);
    leanh::lean_closure_set(v___f_1873_, 1, v_config_1870_);
    leanh::lean_closure_set(v___f_1873_, 2, v_toPure_1867_);
    leanh::lean_closure_set(v___f_1873_, 3, v_pkg_1868_);
    leanh::lean_closure_set(v___f_1873_, 4, v_inst_1862_);
    v___f_1874_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1874_, 0, v_pkg_1868_);
    v___x_1875_ = leanh::lean_apply_4(
        v_map_1871_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1872_,
        v_inst_1863_,
    );
    v___x_1876_ = leanh::lean_apply_4(
        v_map_1871_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1874_,
        v___x_1875_,
    );
    v___x_1877_ = leanh::lean_apply_4(
        v_toBind_1866_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1876_,
        v___f_1873_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lake_InputFileDecl_get(
    mut v_m_1878_: *mut leanh::LeanObject,
    mut v_self_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_inst_1881_: *mut leanh::LeanObject,
    mut v_inst_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1883_ = leanh::lean_ctor_get(v_inst_1880_, 0);
    leanh::lean_inc_ref(v_toApplicative_1883_);
    v_toFunctor_1884_ = leanh::lean_ctor_get(v_toApplicative_1883_, 0);
    leanh::lean_inc_ref(v_toFunctor_1884_);
    v_toBind_1885_ = leanh::lean_ctor_get(v_inst_1880_, 1);
    leanh::lean_inc(v_toBind_1885_);
    leanh::lean_dec_ref(v_inst_1880_);
    v_toPure_1886_ = leanh::lean_ctor_get(v_toApplicative_1883_, 1);
    leanh::lean_inc(v_toPure_1886_);
    leanh::lean_dec_ref(v_toApplicative_1883_);
    v_pkg_1887_ = leanh::lean_ctor_get(v_self_1879_, 0);
    leanh::lean_inc_n(v_pkg_1887_, 2);
    v_name_1888_ = leanh::lean_ctor_get(v_self_1879_, 1);
    leanh::lean_inc(v_name_1888_);
    v_config_1889_ = leanh::lean_ctor_get(v_self_1879_, 3);
    leanh::lean_inc(v_config_1889_);
    leanh::lean_dec_ref(v_self_1879_);
    v_map_1890_ = leanh::lean_ctor_get(v_toFunctor_1884_, 0);
    leanh::lean_inc_n(v_map_1890_, 2);
    leanh::lean_dec_ref(v_toFunctor_1884_);
    v___f_1891_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1892_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1892_, 0, v_name_1888_);
    leanh::lean_closure_set(v___f_1892_, 1, v_config_1889_);
    leanh::lean_closure_set(v___f_1892_, 2, v_toPure_1886_);
    leanh::lean_closure_set(v___f_1892_, 3, v_pkg_1887_);
    leanh::lean_closure_set(v___f_1892_, 4, v_inst_1881_);
    v___f_1893_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1893_, 0, v_pkg_1887_);
    v___x_1894_ = leanh::lean_apply_4(
        v_map_1890_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1891_,
        v_inst_1882_,
    );
    v___x_1895_ = leanh::lean_apply_4(
        v_map_1890_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1893_,
        v___x_1894_,
    );
    v___x_1896_ = leanh::lean_apply_4(
        v_toBind_1885_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1895_,
        v___f_1892_,
    );
    return v___x_1896_;
}
pub unsafe fn l_Lake_InputFileDecl_fetch(
    mut v_self_1897_: *mut leanh::LeanObject,
    mut v_a_1898_: *mut leanh::LeanObject,
    mut v_a_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v_packageMap_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1905_ = leanh::lean_ctor_get(v_a_1902_, 1);
                v_pkg_1906_ = leanh::lean_ctor_get(v_self_1897_, 0);
                v_name_1907_ = leanh::lean_ctor_get(v_self_1897_, 1);
                v_config_1908_ = leanh::lean_ctor_get(v_self_1897_, 3);
                v_isSharedCheck_1940_ = (!leanh::lean_is_exclusive(v_self_1897_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v_unused_1941_ = leanh::lean_ctor_get(v_self_1897_, 2);
                    leanh::lean_dec(v_unused_1941_);
                    v___x_1910_ = v_self_1897_;
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_config_1908_);
                    leanh::lean_inc(v_name_1907_);
                    leanh::lean_inc(v_pkg_1906_);
                    leanh::lean_dec(v_self_1897_);
                    v___x_1910_ = leanh::lean_box(0);
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1912_ = leanh::lean_ctor_get(v_toContext_1905_, 5);
                v___x_1913_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                leanh::lean_inc(v_pkg_1906_);
                leanh::lean_inc(v_packageMap_1912_);
                v___x_1914_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1913_,
                    v_packageMap_1912_,
                    v_pkg_1906_,
                );
                if leanh::lean_obj_tag(v___x_1914_) == 1 {
                    leanh::lean_dec(v_pkg_1906_);
                    v_val_1915_ = leanh::lean_ctor_get(v___x_1914_, 0);
                    leanh::lean_inc(v_val_1915_);
                    leanh::lean_dec_ref_known(v___x_1914_, 1);
                    v_keyName_1916_ = leanh::lean_ctor_get(v_val_1915_, 2);
                    leanh::lean_inc(v_keyName_1916_);
                    v___x_1917_ = l_Lake_InputFile_keyword;
                    leanh::lean_inc(v_name_1907_);
                    v___x_1918_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1918_, 0, v_val_1915_);
                    leanh::lean_ctor_set(v___x_1918_, 1, v_name_1907_);
                    leanh::lean_ctor_set(v___x_1918_, 2, v_config_1908_);
                    v___x_1919_ = l_Lake_InputFile_defaultFacet;
                    v___x_1920_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1920_, 0, v_keyName_1916_);
                    leanh::lean_ctor_set(v___x_1920_, 1, v_name_1907_);
                    if v_isShared_1911_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1910_, 1);
                        leanh::lean_ctor_set(v___x_1910_, 3, v___x_1919_);
                        leanh::lean_ctor_set(v___x_1910_, 2, v___x_1918_);
                        leanh::lean_ctor_set(v___x_1910_, 1, v___x_1917_);
                        leanh::lean_ctor_set(v___x_1910_, 0, v___x_1920_);
                        v___x_1922_ = v___x_1910_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1920_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1917_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 2, v___x_1918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 3, v___x_1919_);
                        v___x_1922_ = v_reuseFailAlloc_1924_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1914_);
                    leanh::lean_del_object(v___x_1910_);
                    leanh::lean_dec(v_config_1908_);
                    leanh::lean_dec_ref(v_a_1898_);
                    v___x_1925_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1926_ = 1;
                    v___x_1927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1906_,
                        v___x_1926_,
                    );
                    v___x_1928_ = lean_string_append(v___x_1925_, v___x_1927_);
                    leanh::lean_dec_ref(v___x_1927_);
                    v___x_1929_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
                    v___x_1931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1907_,
                        v___x_1926_,
                    );
                    v___x_1932_ = lean_string_append(v___x_1930_, v___x_1931_);
                    leanh::lean_dec_ref(v___x_1931_);
                    v___x_1933_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1934_ = lean_string_append(v___x_1932_, v___x_1933_);
                    v___x_1935_ = 3;
                    v___x_1936_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1936_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1935_,
                    );
                    v___x_1937_ = lean_array_get_size(v_a_1903_);
                    v___x_1938_ = lean_array_push(v_a_1903_, v___x_1936_);
                    v___x_1939_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1937_);
                    leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                    return v___x_1939_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_a_1902_);
                leanh::lean_inc(v_a_1901_);
                leanh::lean_inc(v_a_1900_);
                leanh::lean_inc(v_a_1899_);
                v___x_1923_ = leanh::lean_apply_7(
                    v_a_1898_,
                    v___x_1922_,
                    v_a_1899_,
                    v_a_1900_,
                    v_a_1901_,
                    v_a_1902_,
                    v_a_1903_,
                    leanh::lean_box(0),
                );
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileDecl_fetch___boxed(
    mut v_self_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_a_1945_: *mut leanh::LeanObject,
    mut v_a_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lake_InputFileDecl_fetch(
        v_self_1942_,
        v_a_1943_,
        v_a_1944_,
        v_a_1945_,
        v_a_1946_,
        v_a_1947_,
        v_a_1948_,
    );
    leanh::lean_dec_ref(v_a_1947_);
    leanh::lean_dec(v_a_1946_);
    leanh::lean_dec(v_a_1945_);
    leanh::lean_dec(v_a_1944_);
    return v_res_1950_;
}
pub unsafe fn l_Lake_InputDir_fetch(
    mut v_self_1951_: *mut leanh::LeanObject,
    mut v_a_1952_: *mut leanh::LeanObject,
    mut v_a_1953_: *mut leanh::LeanObject,
    mut v_a_1954_: *mut leanh::LeanObject,
    mut v_a_1955_: *mut leanh::LeanObject,
    mut v_a_1956_: *mut leanh::LeanObject,
    mut v_a_1957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1959_ = leanh::lean_ctor_get(v_self_1951_, 0);
    v_name_1960_ = leanh::lean_ctor_get(v_self_1951_, 1);
    v_keyName_1961_ = leanh::lean_ctor_get(v_pkg_1959_, 2);
    v___x_1962_ = l_Lake_InputDir_defaultFacet;
    leanh::lean_inc(v_name_1960_);
    leanh::lean_inc(v_keyName_1961_);
    v___x_1963_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1963_, 0, v_keyName_1961_);
    leanh::lean_ctor_set(v___x_1963_, 1, v_name_1960_);
    v___x_1964_ = l_Lake_InputDir_keyword;
    v___x_1965_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1965_, 0, v___x_1963_);
    leanh::lean_ctor_set(v___x_1965_, 1, v___x_1964_);
    leanh::lean_ctor_set(v___x_1965_, 2, v_self_1951_);
    leanh::lean_ctor_set(v___x_1965_, 3, v___x_1962_);
    leanh::lean_inc_ref(v_a_1956_);
    leanh::lean_inc(v_a_1955_);
    leanh::lean_inc(v_a_1954_);
    leanh::lean_inc(v_a_1953_);
    v___x_1966_ = leanh::lean_apply_7(
        v_a_1952_,
        v___x_1965_,
        v_a_1953_,
        v_a_1954_,
        v_a_1955_,
        v_a_1956_,
        v_a_1957_,
        leanh::lean_box(0),
    );
    return v___x_1966_;
}
pub unsafe fn l_Lake_InputDir_fetch___boxed(
    mut v_self_1967_: *mut leanh::LeanObject,
    mut v_a_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
    mut v_a_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lake_InputDir_fetch(
        v_self_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
    );
    leanh::lean_dec_ref(v_a_1972_);
    leanh::lean_dec(v_a_1971_);
    leanh::lean_dec(v_a_1970_);
    leanh::lean_dec(v_a_1969_);
    return v_res_1975_;
}
pub unsafe fn l_Lake_InputDirDecl_get___redArg(
    mut v_self_1976_: *mut leanh::LeanObject,
    mut v_inst_1977_: *mut leanh::LeanObject,
    mut v_inst_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1980_ = leanh::lean_ctor_get(v_inst_1977_, 0);
    leanh::lean_inc_ref(v_toApplicative_1980_);
    v_toFunctor_1981_ = leanh::lean_ctor_get(v_toApplicative_1980_, 0);
    leanh::lean_inc_ref(v_toFunctor_1981_);
    v_toBind_1982_ = leanh::lean_ctor_get(v_inst_1977_, 1);
    leanh::lean_inc(v_toBind_1982_);
    leanh::lean_dec_ref(v_inst_1977_);
    v_toPure_1983_ = leanh::lean_ctor_get(v_toApplicative_1980_, 1);
    leanh::lean_inc(v_toPure_1983_);
    leanh::lean_dec_ref(v_toApplicative_1980_);
    v_pkg_1984_ = leanh::lean_ctor_get(v_self_1976_, 0);
    leanh::lean_inc_n(v_pkg_1984_, 2);
    v_name_1985_ = leanh::lean_ctor_get(v_self_1976_, 1);
    leanh::lean_inc(v_name_1985_);
    v_config_1986_ = leanh::lean_ctor_get(v_self_1976_, 3);
    leanh::lean_inc(v_config_1986_);
    leanh::lean_dec_ref(v_self_1976_);
    v_map_1987_ = leanh::lean_ctor_get(v_toFunctor_1981_, 0);
    leanh::lean_inc_n(v_map_1987_, 2);
    leanh::lean_dec_ref(v_toFunctor_1981_);
    v___f_1988_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1989_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1989_, 0, v_name_1985_);
    leanh::lean_closure_set(v___f_1989_, 1, v_config_1986_);
    leanh::lean_closure_set(v___f_1989_, 2, v_toPure_1983_);
    leanh::lean_closure_set(v___f_1989_, 3, v_pkg_1984_);
    leanh::lean_closure_set(v___f_1989_, 4, v_inst_1978_);
    v___f_1990_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1990_, 0, v_pkg_1984_);
    v___x_1991_ = leanh::lean_apply_4(
        v_map_1987_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1988_,
        v_inst_1979_,
    );
    v___x_1992_ = leanh::lean_apply_4(
        v_map_1987_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1990_,
        v___x_1991_,
    );
    v___x_1993_ = leanh::lean_apply_4(
        v_toBind_1982_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1992_,
        v___f_1989_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_InputDirDecl_get(
    mut v_m_1994_: *mut leanh::LeanObject,
    mut v_self_1995_: *mut leanh::LeanObject,
    mut v_inst_1996_: *mut leanh::LeanObject,
    mut v_inst_1997_: *mut leanh::LeanObject,
    mut v_inst_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1999_ = leanh::lean_ctor_get(v_inst_1996_, 0);
    leanh::lean_inc_ref(v_toApplicative_1999_);
    v_toFunctor_2000_ = leanh::lean_ctor_get(v_toApplicative_1999_, 0);
    leanh::lean_inc_ref(v_toFunctor_2000_);
    v_toBind_2001_ = leanh::lean_ctor_get(v_inst_1996_, 1);
    leanh::lean_inc(v_toBind_2001_);
    leanh::lean_dec_ref(v_inst_1996_);
    v_toPure_2002_ = leanh::lean_ctor_get(v_toApplicative_1999_, 1);
    leanh::lean_inc(v_toPure_2002_);
    leanh::lean_dec_ref(v_toApplicative_1999_);
    v_pkg_2003_ = leanh::lean_ctor_get(v_self_1995_, 0);
    leanh::lean_inc_n(v_pkg_2003_, 2);
    v_name_2004_ = leanh::lean_ctor_get(v_self_1995_, 1);
    leanh::lean_inc(v_name_2004_);
    v_config_2005_ = leanh::lean_ctor_get(v_self_1995_, 3);
    leanh::lean_inc(v_config_2005_);
    leanh::lean_dec_ref(v_self_1995_);
    v_map_2006_ = leanh::lean_ctor_get(v_toFunctor_2000_, 0);
    leanh::lean_inc_n(v_map_2006_, 2);
    leanh::lean_dec_ref(v_toFunctor_2000_);
    v___f_2007_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_2008_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2008_, 0, v_name_2004_);
    leanh::lean_closure_set(v___f_2008_, 1, v_config_2005_);
    leanh::lean_closure_set(v___f_2008_, 2, v_toPure_2002_);
    leanh::lean_closure_set(v___f_2008_, 3, v_pkg_2003_);
    leanh::lean_closure_set(v___f_2008_, 4, v_inst_1997_);
    v___f_2009_ = leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2009_, 0, v_pkg_2003_);
    v___x_2010_ = leanh::lean_apply_4(
        v_map_2006_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2007_,
        v_inst_1998_,
    );
    v___x_2011_ = leanh::lean_apply_4(
        v_map_2006_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2009_,
        v___x_2010_,
    );
    v___x_2012_ = leanh::lean_apply_4(
        v_toBind_2001_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2011_,
        v___f_2008_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_InputDirDecl_fetch(
    mut v_self_2013_: *mut leanh::LeanObject,
    mut v_a_2014_: *mut leanh::LeanObject,
    mut v_a_2015_: *mut leanh::LeanObject,
    mut v_a_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toContext_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v_packageMap_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_2021_ = leanh::lean_ctor_get(v_a_2018_, 1);
                v_pkg_2022_ = leanh::lean_ctor_get(v_self_2013_, 0);
                v_name_2023_ = leanh::lean_ctor_get(v_self_2013_, 1);
                v_config_2024_ = leanh::lean_ctor_get(v_self_2013_, 3);
                v_isSharedCheck_2056_ = (!leanh::lean_is_exclusive(v_self_2013_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = leanh::lean_ctor_get(v_self_2013_, 2);
                    leanh::lean_dec(v_unused_2057_);
                    v___x_2026_ = v_self_2013_;
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_config_2024_);
                    leanh::lean_inc(v_name_2023_);
                    leanh::lean_inc(v_pkg_2022_);
                    leanh::lean_dec(v_self_2013_);
                    v___x_2026_ = leanh::lean_box(0);
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_2028_ = leanh::lean_ctor_get(v_toContext_2021_, 5);
                v___x_2029_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                leanh::lean_inc(v_pkg_2022_);
                leanh::lean_inc(v_packageMap_2028_);
                v___x_2030_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_2029_,
                    v_packageMap_2028_,
                    v_pkg_2022_,
                );
                if leanh::lean_obj_tag(v___x_2030_) == 1 {
                    leanh::lean_dec(v_pkg_2022_);
                    v_val_2031_ = leanh::lean_ctor_get(v___x_2030_, 0);
                    leanh::lean_inc(v_val_2031_);
                    leanh::lean_dec_ref_known(v___x_2030_, 1);
                    v_keyName_2032_ = leanh::lean_ctor_get(v_val_2031_, 2);
                    leanh::lean_inc(v_keyName_2032_);
                    v___x_2033_ = l_Lake_InputDir_keyword;
                    leanh::lean_inc(v_name_2023_);
                    v___x_2034_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2034_, 0, v_val_2031_);
                    leanh::lean_ctor_set(v___x_2034_, 1, v_name_2023_);
                    leanh::lean_ctor_set(v___x_2034_, 2, v_config_2024_);
                    v___x_2035_ = l_Lake_InputDir_defaultFacet;
                    v___x_2036_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2036_, 0, v_keyName_2032_);
                    leanh::lean_ctor_set(v___x_2036_, 1, v_name_2023_);
                    if v_isShared_2027_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2026_, 1);
                        leanh::lean_ctor_set(v___x_2026_, 3, v___x_2035_);
                        leanh::lean_ctor_set(v___x_2026_, 2, v___x_2034_);
                        leanh::lean_ctor_set(v___x_2026_, 1, v___x_2033_);
                        leanh::lean_ctor_set(v___x_2026_, 0, v___x_2036_);
                        v___x_2038_ = v___x_2026_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2040_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2033_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 2, v___x_2034_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 3, v___x_2035_);
                        v___x_2038_ = v_reuseFailAlloc_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2030_);
                    leanh::lean_del_object(v___x_2026_);
                    leanh::lean_dec(v_config_2024_);
                    leanh::lean_dec_ref(v_a_2014_);
                    v___x_2041_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_2042_ = 1;
                    v___x_2043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_2022_,
                        v___x_2042_,
                    );
                    v___x_2044_ = lean_string_append(v___x_2041_, v___x_2043_);
                    leanh::lean_dec_ref(v___x_2043_);
                    v___x_2045_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
                    v___x_2047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2023_,
                        v___x_2042_,
                    );
                    v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
                    leanh::lean_dec_ref(v___x_2047_);
                    v___x_2049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
                    v___x_2051_ = 3;
                    v___x_2052_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2052_, 0, v___x_2050_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2052_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2051_,
                    );
                    v___x_2053_ = lean_array_get_size(v_a_2019_);
                    v___x_2054_ = lean_array_push(v_a_2019_, v___x_2052_);
                    v___x_2055_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2055_, 0, v___x_2053_);
                    leanh::lean_ctor_set(v___x_2055_, 1, v___x_2054_);
                    return v___x_2055_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_a_2018_);
                leanh::lean_inc(v_a_2017_);
                leanh::lean_inc(v_a_2016_);
                leanh::lean_inc(v_a_2015_);
                v___x_2039_ = leanh::lean_apply_7(
                    v_a_2014_,
                    v___x_2038_,
                    v_a_2015_,
                    v_a_2016_,
                    v_a_2017_,
                    v_a_2018_,
                    v_a_2019_,
                    leanh::lean_box(0),
                );
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirDecl_fetch___boxed(
    mut v_self_2058_: *mut leanh::LeanObject,
    mut v_a_2059_: *mut leanh::LeanObject,
    mut v_a_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
    mut v_a_2064_: *mut leanh::LeanObject,
    mut v_a_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lake_InputDirDecl_fetch(
        v_self_2058_,
        v_a_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
        v_a_2064_,
    );
    leanh::lean_dec_ref(v_a_2063_);
    leanh::lean_dec(v_a_2062_);
    leanh::lean_dec(v_a_2061_);
    leanh::lean_dec(v_a_2060_);
    return v_res_2066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Targets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Targets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Targets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Targets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Targets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Targets(builtin);
}