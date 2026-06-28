// Lean compiler output
// Module: Lake.Build.Targets
// Imports: Lake.Config.Monad Lake.Config.InputFile Lake.Build.Infos
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1};
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
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_array_push};
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_KConfigDecl_get___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_KConfigDecl_get___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_KConfigDecl_get___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__1_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__2_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_fetch___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_LeanLib_fetch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_fetch___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_fetch___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0(
    mut v_x_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1034_);
    return v_x_1034_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0___boxed(
    mut v_x_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lake_KConfigDecl_get___redArg___lam__0(v_x_1035_);
    crate::leanh::lean_dec(v_x_1035_);
    return v_res_1036_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1(
    mut v_name_1040_: *mut crate::leanh::LeanObject,
    mut v_config_1041_: *mut crate::leanh::LeanObject,
    mut v_toPure_1042_: *mut crate::leanh::LeanObject,
    mut v_pkg_1043_: *mut crate::leanh::LeanObject,
    mut v_inst_1044_: *mut crate::leanh::LeanObject,
    mut v_____x_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_1045_) == 1 {
        let mut v_val_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_1044_);
        crate::leanh::lean_dec(v_pkg_1043_);
        v_val_1046_ = crate::leanh::lean_ctor_get(v_____x_1045_, 0);
        crate::leanh::lean_inc(v_val_1046_);
        v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1047_, 0, v_val_1046_);
        crate::leanh::lean_ctor_set(v___x_1047_, 1, v_name_1040_);
        crate::leanh::lean_ctor_set(v___x_1047_, 2, v_config_1041_);
        v___x_1048_ =
            crate::leanh::lean_apply_2(v_toPure_1042_, crate::leanh::lean_box(0), v___x_1047_);
        return v___x_1048_;
    } else {
        let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: u8 = 0;
        let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1042_);
        crate::leanh::lean_dec(v_config_1041_);
        v___x_1049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
        v___x_1050_ = 1;
        v___x_1051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1043_,
            v___x_1050_,
        );
        v___x_1052_ = lean_string_append(v___x_1049_, v___x_1051_);
        crate::leanh::lean_dec_ref(v___x_1051_);
        v___x_1053_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
        v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
        v___x_1055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1040_,
            v___x_1050_,
        );
        v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
        crate::leanh::lean_dec_ref(v___x_1055_);
        v___x_1057_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
        v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
        v___x_1059_ =
            crate::leanh::lean_apply_2(v_inst_1044_, crate::leanh::lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1___boxed(
    mut v_name_1060_: *mut crate::leanh::LeanObject,
    mut v_config_1061_: *mut crate::leanh::LeanObject,
    mut v_toPure_1062_: *mut crate::leanh::LeanObject,
    mut v_pkg_1063_: *mut crate::leanh::LeanObject,
    mut v_inst_1064_: *mut crate::leanh::LeanObject,
    mut v_____x_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lake_KConfigDecl_get___redArg___lam__1(
        v_name_1060_,
        v_config_1061_,
        v_toPure_1062_,
        v_pkg_1063_,
        v_inst_1064_,
        v_____x_1065_,
    );
    crate::leanh::lean_dec(v_____x_1065_);
    return v_res_1066_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__2(
    mut v_pkg_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packageMap_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1070_ = crate::leanh::lean_ctor_get(v_x_1069_, 5);
    crate::leanh::lean_inc(v_packageMap_1070_);
    crate::leanh::lean_dec_ref(v_x_1069_);
    v___x_1071_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    v___x_1072_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1071_, v_packageMap_1070_, v_pkg_1068_);
    return v___x_1072_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg(
    mut v_inst_1074_: *mut crate::leanh::LeanObject,
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_self_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1078_ = crate::leanh::lean_ctor_get(v_inst_1074_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1078_);
    v_toFunctor_1079_ = crate::leanh::lean_ctor_get(v_toApplicative_1078_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1079_);
    v_toBind_1080_ = crate::leanh::lean_ctor_get(v_inst_1074_, 1);
    crate::leanh::lean_inc(v_toBind_1080_);
    crate::leanh::lean_dec_ref(v_inst_1074_);
    v_toPure_1081_ = crate::leanh::lean_ctor_get(v_toApplicative_1078_, 1);
    crate::leanh::lean_inc(v_toPure_1081_);
    crate::leanh::lean_dec_ref(v_toApplicative_1078_);
    v_pkg_1082_ = crate::leanh::lean_ctor_get(v_self_1077_, 0);
    crate::leanh::lean_inc_n(v_pkg_1082_, 2);
    v_name_1083_ = crate::leanh::lean_ctor_get(v_self_1077_, 1);
    crate::leanh::lean_inc(v_name_1083_);
    v_config_1084_ = crate::leanh::lean_ctor_get(v_self_1077_, 3);
    crate::leanh::lean_inc(v_config_1084_);
    crate::leanh::lean_dec_ref(v_self_1077_);
    v_map_1085_ = crate::leanh::lean_ctor_get(v_toFunctor_1079_, 0);
    crate::leanh::lean_inc_n(v_map_1085_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1079_);
    v___f_1086_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1087_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1087_, 0, v_name_1083_);
    crate::leanh::lean_closure_set(v___f_1087_, 1, v_config_1084_);
    crate::leanh::lean_closure_set(v___f_1087_, 2, v_toPure_1081_);
    crate::leanh::lean_closure_set(v___f_1087_, 3, v_pkg_1082_);
    crate::leanh::lean_closure_set(v___f_1087_, 4, v_inst_1075_);
    v___f_1088_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1088_, 0, v_pkg_1082_);
    v___x_1089_ = crate::leanh::lean_apply_4(
        v_map_1085_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1086_,
        v_inst_1076_,
    );
    v___x_1090_ = crate::leanh::lean_apply_4(
        v_map_1085_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1088_,
        v___x_1089_,
    );
    v___x_1091_ = crate::leanh::lean_apply_4(
        v_toBind_1080_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1090_,
        v___f_1087_,
    );
    return v___x_1091_;
}
pub unsafe fn l_Lake_KConfigDecl_get(
    mut v_m_1092_: *mut crate::leanh::LeanObject,
    mut v_kind_1093_: *mut crate::leanh::LeanObject,
    mut v_inst_1094_: *mut crate::leanh::LeanObject,
    mut v_inst_1095_: *mut crate::leanh::LeanObject,
    mut v_inst_1096_: *mut crate::leanh::LeanObject,
    mut v_self_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = crate::leanh::lean_ctor_get(v_inst_1094_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1098_);
    v_toFunctor_1099_ = crate::leanh::lean_ctor_get(v_toApplicative_1098_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1099_);
    v_toBind_1100_ = crate::leanh::lean_ctor_get(v_inst_1094_, 1);
    crate::leanh::lean_inc(v_toBind_1100_);
    crate::leanh::lean_dec_ref(v_inst_1094_);
    v_toPure_1101_ = crate::leanh::lean_ctor_get(v_toApplicative_1098_, 1);
    crate::leanh::lean_inc(v_toPure_1101_);
    crate::leanh::lean_dec_ref(v_toApplicative_1098_);
    v_pkg_1102_ = crate::leanh::lean_ctor_get(v_self_1097_, 0);
    crate::leanh::lean_inc_n(v_pkg_1102_, 2);
    v_name_1103_ = crate::leanh::lean_ctor_get(v_self_1097_, 1);
    crate::leanh::lean_inc(v_name_1103_);
    v_config_1104_ = crate::leanh::lean_ctor_get(v_self_1097_, 3);
    crate::leanh::lean_inc(v_config_1104_);
    crate::leanh::lean_dec_ref(v_self_1097_);
    v_map_1105_ = crate::leanh::lean_ctor_get(v_toFunctor_1099_, 0);
    crate::leanh::lean_inc_n(v_map_1105_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1099_);
    v___f_1106_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1107_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1107_, 0, v_name_1103_);
    crate::leanh::lean_closure_set(v___f_1107_, 1, v_config_1104_);
    crate::leanh::lean_closure_set(v___f_1107_, 2, v_toPure_1101_);
    crate::leanh::lean_closure_set(v___f_1107_, 3, v_pkg_1102_);
    crate::leanh::lean_closure_set(v___f_1107_, 4, v_inst_1095_);
    v___f_1108_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1108_, 0, v_pkg_1102_);
    v___x_1109_ = crate::leanh::lean_apply_4(
        v_map_1105_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1106_,
        v_inst_1096_,
    );
    v___x_1110_ = crate::leanh::lean_apply_4(
        v_map_1105_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1108_,
        v___x_1109_,
    );
    v___x_1111_ = crate::leanh::lean_apply_4(
        v_toBind_1100_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1110_,
        v___f_1107_,
    );
    return v___x_1111_;
}
pub unsafe fn l_Lake_KConfigDecl_get___boxed(
    mut v_m_1112_: *mut crate::leanh::LeanObject,
    mut v_kind_1113_: *mut crate::leanh::LeanObject,
    mut v_inst_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_inst_1116_: *mut crate::leanh::LeanObject,
    mut v_self_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lake_KConfigDecl_get(
        v_m_1112_,
        v_kind_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_inst_1116_,
        v_self_1117_,
    );
    crate::leanh::lean_dec(v_kind_1113_);
    return v_res_1118_;
}
pub unsafe fn l_Lake_Package_fetchTargetJob(
    mut v_self_1119_: *mut crate::leanh::LeanObject,
    mut v_target_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1128_, 0, v_self_1119_);
                crate::leanh::lean_ctor_set(v___x_1128_, 1, v_target_1120_);
                crate::leanh::lean_inc_ref(v_a_1125_);
                crate::leanh::lean_inc(v_a_1124_);
                crate::leanh::lean_inc(v_a_1123_);
                crate::leanh::lean_inc(v_a_1122_);
                v___x_1129_ = crate::leanh::lean_apply_7(
                    v_a_1121_,
                    v___x_1128_,
                    v_a_1122_,
                    v_a_1123_,
                    v_a_1124_,
                    v_a_1125_,
                    v_a_1126_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1129_) == 0 {
                    v_a_1130_ = crate::leanh::lean_ctor_get(v___x_1129_, 0);
                    v_a_1131_ = crate::leanh::lean_ctor_get(v___x_1129_, 1);
                    v_isSharedCheck_1139_ = (!crate::leanh::lean_is_exclusive(v___x_1129_)) as u8;
                    if v_isSharedCheck_1139_ == 0 {
                        v___x_1133_ = v___x_1129_;
                        v_isShared_1134_ = v_isSharedCheck_1139_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1131_);
                        crate::leanh::lean_inc(v_a_1130_);
                        crate::leanh::lean_dec(v___x_1129_);
                        v___x_1133_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1135_);
                    v___x_1137_ = v___x_1133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1131_);
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
    mut v_self_1140_: *mut crate::leanh::LeanObject,
    mut v_target_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_a_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1146_);
    crate::leanh::lean_dec(v_a_1145_);
    crate::leanh::lean_dec(v_a_1144_);
    crate::leanh::lean_dec(v_a_1143_);
    return v_res_1149_;
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg(
    mut v_self_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toContext_1161_ = crate::leanh::lean_ctor_get(v_a_1158_, 1);
    v_pkg_1162_ = crate::leanh::lean_ctor_get(v_self_1153_, 0);
    crate::leanh::lean_inc_n(v_pkg_1162_, 2);
    v_name_1163_ = crate::leanh::lean_ctor_get(v_self_1153_, 1);
    crate::leanh::lean_inc(v_name_1163_);
    crate::leanh::lean_dec_ref(v_self_1153_);
    v_packageMap_1164_ = crate::leanh::lean_ctor_get(v_toContext_1161_, 5);
    v___x_1165_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    crate::leanh::lean_inc(v_packageMap_1164_);
    v___x_1166_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1165_, v_packageMap_1164_, v_pkg_1162_);
    if crate::leanh::lean_obj_tag(v___x_1166_) == 1 {
        let mut v_val_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_pkg_1162_);
        v_val_1167_ = crate::leanh::lean_ctor_get(v___x_1166_, 0);
        crate::leanh::lean_inc(v_val_1167_);
        crate::leanh::lean_dec_ref_known(v___x_1166_, 1);
        v___x_1168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1168_, 0, v_val_1167_);
        crate::leanh::lean_ctor_set(v___x_1168_, 1, v_name_1163_);
        crate::leanh::lean_inc_ref(v_a_1158_);
        crate::leanh::lean_inc(v_a_1157_);
        crate::leanh::lean_inc(v_a_1156_);
        crate::leanh::lean_inc(v_a_1155_);
        v___x_1169_ = crate::leanh::lean_apply_7(
            v_a_1154_,
            v___x_1168_,
            v_a_1155_,
            v_a_1156_,
            v_a_1157_,
            v_a_1158_,
            v_a_1159_,
            crate::leanh::lean_box(0),
        );
        return v___x_1169_;
    } else {
        let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: u8 = 0;
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: u8 = 0;
        let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1166_);
        crate::leanh::lean_dec_ref(v_a_1154_);
        v___x_1170_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
        v___x_1171_ = 1;
        v___x_1172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1162_,
            v___x_1171_,
        );
        v___x_1173_ = lean_string_append(v___x_1170_, v___x_1172_);
        crate::leanh::lean_dec_ref(v___x_1172_);
        v___x_1174_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
        v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
        v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1163_,
            v___x_1171_,
        );
        v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
        crate::leanh::lean_dec_ref(v___x_1176_);
        v___x_1178_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
        v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
        v___x_1180_ = 3;
        v___x_1181_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1179_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1181_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1180_,
        );
        v___x_1182_ = lean_array_get_size(v_a_1159_);
        v___x_1183_ = lean_array_push(v_a_1159_, v___x_1181_);
        v___x_1184_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1184_, 0, v___x_1182_);
        crate::leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
        return v___x_1184_;
    }
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg___boxed(
    mut v_self_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_TargetDecl_fetch___redArg(
        v_self_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
        v_a_1189_,
        v_a_1190_,
        v_a_1191_,
    );
    crate::leanh::lean_dec_ref(v_a_1190_);
    crate::leanh::lean_dec(v_a_1189_);
    crate::leanh::lean_dec(v_a_1188_);
    crate::leanh::lean_dec(v_a_1187_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_TargetDecl_fetch(
    mut v_00_u03b1_1194_: *mut crate::leanh::LeanObject,
    mut v_self_1195_: *mut crate::leanh::LeanObject,
    mut v_inst_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1205_: *mut crate::leanh::LeanObject,
    mut v_self_1206_: *mut crate::leanh::LeanObject,
    mut v_inst_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
    mut v_a_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_a_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1212_);
    crate::leanh::lean_dec(v_a_1211_);
    crate::leanh::lean_dec(v_a_1210_);
    crate::leanh::lean_dec(v_a_1209_);
    return v_res_1215_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
    mut v_t_1216_: *mut crate::leanh::LeanObject,
    mut v_k_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1216_) == 0 {
                    v_k_1218_ = crate::leanh::lean_ctor_get(v_t_1216_, 1);
                    v_v_1219_ = crate::leanh::lean_ctor_get(v_t_1216_, 2);
                    v_l_1220_ = crate::leanh::lean_ctor_get(v_t_1216_, 3);
                    v_r_1221_ = crate::leanh::lean_ctor_get(v_t_1216_, 4);
                    v___x_1222_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1217_, v_k_1218_);
                    match v___x_1222_ {
                        0 => {
                            v_t_1216_ = v_l_1220_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1219_);
                            v___x_1224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1224_, 0, v_v_1219_);
                            return v___x_1224_;
                        }
                        _ => {
                            v_t_1216_ = v_r_1221_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1226_ = crate::leanh::lean_box(0);
                    return v___x_1226_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(
    mut v_t_1227_: *mut crate::leanh::LeanObject,
    mut v_k_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1227_, v_k_1228_,
        );
    crate::leanh::lean_dec(v_k_1228_);
    crate::leanh::lean_dec(v_t_1227_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_TargetDecl_fetchJob(
    mut v_self_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1238_ = crate::leanh::lean_ctor_get(v_a_1235_, 1);
                v_pkg_1239_ = crate::leanh::lean_ctor_get(v_self_1230_, 0);
                crate::leanh::lean_inc(v_pkg_1239_);
                v_name_1240_ = crate::leanh::lean_ctor_get(v_self_1230_, 1);
                crate::leanh::lean_inc(v_name_1240_);
                crate::leanh::lean_dec_ref(v_self_1230_);
                v_packageMap_1241_ = crate::leanh::lean_ctor_get(v_toContext_1238_, 5);
                v___x_1242_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_packageMap_1241_, v_pkg_1239_);
                if crate::leanh::lean_obj_tag(v___x_1242_) == 1 {
                    crate::leanh::lean_dec(v_pkg_1239_);
                    v_val_1243_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                    crate::leanh::lean_inc(v_val_1243_);
                    crate::leanh::lean_dec_ref_known(v___x_1242_, 1);
                    v___x_1244_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1244_, 0, v_val_1243_);
                    crate::leanh::lean_ctor_set(v___x_1244_, 1, v_name_1240_);
                    crate::leanh::lean_inc_ref(v_a_1235_);
                    crate::leanh::lean_inc(v_a_1234_);
                    crate::leanh::lean_inc(v_a_1233_);
                    crate::leanh::lean_inc(v_a_1232_);
                    v___x_1245_ = crate::leanh::lean_apply_7(
                        v_a_1231_,
                        v___x_1244_,
                        v_a_1232_,
                        v_a_1233_,
                        v_a_1234_,
                        v_a_1235_,
                        v_a_1236_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1245_) == 0 {
                        v_a_1246_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                        v_a_1247_ = crate::leanh::lean_ctor_get(v___x_1245_, 1);
                        v_isSharedCheck_1255_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1245_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1249_ = v___x_1245_;
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1247_);
                            crate::leanh::lean_inc(v_a_1246_);
                            crate::leanh::lean_dec(v___x_1245_);
                            v___x_1249_ = crate::leanh::lean_box(0);
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1245_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1242_);
                    crate::leanh::lean_dec_ref(v_a_1231_);
                    v___x_1256_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
                    v___x_1257_ = 1;
                    v___x_1258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1239_,
                        v___x_1257_,
                    );
                    v___x_1259_ = lean_string_append(v___x_1256_, v___x_1258_);
                    crate::leanh::lean_dec_ref(v___x_1258_);
                    v___x_1260_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
                    v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
                    v___x_1262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1240_,
                        v___x_1257_,
                    );
                    v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
                    crate::leanh::lean_dec_ref(v___x_1262_);
                    v___x_1264_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
                    v___x_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
                    v___x_1266_ = 3;
                    v___x_1267_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1265_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1267_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1266_,
                    );
                    v___x_1268_ = lean_array_get_size(v_a_1236_);
                    v___x_1269_ = lean_array_push(v_a_1236_, v___x_1267_);
                    v___x_1270_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1268_);
                    crate::leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
                    return v___x_1270_;
                }
            }
            1 => {
                v___x_1251_ = l_Lake_Job_toOpaque___redArg(v_a_1246_);
                if v_isShared_1250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1247_);
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
    mut v_self_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lake_TargetDecl_fetchJob(
        v_self_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
        v_a_1275_,
        v_a_1276_,
        v_a_1277_,
    );
    crate::leanh::lean_dec_ref(v_a_1276_);
    crate::leanh::lean_dec(v_a_1275_);
    crate::leanh::lean_dec(v_a_1274_);
    crate::leanh::lean_dec(v_a_1273_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
    mut v_00_u03b2_1280_: *mut crate::leanh::LeanObject,
    mut v_inst_1281_: *mut crate::leanh::LeanObject,
    mut v_t_1282_: *mut crate::leanh::LeanObject,
    mut v_k_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1282_, v_k_1283_,
        );
    return v___x_1284_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(
    mut v_00_u03b2_1285_: *mut crate::leanh::LeanObject,
    mut v_inst_1286_: *mut crate::leanh::LeanObject,
    mut v_t_1287_: *mut crate::leanh::LeanObject,
    mut v_k_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
        v_00_u03b2_1285_,
        v_inst_1286_,
        v_t_1287_,
        v_k_1288_,
    );
    crate::leanh::lean_dec(v_k_1288_);
    crate::leanh::lean_dec(v_t_1287_);
    return v_res_1289_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg(
    mut v_pkg_1290_: *mut crate::leanh::LeanObject,
    mut v_self_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1299_ = crate::leanh::lean_ctor_get(v_self_1291_, 0);
    v_keyName_1300_ = crate::leanh::lean_ctor_get(v_pkg_1290_, 2);
    crate::leanh::lean_inc(v_keyName_1300_);
    v___x_1301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1301_, 0, v_keyName_1300_);
    v___x_1302_ = l_Lake_Package_keyword;
    crate::leanh::lean_inc(v_name_1299_);
    v___x_1303_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1303_, 0, v___x_1301_);
    crate::leanh::lean_ctor_set(v___x_1303_, 1, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1303_, 2, v_pkg_1290_);
    crate::leanh::lean_ctor_set(v___x_1303_, 3, v_name_1299_);
    crate::leanh::lean_inc_ref(v_a_1296_);
    crate::leanh::lean_inc(v_a_1295_);
    crate::leanh::lean_inc(v_a_1294_);
    crate::leanh::lean_inc(v_a_1293_);
    v___x_1304_ = crate::leanh::lean_apply_7(
        v_a_1292_,
        v___x_1303_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        crate::leanh::lean_box(0),
    );
    return v___x_1304_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg___boxed(
    mut v_pkg_1305_: *mut crate::leanh::LeanObject,
    mut v_self_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1311_);
    crate::leanh::lean_dec(v_a_1310_);
    crate::leanh::lean_dec(v_a_1309_);
    crate::leanh::lean_dec(v_a_1308_);
    crate::leanh::lean_dec_ref(v_self_1306_);
    return v_res_1314_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch(
    mut v_00_u03b1_1315_: *mut crate::leanh::LeanObject,
    mut v_pkg_1316_: *mut crate::leanh::LeanObject,
    mut v_self_1317_: *mut crate::leanh::LeanObject,
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1326_ = crate::leanh::lean_ctor_get(v_self_1317_, 0);
    v_keyName_1327_ = crate::leanh::lean_ctor_get(v_pkg_1316_, 2);
    crate::leanh::lean_inc(v_keyName_1327_);
    v___x_1328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1328_, 0, v_keyName_1327_);
    v___x_1329_ = l_Lake_Package_keyword;
    crate::leanh::lean_inc(v_name_1326_);
    v___x_1330_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1328_);
    crate::leanh::lean_ctor_set(v___x_1330_, 1, v___x_1329_);
    crate::leanh::lean_ctor_set(v___x_1330_, 2, v_pkg_1316_);
    crate::leanh::lean_ctor_set(v___x_1330_, 3, v_name_1326_);
    crate::leanh::lean_inc_ref(v_a_1323_);
    crate::leanh::lean_inc(v_a_1322_);
    crate::leanh::lean_inc(v_a_1321_);
    crate::leanh::lean_inc(v_a_1320_);
    v___x_1331_ = crate::leanh::lean_apply_7(
        v_a_1319_,
        v___x_1330_,
        v_a_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        crate::leanh::lean_box(0),
    );
    return v___x_1331_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___boxed(
    mut v_00_u03b1_1332_: *mut crate::leanh::LeanObject,
    mut v_pkg_1333_: *mut crate::leanh::LeanObject,
    mut v_self_1334_: *mut crate::leanh::LeanObject,
    mut v_inst_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
    mut v_a_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1340_);
    crate::leanh::lean_dec(v_a_1339_);
    crate::leanh::lean_dec(v_a_1338_);
    crate::leanh::lean_dec(v_a_1337_);
    crate::leanh::lean_dec_ref(v_self_1334_);
    return v_res_1343_;
}
pub unsafe fn l_Lake_Package_fetchFacetJob(
    mut v_name_1344_: *mut crate::leanh::LeanObject,
    mut v_self_1345_: *mut crate::leanh::LeanObject,
    mut v_a_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_a_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
    mut v_a_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keyName_1353_ = crate::leanh::lean_ctor_get(v_self_1345_, 2);
                v___x_1354_ = l_Lake_Package_keyword;
                v___x_1355_ = l_Lean_Name_append(v___x_1354_, v_name_1344_);
                crate::leanh::lean_inc(v_keyName_1353_);
                v___x_1356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1356_, 0, v_keyName_1353_);
                v___x_1357_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1354_);
                crate::leanh::lean_ctor_set(v___x_1357_, 2, v_self_1345_);
                crate::leanh::lean_ctor_set(v___x_1357_, 3, v___x_1355_);
                crate::leanh::lean_inc_ref(v_a_1350_);
                crate::leanh::lean_inc(v_a_1349_);
                crate::leanh::lean_inc(v_a_1348_);
                crate::leanh::lean_inc(v_a_1347_);
                v___x_1358_ = crate::leanh::lean_apply_7(
                    v_a_1346_,
                    v___x_1357_,
                    v_a_1347_,
                    v_a_1348_,
                    v_a_1349_,
                    v_a_1350_,
                    v_a_1351_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1358_) == 0 {
                    v_a_1359_ = crate::leanh::lean_ctor_get(v___x_1358_, 0);
                    v_a_1360_ = crate::leanh::lean_ctor_get(v___x_1358_, 1);
                    v_isSharedCheck_1368_ = (!crate::leanh::lean_is_exclusive(v___x_1358_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1362_ = v___x_1358_;
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1360_);
                        crate::leanh::lean_inc(v_a_1359_);
                        crate::leanh::lean_dec(v___x_1358_);
                        v___x_1362_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1362_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1360_);
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
    mut v_name_1369_: *mut crate::leanh::LeanObject,
    mut v_self_1370_: *mut crate::leanh::LeanObject,
    mut v_a_1371_: *mut crate::leanh::LeanObject,
    mut v_a_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1375_);
    crate::leanh::lean_dec(v_a_1374_);
    crate::leanh::lean_dec(v_a_1373_);
    crate::leanh::lean_dec(v_a_1372_);
    return v_res_1378_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg(
    mut v_mod_1379_: *mut crate::leanh::LeanObject,
    mut v_self_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v_name_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_unused_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1388_ = crate::leanh::lean_ctor_get(v_mod_1379_, 0);
                v_pkg_1389_ = crate::leanh::lean_ctor_get(v_lib_1388_, 0);
                v_name_1390_ = crate::leanh::lean_ctor_get(v_self_1380_, 0);
                v_isSharedCheck_1402_ = (!crate::leanh::lean_is_exclusive(v_self_1380_)) as u8;
                if v_isSharedCheck_1402_ == 0 {
                    v_unused_1403_ = crate::leanh::lean_ctor_get(v_self_1380_, 1);
                    crate::leanh::lean_dec(v_unused_1403_);
                    v___x_1392_ = v_self_1380_;
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1390_);
                    crate::leanh::lean_dec(v_self_1380_);
                    v___x_1392_ = crate::leanh::lean_box(0);
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1394_ = crate::leanh::lean_ctor_get(v_mod_1379_, 1);
                v_keyName_1395_ = crate::leanh::lean_ctor_get(v_pkg_1389_, 2);
                crate::leanh::lean_inc(v_name_1394_);
                crate::leanh::lean_inc(v_keyName_1395_);
                if v_isShared_1393_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1392_, 2);
                    crate::leanh::lean_ctor_set(v___x_1392_, 1, v_name_1394_);
                    crate::leanh::lean_ctor_set(v___x_1392_, 0, v_keyName_1395_);
                    v___x_1397_ = v___x_1392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1401_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_keyName_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_name_1394_);
                    v___x_1397_ = v_reuseFailAlloc_1401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1398_ = l_Lake_Module_keyword;
                v___x_1399_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1399_, 0, v___x_1397_);
                crate::leanh::lean_ctor_set(v___x_1399_, 1, v___x_1398_);
                crate::leanh::lean_ctor_set(v___x_1399_, 2, v_mod_1379_);
                crate::leanh::lean_ctor_set(v___x_1399_, 3, v_name_1390_);
                crate::leanh::lean_inc_ref(v_a_1385_);
                crate::leanh::lean_inc(v_a_1384_);
                crate::leanh::lean_inc(v_a_1383_);
                crate::leanh::lean_inc(v_a_1382_);
                v___x_1400_ = crate::leanh::lean_apply_7(
                    v_a_1381_,
                    v___x_1399_,
                    v_a_1382_,
                    v_a_1383_,
                    v_a_1384_,
                    v_a_1385_,
                    v_a_1386_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg___boxed(
    mut v_mod_1404_: *mut crate::leanh::LeanObject,
    mut v_self_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1410_);
    crate::leanh::lean_dec(v_a_1409_);
    crate::leanh::lean_dec(v_a_1408_);
    crate::leanh::lean_dec(v_a_1407_);
    return v_res_1413_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch(
    mut v_00_u03b1_1414_: *mut crate::leanh::LeanObject,
    mut v_mod_1415_: *mut crate::leanh::LeanObject,
    mut v_self_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_name_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1439_: u8 = 0;
    let mut v_unused_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1425_ = crate::leanh::lean_ctor_get(v_mod_1415_, 0);
                v_pkg_1426_ = crate::leanh::lean_ctor_get(v_lib_1425_, 0);
                v_name_1427_ = crate::leanh::lean_ctor_get(v_self_1416_, 0);
                v_isSharedCheck_1439_ = (!crate::leanh::lean_is_exclusive(v_self_1416_)) as u8;
                if v_isSharedCheck_1439_ == 0 {
                    v_unused_1440_ = crate::leanh::lean_ctor_get(v_self_1416_, 1);
                    crate::leanh::lean_dec(v_unused_1440_);
                    v___x_1429_ = v_self_1416_;
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1427_);
                    crate::leanh::lean_dec(v_self_1416_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1431_ = crate::leanh::lean_ctor_get(v_mod_1415_, 1);
                v_keyName_1432_ = crate::leanh::lean_ctor_get(v_pkg_1426_, 2);
                crate::leanh::lean_inc(v_name_1431_);
                crate::leanh::lean_inc(v_keyName_1432_);
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1429_, 2);
                    crate::leanh::lean_ctor_set(v___x_1429_, 1, v_name_1431_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_keyName_1432_);
                    v___x_1434_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_keyName_1432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_name_1431_);
                    v___x_1434_ = v_reuseFailAlloc_1438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1435_ = l_Lake_Module_keyword;
                v___x_1436_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1434_);
                crate::leanh::lean_ctor_set(v___x_1436_, 1, v___x_1435_);
                crate::leanh::lean_ctor_set(v___x_1436_, 2, v_mod_1415_);
                crate::leanh::lean_ctor_set(v___x_1436_, 3, v_name_1427_);
                crate::leanh::lean_inc_ref(v_a_1422_);
                crate::leanh::lean_inc(v_a_1421_);
                crate::leanh::lean_inc(v_a_1420_);
                crate::leanh::lean_inc(v_a_1419_);
                v___x_1437_ = crate::leanh::lean_apply_7(
                    v_a_1418_,
                    v___x_1436_,
                    v_a_1419_,
                    v_a_1420_,
                    v_a_1421_,
                    v_a_1422_,
                    v_a_1423_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___boxed(
    mut v_00_u03b1_1441_: *mut crate::leanh::LeanObject,
    mut v_mod_1442_: *mut crate::leanh::LeanObject,
    mut v_self_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1449_);
    crate::leanh::lean_dec(v_a_1448_);
    crate::leanh::lean_dec(v_a_1447_);
    crate::leanh::lean_dec(v_a_1446_);
    return v_res_1452_;
}
pub unsafe fn l_Lake_Module_fetchFacetJob(
    mut v_name_1453_: *mut crate::leanh::LeanObject,
    mut v_self_1454_: *mut crate::leanh::LeanObject,
    mut v_a_1455_: *mut crate::leanh::LeanObject,
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_a_1457_: *mut crate::leanh::LeanObject,
    mut v_a_1458_: *mut crate::leanh::LeanObject,
    mut v_a_1459_: *mut crate::leanh::LeanObject,
    mut v_a_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1462_ = crate::leanh::lean_ctor_get(v_self_1454_, 0);
                v_pkg_1463_ = crate::leanh::lean_ctor_get(v_lib_1462_, 0);
                v_name_1464_ = crate::leanh::lean_ctor_get(v_self_1454_, 1);
                v_keyName_1465_ = crate::leanh::lean_ctor_get(v_pkg_1463_, 2);
                v___x_1466_ = l_Lake_Module_keyword;
                v___x_1467_ = l_Lean_Name_append(v___x_1466_, v_name_1453_);
                crate::leanh::lean_inc(v_name_1464_);
                crate::leanh::lean_inc(v_keyName_1465_);
                v___x_1468_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1468_, 0, v_keyName_1465_);
                crate::leanh::lean_ctor_set(v___x_1468_, 1, v_name_1464_);
                v___x_1469_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                crate::leanh::lean_ctor_set(v___x_1469_, 1, v___x_1466_);
                crate::leanh::lean_ctor_set(v___x_1469_, 2, v_self_1454_);
                crate::leanh::lean_ctor_set(v___x_1469_, 3, v___x_1467_);
                crate::leanh::lean_inc_ref(v_a_1459_);
                crate::leanh::lean_inc(v_a_1458_);
                crate::leanh::lean_inc(v_a_1457_);
                crate::leanh::lean_inc(v_a_1456_);
                v___x_1470_ = crate::leanh::lean_apply_7(
                    v_a_1455_,
                    v___x_1469_,
                    v_a_1456_,
                    v_a_1457_,
                    v_a_1458_,
                    v_a_1459_,
                    v_a_1460_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1470_) == 0 {
                    v_a_1471_ = crate::leanh::lean_ctor_get(v___x_1470_, 0);
                    v_a_1472_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                    v_isSharedCheck_1480_ = (!crate::leanh::lean_is_exclusive(v___x_1470_)) as u8;
                    if v_isSharedCheck_1480_ == 0 {
                        v___x_1474_ = v___x_1470_;
                        v_isShared_1475_ = v_isSharedCheck_1480_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1472_);
                        crate::leanh::lean_inc(v_a_1471_);
                        crate::leanh::lean_dec(v___x_1470_);
                        v___x_1474_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1472_);
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
    mut v_name_1481_: *mut crate::leanh::LeanObject,
    mut v_self_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1487_);
    crate::leanh::lean_dec(v_a_1486_);
    crate::leanh::lean_dec(v_a_1485_);
    crate::leanh::lean_dec(v_a_1484_);
    return v_res_1490_;
}
pub unsafe fn l_Lake_LeanLibDecl_get___redArg(
    mut v_self_1491_: *mut crate::leanh::LeanObject,
    mut v_inst_1492_: *mut crate::leanh::LeanObject,
    mut v_inst_1493_: *mut crate::leanh::LeanObject,
    mut v_inst_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1495_ = crate::leanh::lean_ctor_get(v_inst_1492_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1495_);
    v_toFunctor_1496_ = crate::leanh::lean_ctor_get(v_toApplicative_1495_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1496_);
    v_toBind_1497_ = crate::leanh::lean_ctor_get(v_inst_1492_, 1);
    crate::leanh::lean_inc(v_toBind_1497_);
    crate::leanh::lean_dec_ref(v_inst_1492_);
    v_toPure_1498_ = crate::leanh::lean_ctor_get(v_toApplicative_1495_, 1);
    crate::leanh::lean_inc(v_toPure_1498_);
    crate::leanh::lean_dec_ref(v_toApplicative_1495_);
    v_pkg_1499_ = crate::leanh::lean_ctor_get(v_self_1491_, 0);
    crate::leanh::lean_inc_n(v_pkg_1499_, 2);
    v_name_1500_ = crate::leanh::lean_ctor_get(v_self_1491_, 1);
    crate::leanh::lean_inc(v_name_1500_);
    v_config_1501_ = crate::leanh::lean_ctor_get(v_self_1491_, 3);
    crate::leanh::lean_inc(v_config_1501_);
    crate::leanh::lean_dec_ref(v_self_1491_);
    v_map_1502_ = crate::leanh::lean_ctor_get(v_toFunctor_1496_, 0);
    crate::leanh::lean_inc_n(v_map_1502_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1496_);
    v___f_1503_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1504_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1504_, 0, v_name_1500_);
    crate::leanh::lean_closure_set(v___f_1504_, 1, v_config_1501_);
    crate::leanh::lean_closure_set(v___f_1504_, 2, v_toPure_1498_);
    crate::leanh::lean_closure_set(v___f_1504_, 3, v_pkg_1499_);
    crate::leanh::lean_closure_set(v___f_1504_, 4, v_inst_1493_);
    v___f_1505_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1505_, 0, v_pkg_1499_);
    v___x_1506_ = crate::leanh::lean_apply_4(
        v_map_1502_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1503_,
        v_inst_1494_,
    );
    v___x_1507_ = crate::leanh::lean_apply_4(
        v_map_1502_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1505_,
        v___x_1506_,
    );
    v___x_1508_ = crate::leanh::lean_apply_4(
        v_toBind_1497_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1507_,
        v___f_1504_,
    );
    return v___x_1508_;
}
pub unsafe fn l_Lake_LeanLibDecl_get(
    mut v_m_1509_: *mut crate::leanh::LeanObject,
    mut v_self_1510_: *mut crate::leanh::LeanObject,
    mut v_inst_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_inst_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1514_ = crate::leanh::lean_ctor_get(v_inst_1511_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1514_);
    v_toFunctor_1515_ = crate::leanh::lean_ctor_get(v_toApplicative_1514_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1515_);
    v_toBind_1516_ = crate::leanh::lean_ctor_get(v_inst_1511_, 1);
    crate::leanh::lean_inc(v_toBind_1516_);
    crate::leanh::lean_dec_ref(v_inst_1511_);
    v_toPure_1517_ = crate::leanh::lean_ctor_get(v_toApplicative_1514_, 1);
    crate::leanh::lean_inc(v_toPure_1517_);
    crate::leanh::lean_dec_ref(v_toApplicative_1514_);
    v_pkg_1518_ = crate::leanh::lean_ctor_get(v_self_1510_, 0);
    crate::leanh::lean_inc_n(v_pkg_1518_, 2);
    v_name_1519_ = crate::leanh::lean_ctor_get(v_self_1510_, 1);
    crate::leanh::lean_inc(v_name_1519_);
    v_config_1520_ = crate::leanh::lean_ctor_get(v_self_1510_, 3);
    crate::leanh::lean_inc(v_config_1520_);
    crate::leanh::lean_dec_ref(v_self_1510_);
    v_map_1521_ = crate::leanh::lean_ctor_get(v_toFunctor_1515_, 0);
    crate::leanh::lean_inc_n(v_map_1521_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1515_);
    v___f_1522_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1523_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1523_, 0, v_name_1519_);
    crate::leanh::lean_closure_set(v___f_1523_, 1, v_config_1520_);
    crate::leanh::lean_closure_set(v___f_1523_, 2, v_toPure_1517_);
    crate::leanh::lean_closure_set(v___f_1523_, 3, v_pkg_1518_);
    crate::leanh::lean_closure_set(v___f_1523_, 4, v_inst_1512_);
    v___f_1524_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1524_, 0, v_pkg_1518_);
    v___x_1525_ = crate::leanh::lean_apply_4(
        v_map_1521_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1522_,
        v_inst_1513_,
    );
    v___x_1526_ = crate::leanh::lean_apply_4(
        v_map_1521_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1524_,
        v___x_1525_,
    );
    v___x_1527_ = crate::leanh::lean_apply_4(
        v_toBind_1516_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1526_,
        v___f_1523_,
    );
    return v___x_1527_;
}
pub unsafe fn l_Lake_LeanLib_fetch(
    mut v_self_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1539_ = crate::leanh::lean_ctor_get(v_self_1531_, 0);
    v_name_1540_ = crate::leanh::lean_ctor_get(v_self_1531_, 1);
    v_keyName_1541_ = crate::leanh::lean_ctor_get(v_pkg_1539_, 2);
    v___x_1542_ = l_Lake_LeanLib_defaultFacet;
    crate::leanh::lean_inc(v_name_1540_);
    crate::leanh::lean_inc(v_keyName_1541_);
    v___x_1543_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1543_, 0, v_keyName_1541_);
    crate::leanh::lean_ctor_set(v___x_1543_, 1, v_name_1540_);
    v___x_1544_ = l_Lake_LeanLib_fetch___closed__1;
    v___x_1545_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
    crate::leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    crate::leanh::lean_ctor_set(v___x_1545_, 2, v_self_1531_);
    crate::leanh::lean_ctor_set(v___x_1545_, 3, v___x_1542_);
    crate::leanh::lean_inc_ref(v_a_1536_);
    crate::leanh::lean_inc(v_a_1535_);
    crate::leanh::lean_inc(v_a_1534_);
    crate::leanh::lean_inc(v_a_1533_);
    v___x_1546_ = crate::leanh::lean_apply_7(
        v_a_1532_,
        v___x_1545_,
        v_a_1533_,
        v_a_1534_,
        v_a_1535_,
        v_a_1536_,
        v_a_1537_,
        crate::leanh::lean_box(0),
    );
    return v___x_1546_;
}
pub unsafe fn l_Lake_LeanLib_fetch___boxed(
    mut v_self_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Lake_LeanLib_fetch(
        v_self_1547_,
        v_a_1548_,
        v_a_1549_,
        v_a_1550_,
        v_a_1551_,
        v_a_1552_,
        v_a_1553_,
    );
    crate::leanh::lean_dec_ref(v_a_1552_);
    crate::leanh::lean_dec(v_a_1551_);
    crate::leanh::lean_dec(v_a_1550_);
    crate::leanh::lean_dec(v_a_1549_);
    return v_res_1555_;
}
pub unsafe fn l_Lake_LeanLibDecl_fetch(
    mut v_self_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_a_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_packageMap_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_unused_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1564_ = crate::leanh::lean_ctor_get(v_a_1561_, 1);
                v_pkg_1565_ = crate::leanh::lean_ctor_get(v_self_1556_, 0);
                v_name_1566_ = crate::leanh::lean_ctor_get(v_self_1556_, 1);
                v_config_1567_ = crate::leanh::lean_ctor_get(v_self_1556_, 3);
                v_isSharedCheck_1599_ = (!crate::leanh::lean_is_exclusive(v_self_1556_)) as u8;
                if v_isSharedCheck_1599_ == 0 {
                    v_unused_1600_ = crate::leanh::lean_ctor_get(v_self_1556_, 2);
                    crate::leanh::lean_dec(v_unused_1600_);
                    v___x_1569_ = v_self_1556_;
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_config_1567_);
                    crate::leanh::lean_inc(v_name_1566_);
                    crate::leanh::lean_inc(v_pkg_1565_);
                    crate::leanh::lean_dec(v_self_1556_);
                    v___x_1569_ = crate::leanh::lean_box(0);
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1571_ = crate::leanh::lean_ctor_get(v_toContext_1564_, 5);
                v___x_1572_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                crate::leanh::lean_inc(v_pkg_1565_);
                crate::leanh::lean_inc(v_packageMap_1571_);
                v___x_1573_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1572_,
                    v_packageMap_1571_,
                    v_pkg_1565_,
                );
                if crate::leanh::lean_obj_tag(v___x_1573_) == 1 {
                    crate::leanh::lean_dec(v_pkg_1565_);
                    v_val_1574_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                    crate::leanh::lean_inc(v_val_1574_);
                    crate::leanh::lean_dec_ref_known(v___x_1573_, 1);
                    v_keyName_1575_ = crate::leanh::lean_ctor_get(v_val_1574_, 2);
                    crate::leanh::lean_inc(v_keyName_1575_);
                    v___x_1576_ = l_Lake_LeanLib_fetch___closed__1;
                    crate::leanh::lean_inc(v_name_1566_);
                    v___x_1577_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1577_, 0, v_val_1574_);
                    crate::leanh::lean_ctor_set(v___x_1577_, 1, v_name_1566_);
                    crate::leanh::lean_ctor_set(v___x_1577_, 2, v_config_1567_);
                    v___x_1578_ = l_Lake_LeanLib_defaultFacet;
                    v___x_1579_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1579_, 0, v_keyName_1575_);
                    crate::leanh::lean_ctor_set(v___x_1579_, 1, v_name_1566_);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1569_, 1);
                        crate::leanh::lean_ctor_set(v___x_1569_, 3, v___x_1578_);
                        crate::leanh::lean_ctor_set(v___x_1569_, 2, v___x_1577_);
                        crate::leanh::lean_ctor_set(v___x_1569_, 1, v___x_1576_);
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1579_);
                        v___x_1581_ = v___x_1569_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1583_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1576_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 2, v___x_1577_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1578_);
                        v___x_1581_ = v_reuseFailAlloc_1583_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1573_);
                    crate::leanh::lean_del_object(v___x_1569_);
                    crate::leanh::lean_dec(v_config_1567_);
                    crate::leanh::lean_dec_ref(v_a_1557_);
                    v___x_1584_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1585_ = 1;
                    v___x_1586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1565_,
                        v___x_1585_,
                    );
                    v___x_1587_ = lean_string_append(v___x_1584_, v___x_1586_);
                    crate::leanh::lean_dec_ref(v___x_1586_);
                    v___x_1588_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
                    v___x_1590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1566_,
                        v___x_1585_,
                    );
                    v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
                    crate::leanh::lean_dec_ref(v___x_1590_);
                    v___x_1592_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
                    v___x_1594_ = 3;
                    v___x_1595_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1595_, 0, v___x_1593_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1595_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1594_,
                    );
                    v___x_1596_ = lean_array_get_size(v_a_1562_);
                    v___x_1597_ = lean_array_push(v_a_1562_, v___x_1595_);
                    v___x_1598_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1596_);
                    crate::leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                    return v___x_1598_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_1561_);
                crate::leanh::lean_inc(v_a_1560_);
                crate::leanh::lean_inc(v_a_1559_);
                crate::leanh::lean_inc(v_a_1558_);
                v___x_1582_ = crate::leanh::lean_apply_7(
                    v_a_1557_,
                    v___x_1581_,
                    v_a_1558_,
                    v_a_1559_,
                    v_a_1560_,
                    v_a_1561_,
                    v_a_1562_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibDecl_fetch___boxed(
    mut v_self_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lake_LeanLibDecl_fetch(
        v_self_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
    );
    crate::leanh::lean_dec_ref(v_a_1606_);
    crate::leanh::lean_dec(v_a_1605_);
    crate::leanh::lean_dec(v_a_1604_);
    crate::leanh::lean_dec(v_a_1603_);
    return v_res_1609_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg(
    mut v_lib_1610_: *mut crate::leanh::LeanObject,
    mut v_self_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
    mut v_a_1614_: *mut crate::leanh::LeanObject,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_name_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1619_ = crate::leanh::lean_ctor_get(v_lib_1610_, 0);
                v_name_1620_ = crate::leanh::lean_ctor_get(v_self_1611_, 0);
                v_isSharedCheck_1632_ = (!crate::leanh::lean_is_exclusive(v_self_1611_)) as u8;
                if v_isSharedCheck_1632_ == 0 {
                    v_unused_1633_ = crate::leanh::lean_ctor_get(v_self_1611_, 1);
                    crate::leanh::lean_dec(v_unused_1633_);
                    v___x_1622_ = v_self_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1620_);
                    crate::leanh::lean_dec(v_self_1611_);
                    v___x_1622_ = crate::leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1624_ = crate::leanh::lean_ctor_get(v_lib_1610_, 1);
                v_keyName_1625_ = crate::leanh::lean_ctor_get(v_pkg_1619_, 2);
                crate::leanh::lean_inc(v_name_1624_);
                crate::leanh::lean_inc(v_keyName_1625_);
                if v_isShared_1623_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1622_, 3);
                    crate::leanh::lean_ctor_set(v___x_1622_, 1, v_name_1624_);
                    crate::leanh::lean_ctor_set(v___x_1622_, 0, v_keyName_1625_);
                    v___x_1627_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_keyName_1625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_name_1624_);
                    v___x_1627_ = v_reuseFailAlloc_1631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1629_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1629_, 0, v___x_1627_);
                crate::leanh::lean_ctor_set(v___x_1629_, 1, v___x_1628_);
                crate::leanh::lean_ctor_set(v___x_1629_, 2, v_lib_1610_);
                crate::leanh::lean_ctor_set(v___x_1629_, 3, v_name_1620_);
                crate::leanh::lean_inc_ref(v_a_1616_);
                crate::leanh::lean_inc(v_a_1615_);
                crate::leanh::lean_inc(v_a_1614_);
                crate::leanh::lean_inc(v_a_1613_);
                v___x_1630_ = crate::leanh::lean_apply_7(
                    v_a_1612_,
                    v___x_1629_,
                    v_a_1613_,
                    v_a_1614_,
                    v_a_1615_,
                    v_a_1616_,
                    v_a_1617_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg___boxed(
    mut v_lib_1634_: *mut crate::leanh::LeanObject,
    mut v_self_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1640_);
    crate::leanh::lean_dec(v_a_1639_);
    crate::leanh::lean_dec(v_a_1638_);
    crate::leanh::lean_dec(v_a_1637_);
    return v_res_1643_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch(
    mut v_00_u03b1_1644_: *mut crate::leanh::LeanObject,
    mut v_lib_1645_: *mut crate::leanh::LeanObject,
    mut v_self_1646_: *mut crate::leanh::LeanObject,
    mut v_inst_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v_name_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1655_ = crate::leanh::lean_ctor_get(v_lib_1645_, 0);
                v_name_1656_ = crate::leanh::lean_ctor_get(v_self_1646_, 0);
                v_isSharedCheck_1668_ = (!crate::leanh::lean_is_exclusive(v_self_1646_)) as u8;
                if v_isSharedCheck_1668_ == 0 {
                    v_unused_1669_ = crate::leanh::lean_ctor_get(v_self_1646_, 1);
                    crate::leanh::lean_dec(v_unused_1669_);
                    v___x_1658_ = v_self_1646_;
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1656_);
                    crate::leanh::lean_dec(v_self_1646_);
                    v___x_1658_ = crate::leanh::lean_box(0);
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1660_ = crate::leanh::lean_ctor_get(v_lib_1645_, 1);
                v_keyName_1661_ = crate::leanh::lean_ctor_get(v_pkg_1655_, 2);
                crate::leanh::lean_inc(v_name_1660_);
                crate::leanh::lean_inc(v_keyName_1661_);
                if v_isShared_1659_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1658_, 3);
                    crate::leanh::lean_ctor_set(v___x_1658_, 1, v_name_1660_);
                    crate::leanh::lean_ctor_set(v___x_1658_, 0, v_keyName_1661_);
                    v___x_1663_ = v___x_1658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_keyName_1661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_name_1660_);
                    v___x_1663_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1664_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1665_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1663_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                crate::leanh::lean_ctor_set(v___x_1665_, 2, v_lib_1645_);
                crate::leanh::lean_ctor_set(v___x_1665_, 3, v_name_1656_);
                crate::leanh::lean_inc_ref(v_a_1652_);
                crate::leanh::lean_inc(v_a_1651_);
                crate::leanh::lean_inc(v_a_1650_);
                crate::leanh::lean_inc(v_a_1649_);
                v___x_1666_ = crate::leanh::lean_apply_7(
                    v_a_1648_,
                    v___x_1665_,
                    v_a_1649_,
                    v_a_1650_,
                    v_a_1651_,
                    v_a_1652_,
                    v_a_1653_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___boxed(
    mut v_00_u03b1_1670_: *mut crate::leanh::LeanObject,
    mut v_lib_1671_: *mut crate::leanh::LeanObject,
    mut v_self_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_a_1674_: *mut crate::leanh::LeanObject,
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v_a_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1678_);
    crate::leanh::lean_dec(v_a_1677_);
    crate::leanh::lean_dec(v_a_1676_);
    crate::leanh::lean_dec(v_a_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Lake_LeanLib_fetchFacetJob(
    mut v_name_1682_: *mut crate::leanh::LeanObject,
    mut v_self_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1691_ = crate::leanh::lean_ctor_get(v_self_1683_, 0);
                v_name_1692_ = crate::leanh::lean_ctor_get(v_self_1683_, 1);
                v_keyName_1693_ = crate::leanh::lean_ctor_get(v_pkg_1691_, 2);
                v___x_1694_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1695_ = l_Lean_Name_append(v___x_1694_, v_name_1682_);
                crate::leanh::lean_inc(v_name_1692_);
                crate::leanh::lean_inc(v_keyName_1693_);
                v___x_1696_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1696_, 0, v_keyName_1693_);
                crate::leanh::lean_ctor_set(v___x_1696_, 1, v_name_1692_);
                v___x_1697_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1694_);
                crate::leanh::lean_ctor_set(v___x_1697_, 2, v_self_1683_);
                crate::leanh::lean_ctor_set(v___x_1697_, 3, v___x_1695_);
                crate::leanh::lean_inc_ref(v_a_1688_);
                crate::leanh::lean_inc(v_a_1687_);
                crate::leanh::lean_inc(v_a_1686_);
                crate::leanh::lean_inc(v_a_1685_);
                v___x_1698_ = crate::leanh::lean_apply_7(
                    v_a_1684_,
                    v___x_1697_,
                    v_a_1685_,
                    v_a_1686_,
                    v_a_1687_,
                    v_a_1688_,
                    v_a_1689_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1698_) == 0 {
                    v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1698_, 0);
                    v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1698_, 1);
                    v_isSharedCheck_1708_ = (!crate::leanh::lean_is_exclusive(v___x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v___x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1700_);
                        crate::leanh::lean_inc(v_a_1699_);
                        crate::leanh::lean_dec(v___x_1698_);
                        v___x_1702_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
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
    mut v_name_1709_: *mut crate::leanh::LeanObject,
    mut v_self_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1715_);
    crate::leanh::lean_dec(v_a_1714_);
    crate::leanh::lean_dec(v_a_1713_);
    crate::leanh::lean_dec(v_a_1712_);
    return v_res_1718_;
}
pub unsafe fn l_Lake_LeanExeDecl_get___redArg(
    mut v_self_1719_: *mut crate::leanh::LeanObject,
    mut v_inst_1720_: *mut crate::leanh::LeanObject,
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1723_ = crate::leanh::lean_ctor_get(v_inst_1720_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1723_);
    v_toFunctor_1724_ = crate::leanh::lean_ctor_get(v_toApplicative_1723_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1724_);
    v_toBind_1725_ = crate::leanh::lean_ctor_get(v_inst_1720_, 1);
    crate::leanh::lean_inc(v_toBind_1725_);
    crate::leanh::lean_dec_ref(v_inst_1720_);
    v_toPure_1726_ = crate::leanh::lean_ctor_get(v_toApplicative_1723_, 1);
    crate::leanh::lean_inc(v_toPure_1726_);
    crate::leanh::lean_dec_ref(v_toApplicative_1723_);
    v_pkg_1727_ = crate::leanh::lean_ctor_get(v_self_1719_, 0);
    crate::leanh::lean_inc_n(v_pkg_1727_, 2);
    v_name_1728_ = crate::leanh::lean_ctor_get(v_self_1719_, 1);
    crate::leanh::lean_inc(v_name_1728_);
    v_config_1729_ = crate::leanh::lean_ctor_get(v_self_1719_, 3);
    crate::leanh::lean_inc(v_config_1729_);
    crate::leanh::lean_dec_ref(v_self_1719_);
    v_map_1730_ = crate::leanh::lean_ctor_get(v_toFunctor_1724_, 0);
    crate::leanh::lean_inc_n(v_map_1730_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1724_);
    v___f_1731_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1732_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1732_, 0, v_name_1728_);
    crate::leanh::lean_closure_set(v___f_1732_, 1, v_config_1729_);
    crate::leanh::lean_closure_set(v___f_1732_, 2, v_toPure_1726_);
    crate::leanh::lean_closure_set(v___f_1732_, 3, v_pkg_1727_);
    crate::leanh::lean_closure_set(v___f_1732_, 4, v_inst_1721_);
    v___f_1733_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1733_, 0, v_pkg_1727_);
    v___x_1734_ = crate::leanh::lean_apply_4(
        v_map_1730_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1731_,
        v_inst_1722_,
    );
    v___x_1735_ = crate::leanh::lean_apply_4(
        v_map_1730_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1733_,
        v___x_1734_,
    );
    v___x_1736_ = crate::leanh::lean_apply_4(
        v_toBind_1725_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1735_,
        v___f_1732_,
    );
    return v___x_1736_;
}
pub unsafe fn l_Lake_LeanExeDecl_get(
    mut v_m_1737_: *mut crate::leanh::LeanObject,
    mut v_self_1738_: *mut crate::leanh::LeanObject,
    mut v_inst_1739_: *mut crate::leanh::LeanObject,
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1742_ = crate::leanh::lean_ctor_get(v_inst_1739_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1742_);
    v_toFunctor_1743_ = crate::leanh::lean_ctor_get(v_toApplicative_1742_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1743_);
    v_toBind_1744_ = crate::leanh::lean_ctor_get(v_inst_1739_, 1);
    crate::leanh::lean_inc(v_toBind_1744_);
    crate::leanh::lean_dec_ref(v_inst_1739_);
    v_toPure_1745_ = crate::leanh::lean_ctor_get(v_toApplicative_1742_, 1);
    crate::leanh::lean_inc(v_toPure_1745_);
    crate::leanh::lean_dec_ref(v_toApplicative_1742_);
    v_pkg_1746_ = crate::leanh::lean_ctor_get(v_self_1738_, 0);
    crate::leanh::lean_inc_n(v_pkg_1746_, 2);
    v_name_1747_ = crate::leanh::lean_ctor_get(v_self_1738_, 1);
    crate::leanh::lean_inc(v_name_1747_);
    v_config_1748_ = crate::leanh::lean_ctor_get(v_self_1738_, 3);
    crate::leanh::lean_inc(v_config_1748_);
    crate::leanh::lean_dec_ref(v_self_1738_);
    v_map_1749_ = crate::leanh::lean_ctor_get(v_toFunctor_1743_, 0);
    crate::leanh::lean_inc_n(v_map_1749_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1743_);
    v___f_1750_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1751_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1751_, 0, v_name_1747_);
    crate::leanh::lean_closure_set(v___f_1751_, 1, v_config_1748_);
    crate::leanh::lean_closure_set(v___f_1751_, 2, v_toPure_1745_);
    crate::leanh::lean_closure_set(v___f_1751_, 3, v_pkg_1746_);
    crate::leanh::lean_closure_set(v___f_1751_, 4, v_inst_1740_);
    v___f_1752_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1752_, 0, v_pkg_1746_);
    v___x_1753_ = crate::leanh::lean_apply_4(
        v_map_1749_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1750_,
        v_inst_1741_,
    );
    v___x_1754_ = crate::leanh::lean_apply_4(
        v_map_1749_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1752_,
        v___x_1753_,
    );
    v___x_1755_ = crate::leanh::lean_apply_4(
        v_toBind_1744_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1754_,
        v___f_1751_,
    );
    return v___x_1755_;
}
pub unsafe fn l_Lake_LeanExe_fetch(
    mut v_self_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1764_ = crate::leanh::lean_ctor_get(v_self_1756_, 0);
    v_name_1765_ = crate::leanh::lean_ctor_get(v_self_1756_, 1);
    v_keyName_1766_ = crate::leanh::lean_ctor_get(v_pkg_1764_, 2);
    v___x_1767_ = l_Lake_LeanExe_exeFacet;
    crate::leanh::lean_inc(v_name_1765_);
    crate::leanh::lean_inc(v_keyName_1766_);
    v___x_1768_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1768_, 0, v_keyName_1766_);
    crate::leanh::lean_ctor_set(v___x_1768_, 1, v_name_1765_);
    v___x_1769_ = l_Lake_LeanExe_keyword;
    v___x_1770_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1770_, 0, v___x_1768_);
    crate::leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
    crate::leanh::lean_ctor_set(v___x_1770_, 2, v_self_1756_);
    crate::leanh::lean_ctor_set(v___x_1770_, 3, v___x_1767_);
    crate::leanh::lean_inc_ref(v_a_1761_);
    crate::leanh::lean_inc(v_a_1760_);
    crate::leanh::lean_inc(v_a_1759_);
    crate::leanh::lean_inc(v_a_1758_);
    v___x_1771_ = crate::leanh::lean_apply_7(
        v_a_1757_,
        v___x_1770_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
        v_a_1761_,
        v_a_1762_,
        crate::leanh::lean_box(0),
    );
    return v___x_1771_;
}
pub unsafe fn l_Lake_LeanExe_fetch___boxed(
    mut v_self_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1780_ = l_Lake_LeanExe_fetch(
        v_self_1772_,
        v_a_1773_,
        v_a_1774_,
        v_a_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
    );
    crate::leanh::lean_dec_ref(v_a_1777_);
    crate::leanh::lean_dec(v_a_1776_);
    crate::leanh::lean_dec(v_a_1775_);
    crate::leanh::lean_dec(v_a_1774_);
    return v_res_1780_;
}
pub unsafe fn l_Lake_LeanExeDecl_fetch(
    mut v_self_1781_: *mut crate::leanh::LeanObject,
    mut v_a_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v_packageMap_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut v_unused_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1789_ = crate::leanh::lean_ctor_get(v_a_1786_, 1);
                v_pkg_1790_ = crate::leanh::lean_ctor_get(v_self_1781_, 0);
                v_name_1791_ = crate::leanh::lean_ctor_get(v_self_1781_, 1);
                v_config_1792_ = crate::leanh::lean_ctor_get(v_self_1781_, 3);
                v_isSharedCheck_1824_ = (!crate::leanh::lean_is_exclusive(v_self_1781_)) as u8;
                if v_isSharedCheck_1824_ == 0 {
                    v_unused_1825_ = crate::leanh::lean_ctor_get(v_self_1781_, 2);
                    crate::leanh::lean_dec(v_unused_1825_);
                    v___x_1794_ = v_self_1781_;
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_config_1792_);
                    crate::leanh::lean_inc(v_name_1791_);
                    crate::leanh::lean_inc(v_pkg_1790_);
                    crate::leanh::lean_dec(v_self_1781_);
                    v___x_1794_ = crate::leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1796_ = crate::leanh::lean_ctor_get(v_toContext_1789_, 5);
                v___x_1797_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                crate::leanh::lean_inc(v_pkg_1790_);
                crate::leanh::lean_inc(v_packageMap_1796_);
                v___x_1798_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1797_,
                    v_packageMap_1796_,
                    v_pkg_1790_,
                );
                if crate::leanh::lean_obj_tag(v___x_1798_) == 1 {
                    crate::leanh::lean_dec(v_pkg_1790_);
                    v_val_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                    crate::leanh::lean_inc(v_val_1799_);
                    crate::leanh::lean_dec_ref_known(v___x_1798_, 1);
                    v_keyName_1800_ = crate::leanh::lean_ctor_get(v_val_1799_, 2);
                    crate::leanh::lean_inc(v_keyName_1800_);
                    v___x_1801_ = l_Lake_LeanExe_keyword;
                    crate::leanh::lean_inc(v_name_1791_);
                    v___x_1802_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1802_, 0, v_val_1799_);
                    crate::leanh::lean_ctor_set(v___x_1802_, 1, v_name_1791_);
                    crate::leanh::lean_ctor_set(v___x_1802_, 2, v_config_1792_);
                    v___x_1803_ = l_Lake_LeanExe_exeFacet;
                    v___x_1804_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1804_, 0, v_keyName_1800_);
                    crate::leanh::lean_ctor_set(v___x_1804_, 1, v_name_1791_);
                    if v_isShared_1795_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1794_, 1);
                        crate::leanh::lean_ctor_set(v___x_1794_, 3, v___x_1803_);
                        crate::leanh::lean_ctor_set(v___x_1794_, 2, v___x_1802_);
                        crate::leanh::lean_ctor_set(v___x_1794_, 1, v___x_1801_);
                        crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1804_);
                        v___x_1806_ = v___x_1794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1801_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 2, v___x_1802_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 3, v___x_1803_);
                        v___x_1806_ = v_reuseFailAlloc_1808_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1798_);
                    crate::leanh::lean_del_object(v___x_1794_);
                    crate::leanh::lean_dec(v_config_1792_);
                    crate::leanh::lean_dec_ref(v_a_1782_);
                    v___x_1809_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1810_ = 1;
                    v___x_1811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1790_,
                        v___x_1810_,
                    );
                    v___x_1812_ = lean_string_append(v___x_1809_, v___x_1811_);
                    crate::leanh::lean_dec_ref(v___x_1811_);
                    v___x_1813_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1814_ = lean_string_append(v___x_1812_, v___x_1813_);
                    v___x_1815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1791_,
                        v___x_1810_,
                    );
                    v___x_1816_ = lean_string_append(v___x_1814_, v___x_1815_);
                    crate::leanh::lean_dec_ref(v___x_1815_);
                    v___x_1817_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
                    v___x_1819_ = 3;
                    v___x_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1818_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1820_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1819_,
                    );
                    v___x_1821_ = lean_array_get_size(v_a_1787_);
                    v___x_1822_ = lean_array_push(v_a_1787_, v___x_1820_);
                    v___x_1823_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1823_, 0, v___x_1821_);
                    crate::leanh::lean_ctor_set(v___x_1823_, 1, v___x_1822_);
                    return v___x_1823_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_1786_);
                crate::leanh::lean_inc(v_a_1785_);
                crate::leanh::lean_inc(v_a_1784_);
                crate::leanh::lean_inc(v_a_1783_);
                v___x_1807_ = crate::leanh::lean_apply_7(
                    v_a_1782_,
                    v___x_1806_,
                    v_a_1783_,
                    v_a_1784_,
                    v_a_1785_,
                    v_a_1786_,
                    v_a_1787_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeDecl_fetch___boxed(
    mut v_self_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lake_LeanExeDecl_fetch(
        v_self_1826_,
        v_a_1827_,
        v_a_1828_,
        v_a_1829_,
        v_a_1830_,
        v_a_1831_,
        v_a_1832_,
    );
    crate::leanh::lean_dec_ref(v_a_1831_);
    crate::leanh::lean_dec(v_a_1830_);
    crate::leanh::lean_dec(v_a_1829_);
    crate::leanh::lean_dec(v_a_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lake_InputFile_fetch(
    mut v_self_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1843_ = crate::leanh::lean_ctor_get(v_self_1835_, 0);
    v_name_1844_ = crate::leanh::lean_ctor_get(v_self_1835_, 1);
    v_keyName_1845_ = crate::leanh::lean_ctor_get(v_pkg_1843_, 2);
    v___x_1846_ = l_Lake_InputFile_defaultFacet;
    crate::leanh::lean_inc(v_name_1844_);
    crate::leanh::lean_inc(v_keyName_1845_);
    v___x_1847_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1847_, 0, v_keyName_1845_);
    crate::leanh::lean_ctor_set(v___x_1847_, 1, v_name_1844_);
    v___x_1848_ = l_Lake_InputFile_keyword;
    v___x_1849_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1847_);
    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1849_, 2, v_self_1835_);
    crate::leanh::lean_ctor_set(v___x_1849_, 3, v___x_1846_);
    crate::leanh::lean_inc_ref(v_a_1840_);
    crate::leanh::lean_inc(v_a_1839_);
    crate::leanh::lean_inc(v_a_1838_);
    crate::leanh::lean_inc(v_a_1837_);
    v___x_1850_ = crate::leanh::lean_apply_7(
        v_a_1836_,
        v___x_1849_,
        v_a_1837_,
        v_a_1838_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
        crate::leanh::lean_box(0),
    );
    return v___x_1850_;
}
pub unsafe fn l_Lake_InputFile_fetch___boxed(
    mut v_self_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lake_InputFile_fetch(
        v_self_1851_,
        v_a_1852_,
        v_a_1853_,
        v_a_1854_,
        v_a_1855_,
        v_a_1856_,
        v_a_1857_,
    );
    crate::leanh::lean_dec_ref(v_a_1856_);
    crate::leanh::lean_dec(v_a_1855_);
    crate::leanh::lean_dec(v_a_1854_);
    crate::leanh::lean_dec(v_a_1853_);
    return v_res_1859_;
}
pub unsafe fn l_Lake_InputFileDecl_get___redArg(
    mut v_self_1860_: *mut crate::leanh::LeanObject,
    mut v_inst_1861_: *mut crate::leanh::LeanObject,
    mut v_inst_1862_: *mut crate::leanh::LeanObject,
    mut v_inst_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = crate::leanh::lean_ctor_get(v_inst_1861_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1864_);
    v_toFunctor_1865_ = crate::leanh::lean_ctor_get(v_toApplicative_1864_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1865_);
    v_toBind_1866_ = crate::leanh::lean_ctor_get(v_inst_1861_, 1);
    crate::leanh::lean_inc(v_toBind_1866_);
    crate::leanh::lean_dec_ref(v_inst_1861_);
    v_toPure_1867_ = crate::leanh::lean_ctor_get(v_toApplicative_1864_, 1);
    crate::leanh::lean_inc(v_toPure_1867_);
    crate::leanh::lean_dec_ref(v_toApplicative_1864_);
    v_pkg_1868_ = crate::leanh::lean_ctor_get(v_self_1860_, 0);
    crate::leanh::lean_inc_n(v_pkg_1868_, 2);
    v_name_1869_ = crate::leanh::lean_ctor_get(v_self_1860_, 1);
    crate::leanh::lean_inc(v_name_1869_);
    v_config_1870_ = crate::leanh::lean_ctor_get(v_self_1860_, 3);
    crate::leanh::lean_inc(v_config_1870_);
    crate::leanh::lean_dec_ref(v_self_1860_);
    v_map_1871_ = crate::leanh::lean_ctor_get(v_toFunctor_1865_, 0);
    crate::leanh::lean_inc_n(v_map_1871_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1865_);
    v___f_1872_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1873_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1873_, 0, v_name_1869_);
    crate::leanh::lean_closure_set(v___f_1873_, 1, v_config_1870_);
    crate::leanh::lean_closure_set(v___f_1873_, 2, v_toPure_1867_);
    crate::leanh::lean_closure_set(v___f_1873_, 3, v_pkg_1868_);
    crate::leanh::lean_closure_set(v___f_1873_, 4, v_inst_1862_);
    v___f_1874_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1874_, 0, v_pkg_1868_);
    v___x_1875_ = crate::leanh::lean_apply_4(
        v_map_1871_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1872_,
        v_inst_1863_,
    );
    v___x_1876_ = crate::leanh::lean_apply_4(
        v_map_1871_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1874_,
        v___x_1875_,
    );
    v___x_1877_ = crate::leanh::lean_apply_4(
        v_toBind_1866_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1876_,
        v___f_1873_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lake_InputFileDecl_get(
    mut v_m_1878_: *mut crate::leanh::LeanObject,
    mut v_self_1879_: *mut crate::leanh::LeanObject,
    mut v_inst_1880_: *mut crate::leanh::LeanObject,
    mut v_inst_1881_: *mut crate::leanh::LeanObject,
    mut v_inst_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1883_ = crate::leanh::lean_ctor_get(v_inst_1880_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1883_);
    v_toFunctor_1884_ = crate::leanh::lean_ctor_get(v_toApplicative_1883_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1884_);
    v_toBind_1885_ = crate::leanh::lean_ctor_get(v_inst_1880_, 1);
    crate::leanh::lean_inc(v_toBind_1885_);
    crate::leanh::lean_dec_ref(v_inst_1880_);
    v_toPure_1886_ = crate::leanh::lean_ctor_get(v_toApplicative_1883_, 1);
    crate::leanh::lean_inc(v_toPure_1886_);
    crate::leanh::lean_dec_ref(v_toApplicative_1883_);
    v_pkg_1887_ = crate::leanh::lean_ctor_get(v_self_1879_, 0);
    crate::leanh::lean_inc_n(v_pkg_1887_, 2);
    v_name_1888_ = crate::leanh::lean_ctor_get(v_self_1879_, 1);
    crate::leanh::lean_inc(v_name_1888_);
    v_config_1889_ = crate::leanh::lean_ctor_get(v_self_1879_, 3);
    crate::leanh::lean_inc(v_config_1889_);
    crate::leanh::lean_dec_ref(v_self_1879_);
    v_map_1890_ = crate::leanh::lean_ctor_get(v_toFunctor_1884_, 0);
    crate::leanh::lean_inc_n(v_map_1890_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1884_);
    v___f_1891_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1892_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1892_, 0, v_name_1888_);
    crate::leanh::lean_closure_set(v___f_1892_, 1, v_config_1889_);
    crate::leanh::lean_closure_set(v___f_1892_, 2, v_toPure_1886_);
    crate::leanh::lean_closure_set(v___f_1892_, 3, v_pkg_1887_);
    crate::leanh::lean_closure_set(v___f_1892_, 4, v_inst_1881_);
    v___f_1893_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1893_, 0, v_pkg_1887_);
    v___x_1894_ = crate::leanh::lean_apply_4(
        v_map_1890_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1891_,
        v_inst_1882_,
    );
    v___x_1895_ = crate::leanh::lean_apply_4(
        v_map_1890_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1893_,
        v___x_1894_,
    );
    v___x_1896_ = crate::leanh::lean_apply_4(
        v_toBind_1885_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1895_,
        v___f_1892_,
    );
    return v___x_1896_;
}
pub unsafe fn l_Lake_InputFileDecl_fetch(
    mut v_self_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v_packageMap_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1905_ = crate::leanh::lean_ctor_get(v_a_1902_, 1);
                v_pkg_1906_ = crate::leanh::lean_ctor_get(v_self_1897_, 0);
                v_name_1907_ = crate::leanh::lean_ctor_get(v_self_1897_, 1);
                v_config_1908_ = crate::leanh::lean_ctor_get(v_self_1897_, 3);
                v_isSharedCheck_1940_ = (!crate::leanh::lean_is_exclusive(v_self_1897_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v_unused_1941_ = crate::leanh::lean_ctor_get(v_self_1897_, 2);
                    crate::leanh::lean_dec(v_unused_1941_);
                    v___x_1910_ = v_self_1897_;
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_config_1908_);
                    crate::leanh::lean_inc(v_name_1907_);
                    crate::leanh::lean_inc(v_pkg_1906_);
                    crate::leanh::lean_dec(v_self_1897_);
                    v___x_1910_ = crate::leanh::lean_box(0);
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1912_ = crate::leanh::lean_ctor_get(v_toContext_1905_, 5);
                v___x_1913_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                crate::leanh::lean_inc(v_pkg_1906_);
                crate::leanh::lean_inc(v_packageMap_1912_);
                v___x_1914_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1913_,
                    v_packageMap_1912_,
                    v_pkg_1906_,
                );
                if crate::leanh::lean_obj_tag(v___x_1914_) == 1 {
                    crate::leanh::lean_dec(v_pkg_1906_);
                    v_val_1915_ = crate::leanh::lean_ctor_get(v___x_1914_, 0);
                    crate::leanh::lean_inc(v_val_1915_);
                    crate::leanh::lean_dec_ref_known(v___x_1914_, 1);
                    v_keyName_1916_ = crate::leanh::lean_ctor_get(v_val_1915_, 2);
                    crate::leanh::lean_inc(v_keyName_1916_);
                    v___x_1917_ = l_Lake_InputFile_keyword;
                    crate::leanh::lean_inc(v_name_1907_);
                    v___x_1918_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1918_, 0, v_val_1915_);
                    crate::leanh::lean_ctor_set(v___x_1918_, 1, v_name_1907_);
                    crate::leanh::lean_ctor_set(v___x_1918_, 2, v_config_1908_);
                    v___x_1919_ = l_Lake_InputFile_defaultFacet;
                    v___x_1920_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1920_, 0, v_keyName_1916_);
                    crate::leanh::lean_ctor_set(v___x_1920_, 1, v_name_1907_);
                    if v_isShared_1911_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1910_, 1);
                        crate::leanh::lean_ctor_set(v___x_1910_, 3, v___x_1919_);
                        crate::leanh::lean_ctor_set(v___x_1910_, 2, v___x_1918_);
                        crate::leanh::lean_ctor_set(v___x_1910_, 1, v___x_1917_);
                        crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1920_);
                        v___x_1922_ = v___x_1910_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1920_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 2, v___x_1918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 3, v___x_1919_);
                        v___x_1922_ = v_reuseFailAlloc_1924_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1914_);
                    crate::leanh::lean_del_object(v___x_1910_);
                    crate::leanh::lean_dec(v_config_1908_);
                    crate::leanh::lean_dec_ref(v_a_1898_);
                    v___x_1925_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1926_ = 1;
                    v___x_1927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1906_,
                        v___x_1926_,
                    );
                    v___x_1928_ = lean_string_append(v___x_1925_, v___x_1927_);
                    crate::leanh::lean_dec_ref(v___x_1927_);
                    v___x_1929_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
                    v___x_1931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1907_,
                        v___x_1926_,
                    );
                    v___x_1932_ = lean_string_append(v___x_1930_, v___x_1931_);
                    crate::leanh::lean_dec_ref(v___x_1931_);
                    v___x_1933_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1934_ = lean_string_append(v___x_1932_, v___x_1933_);
                    v___x_1935_ = 3;
                    v___x_1936_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1936_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1935_,
                    );
                    v___x_1937_ = lean_array_get_size(v_a_1903_);
                    v___x_1938_ = lean_array_push(v_a_1903_, v___x_1936_);
                    v___x_1939_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1937_);
                    crate::leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                    return v___x_1939_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_1902_);
                crate::leanh::lean_inc(v_a_1901_);
                crate::leanh::lean_inc(v_a_1900_);
                crate::leanh::lean_inc(v_a_1899_);
                v___x_1923_ = crate::leanh::lean_apply_7(
                    v_a_1898_,
                    v___x_1922_,
                    v_a_1899_,
                    v_a_1900_,
                    v_a_1901_,
                    v_a_1902_,
                    v_a_1903_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileDecl_fetch___boxed(
    mut v_self_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
    mut v_a_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lake_InputFileDecl_fetch(
        v_self_1942_,
        v_a_1943_,
        v_a_1944_,
        v_a_1945_,
        v_a_1946_,
        v_a_1947_,
        v_a_1948_,
    );
    crate::leanh::lean_dec_ref(v_a_1947_);
    crate::leanh::lean_dec(v_a_1946_);
    crate::leanh::lean_dec(v_a_1945_);
    crate::leanh::lean_dec(v_a_1944_);
    return v_res_1950_;
}
pub unsafe fn l_Lake_InputDir_fetch(
    mut v_self_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
    mut v_a_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1959_ = crate::leanh::lean_ctor_get(v_self_1951_, 0);
    v_name_1960_ = crate::leanh::lean_ctor_get(v_self_1951_, 1);
    v_keyName_1961_ = crate::leanh::lean_ctor_get(v_pkg_1959_, 2);
    v___x_1962_ = l_Lake_InputDir_defaultFacet;
    crate::leanh::lean_inc(v_name_1960_);
    crate::leanh::lean_inc(v_keyName_1961_);
    v___x_1963_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1963_, 0, v_keyName_1961_);
    crate::leanh::lean_ctor_set(v___x_1963_, 1, v_name_1960_);
    v___x_1964_ = l_Lake_InputDir_keyword;
    v___x_1965_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1963_);
    crate::leanh::lean_ctor_set(v___x_1965_, 1, v___x_1964_);
    crate::leanh::lean_ctor_set(v___x_1965_, 2, v_self_1951_);
    crate::leanh::lean_ctor_set(v___x_1965_, 3, v___x_1962_);
    crate::leanh::lean_inc_ref(v_a_1956_);
    crate::leanh::lean_inc(v_a_1955_);
    crate::leanh::lean_inc(v_a_1954_);
    crate::leanh::lean_inc(v_a_1953_);
    v___x_1966_ = crate::leanh::lean_apply_7(
        v_a_1952_,
        v___x_1965_,
        v_a_1953_,
        v_a_1954_,
        v_a_1955_,
        v_a_1956_,
        v_a_1957_,
        crate::leanh::lean_box(0),
    );
    return v___x_1966_;
}
pub unsafe fn l_Lake_InputDir_fetch___boxed(
    mut v_self_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lake_InputDir_fetch(
        v_self_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
    );
    crate::leanh::lean_dec_ref(v_a_1972_);
    crate::leanh::lean_dec(v_a_1971_);
    crate::leanh::lean_dec(v_a_1970_);
    crate::leanh::lean_dec(v_a_1969_);
    return v_res_1975_;
}
pub unsafe fn l_Lake_InputDirDecl_get___redArg(
    mut v_self_1976_: *mut crate::leanh::LeanObject,
    mut v_inst_1977_: *mut crate::leanh::LeanObject,
    mut v_inst_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1980_ = crate::leanh::lean_ctor_get(v_inst_1977_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1980_);
    v_toFunctor_1981_ = crate::leanh::lean_ctor_get(v_toApplicative_1980_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1981_);
    v_toBind_1982_ = crate::leanh::lean_ctor_get(v_inst_1977_, 1);
    crate::leanh::lean_inc(v_toBind_1982_);
    crate::leanh::lean_dec_ref(v_inst_1977_);
    v_toPure_1983_ = crate::leanh::lean_ctor_get(v_toApplicative_1980_, 1);
    crate::leanh::lean_inc(v_toPure_1983_);
    crate::leanh::lean_dec_ref(v_toApplicative_1980_);
    v_pkg_1984_ = crate::leanh::lean_ctor_get(v_self_1976_, 0);
    crate::leanh::lean_inc_n(v_pkg_1984_, 2);
    v_name_1985_ = crate::leanh::lean_ctor_get(v_self_1976_, 1);
    crate::leanh::lean_inc(v_name_1985_);
    v_config_1986_ = crate::leanh::lean_ctor_get(v_self_1976_, 3);
    crate::leanh::lean_inc(v_config_1986_);
    crate::leanh::lean_dec_ref(v_self_1976_);
    v_map_1987_ = crate::leanh::lean_ctor_get(v_toFunctor_1981_, 0);
    crate::leanh::lean_inc_n(v_map_1987_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_1981_);
    v___f_1988_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1989_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1989_, 0, v_name_1985_);
    crate::leanh::lean_closure_set(v___f_1989_, 1, v_config_1986_);
    crate::leanh::lean_closure_set(v___f_1989_, 2, v_toPure_1983_);
    crate::leanh::lean_closure_set(v___f_1989_, 3, v_pkg_1984_);
    crate::leanh::lean_closure_set(v___f_1989_, 4, v_inst_1978_);
    v___f_1990_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1990_, 0, v_pkg_1984_);
    v___x_1991_ = crate::leanh::lean_apply_4(
        v_map_1987_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1988_,
        v_inst_1979_,
    );
    v___x_1992_ = crate::leanh::lean_apply_4(
        v_map_1987_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1990_,
        v___x_1991_,
    );
    v___x_1993_ = crate::leanh::lean_apply_4(
        v_toBind_1982_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1992_,
        v___f_1989_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_InputDirDecl_get(
    mut v_m_1994_: *mut crate::leanh::LeanObject,
    mut v_self_1995_: *mut crate::leanh::LeanObject,
    mut v_inst_1996_: *mut crate::leanh::LeanObject,
    mut v_inst_1997_: *mut crate::leanh::LeanObject,
    mut v_inst_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1999_ = crate::leanh::lean_ctor_get(v_inst_1996_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1999_);
    v_toFunctor_2000_ = crate::leanh::lean_ctor_get(v_toApplicative_1999_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2000_);
    v_toBind_2001_ = crate::leanh::lean_ctor_get(v_inst_1996_, 1);
    crate::leanh::lean_inc(v_toBind_2001_);
    crate::leanh::lean_dec_ref(v_inst_1996_);
    v_toPure_2002_ = crate::leanh::lean_ctor_get(v_toApplicative_1999_, 1);
    crate::leanh::lean_inc(v_toPure_2002_);
    crate::leanh::lean_dec_ref(v_toApplicative_1999_);
    v_pkg_2003_ = crate::leanh::lean_ctor_get(v_self_1995_, 0);
    crate::leanh::lean_inc_n(v_pkg_2003_, 2);
    v_name_2004_ = crate::leanh::lean_ctor_get(v_self_1995_, 1);
    crate::leanh::lean_inc(v_name_2004_);
    v_config_2005_ = crate::leanh::lean_ctor_get(v_self_1995_, 3);
    crate::leanh::lean_inc(v_config_2005_);
    crate::leanh::lean_dec_ref(v_self_1995_);
    v_map_2006_ = crate::leanh::lean_ctor_get(v_toFunctor_2000_, 0);
    crate::leanh::lean_inc_n(v_map_2006_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_2000_);
    v___f_2007_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_2008_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2008_, 0, v_name_2004_);
    crate::leanh::lean_closure_set(v___f_2008_, 1, v_config_2005_);
    crate::leanh::lean_closure_set(v___f_2008_, 2, v_toPure_2002_);
    crate::leanh::lean_closure_set(v___f_2008_, 3, v_pkg_2003_);
    crate::leanh::lean_closure_set(v___f_2008_, 4, v_inst_1997_);
    v___f_2009_ = crate::leanh::lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2009_, 0, v_pkg_2003_);
    v___x_2010_ = crate::leanh::lean_apply_4(
        v_map_2006_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2007_,
        v_inst_1998_,
    );
    v___x_2011_ = crate::leanh::lean_apply_4(
        v_map_2006_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2009_,
        v___x_2010_,
    );
    v___x_2012_ = crate::leanh::lean_apply_4(
        v_toBind_2001_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2011_,
        v___f_2008_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_InputDirDecl_fetch(
    mut v_self_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v_packageMap_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_2021_ = crate::leanh::lean_ctor_get(v_a_2018_, 1);
                v_pkg_2022_ = crate::leanh::lean_ctor_get(v_self_2013_, 0);
                v_name_2023_ = crate::leanh::lean_ctor_get(v_self_2013_, 1);
                v_config_2024_ = crate::leanh::lean_ctor_get(v_self_2013_, 3);
                v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v_self_2013_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = crate::leanh::lean_ctor_get(v_self_2013_, 2);
                    crate::leanh::lean_dec(v_unused_2057_);
                    v___x_2026_ = v_self_2013_;
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_config_2024_);
                    crate::leanh::lean_inc(v_name_2023_);
                    crate::leanh::lean_inc(v_pkg_2022_);
                    crate::leanh::lean_dec(v_self_2013_);
                    v___x_2026_ = crate::leanh::lean_box(0);
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_2028_ = crate::leanh::lean_ctor_get(v_toContext_2021_, 5);
                v___x_2029_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                crate::leanh::lean_inc(v_pkg_2022_);
                crate::leanh::lean_inc(v_packageMap_2028_);
                v___x_2030_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_2029_,
                    v_packageMap_2028_,
                    v_pkg_2022_,
                );
                if crate::leanh::lean_obj_tag(v___x_2030_) == 1 {
                    crate::leanh::lean_dec(v_pkg_2022_);
                    v_val_2031_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                    crate::leanh::lean_inc(v_val_2031_);
                    crate::leanh::lean_dec_ref_known(v___x_2030_, 1);
                    v_keyName_2032_ = crate::leanh::lean_ctor_get(v_val_2031_, 2);
                    crate::leanh::lean_inc(v_keyName_2032_);
                    v___x_2033_ = l_Lake_InputDir_keyword;
                    crate::leanh::lean_inc(v_name_2023_);
                    v___x_2034_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2034_, 0, v_val_2031_);
                    crate::leanh::lean_ctor_set(v___x_2034_, 1, v_name_2023_);
                    crate::leanh::lean_ctor_set(v___x_2034_, 2, v_config_2024_);
                    v___x_2035_ = l_Lake_InputDir_defaultFacet;
                    v___x_2036_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2036_, 0, v_keyName_2032_);
                    crate::leanh::lean_ctor_set(v___x_2036_, 1, v_name_2023_);
                    if v_isShared_2027_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2026_, 1);
                        crate::leanh::lean_ctor_set(v___x_2026_, 3, v___x_2035_);
                        crate::leanh::lean_ctor_set(v___x_2026_, 2, v___x_2034_);
                        crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2033_);
                        crate::leanh::lean_ctor_set(v___x_2026_, 0, v___x_2036_);
                        v___x_2038_ = v___x_2026_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2040_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2033_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 2, v___x_2034_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 3, v___x_2035_);
                        v___x_2038_ = v_reuseFailAlloc_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2030_);
                    crate::leanh::lean_del_object(v___x_2026_);
                    crate::leanh::lean_dec(v_config_2024_);
                    crate::leanh::lean_dec_ref(v_a_2014_);
                    v___x_2041_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_2042_ = 1;
                    v___x_2043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_2022_,
                        v___x_2042_,
                    );
                    v___x_2044_ = lean_string_append(v___x_2041_, v___x_2043_);
                    crate::leanh::lean_dec_ref(v___x_2043_);
                    v___x_2045_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
                    v___x_2047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2023_,
                        v___x_2042_,
                    );
                    v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
                    crate::leanh::lean_dec_ref(v___x_2047_);
                    v___x_2049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
                    v___x_2051_ = 3;
                    v___x_2052_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2050_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2052_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2051_,
                    );
                    v___x_2053_ = lean_array_get_size(v_a_2019_);
                    v___x_2054_ = lean_array_push(v_a_2019_, v___x_2052_);
                    v___x_2055_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2053_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 1, v___x_2054_);
                    return v___x_2055_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_2018_);
                crate::leanh::lean_inc(v_a_2017_);
                crate::leanh::lean_inc(v_a_2016_);
                crate::leanh::lean_inc(v_a_2015_);
                v___x_2039_ = crate::leanh::lean_apply_7(
                    v_a_2014_,
                    v___x_2038_,
                    v_a_2015_,
                    v_a_2016_,
                    v_a_2017_,
                    v_a_2018_,
                    v_a_2019_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirDecl_fetch___boxed(
    mut v_self_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lake_InputDirDecl_fetch(
        v_self_2058_,
        v_a_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
        v_a_2064_,
    );
    crate::leanh::lean_dec_ref(v_a_2063_);
    crate::leanh::lean_dec(v_a_2062_);
    crate::leanh::lean_dec(v_a_2061_);
    crate::leanh::lean_dec(v_a_2060_);
    return v_res_2066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Targets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Targets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Targets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Targets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Targets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Targets(builtin);
}
