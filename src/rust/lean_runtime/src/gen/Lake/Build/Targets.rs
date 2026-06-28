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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            112, 97, 99, 107, 97, 103, 101, 32, 111, 102, 32, 116, 97, 114, 103, 101, 116, 32, 39,
            0,
        ],
    };
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 119, 111, 114,
            107, 115, 112, 97, 99, 101, 0,
        ],
    };
static mut l_Lake_KConfigDecl_get___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_KConfigDecl_get___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_KConfigDecl_get___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_KConfigDecl_get___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_KConfigDecl_get___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_KConfigDecl_get___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_TargetDecl_fetch___redArg___closed__2_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_TargetDecl_fetch___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_TargetDecl_fetch___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanLib_fetch___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LeanLib_fetch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_fetch___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__0_value) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanLib_fetch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_fetch___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0(
    mut v_x_1034_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1034_);
    return v_x_1034_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__0___boxed(
    mut v_x_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lake_KConfigDecl_get___redArg___lam__0(v_x_1035_);
    lean_dec(v_x_1035_);
    return v_res_1036_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1(
    mut v_name_1040_: *mut LeanObject,
    mut v_config_1041_: *mut LeanObject,
    mut v_toPure_1042_: *mut LeanObject,
    mut v_pkg_1043_: *mut LeanObject,
    mut v_inst_1044_: *mut LeanObject,
    mut v_____x_1045_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_1045_) == 1 {
        let mut v_val_1046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1044_);
        lean_dec(v_pkg_1043_);
        v_val_1046_ = lean_ctor_get(v_____x_1045_, 0);
        lean_inc(v_val_1046_);
        v___x_1047_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_1047_, 0, v_val_1046_);
        lean_ctor_set(v___x_1047_, 1, v_name_1040_);
        lean_ctor_set(v___x_1047_, 2, v_config_1041_);
        v___x_1048_ = lean_apply_2(v_toPure_1042_, lean_box(0), v___x_1047_);
        return v___x_1048_;
    } else {
        let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: u8 = 0;
        let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1042_);
        lean_dec(v_config_1041_);
        v___x_1049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
        v___x_1050_ = 1;
        v___x_1051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1043_,
            v___x_1050_,
        );
        v___x_1052_ = lean_string_append(v___x_1049_, v___x_1051_);
        lean_dec_ref(v___x_1051_);
        v___x_1053_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
        v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
        v___x_1055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1040_,
            v___x_1050_,
        );
        v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
        lean_dec_ref(v___x_1055_);
        v___x_1057_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
        v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
        v___x_1059_ = lean_apply_2(v_inst_1044_, lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__1___boxed(
    mut v_name_1060_: *mut LeanObject,
    mut v_config_1061_: *mut LeanObject,
    mut v_toPure_1062_: *mut LeanObject,
    mut v_pkg_1063_: *mut LeanObject,
    mut v_inst_1064_: *mut LeanObject,
    mut v_____x_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lake_KConfigDecl_get___redArg___lam__1(
        v_name_1060_,
        v_config_1061_,
        v_toPure_1062_,
        v_pkg_1063_,
        v_inst_1064_,
        v_____x_1065_,
    );
    lean_dec(v_____x_1065_);
    return v_res_1066_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg___lam__2(
    mut v_pkg_1068_: *mut LeanObject,
    mut v_x_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_packageMap_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v_packageMap_1070_ = lean_ctor_get(v_x_1069_, 5);
    lean_inc(v_packageMap_1070_);
    lean_dec_ref(v_x_1069_);
    v___x_1071_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    v___x_1072_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1071_, v_packageMap_1070_, v_pkg_1068_);
    return v___x_1072_;
}
pub unsafe fn l_Lake_KConfigDecl_get___redArg(
    mut v_inst_1074_: *mut LeanObject,
    mut v_inst_1075_: *mut LeanObject,
    mut v_inst_1076_: *mut LeanObject,
    mut v_self_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1078_ = lean_ctor_get(v_inst_1074_, 0);
    lean_inc_ref(v_toApplicative_1078_);
    v_toFunctor_1079_ = lean_ctor_get(v_toApplicative_1078_, 0);
    lean_inc_ref(v_toFunctor_1079_);
    v_toBind_1080_ = lean_ctor_get(v_inst_1074_, 1);
    lean_inc(v_toBind_1080_);
    lean_dec_ref(v_inst_1074_);
    v_toPure_1081_ = lean_ctor_get(v_toApplicative_1078_, 1);
    lean_inc(v_toPure_1081_);
    lean_dec_ref(v_toApplicative_1078_);
    v_pkg_1082_ = lean_ctor_get(v_self_1077_, 0);
    lean_inc_n(v_pkg_1082_, 2);
    v_name_1083_ = lean_ctor_get(v_self_1077_, 1);
    lean_inc(v_name_1083_);
    v_config_1084_ = lean_ctor_get(v_self_1077_, 3);
    lean_inc(v_config_1084_);
    lean_dec_ref(v_self_1077_);
    v_map_1085_ = lean_ctor_get(v_toFunctor_1079_, 0);
    lean_inc_n(v_map_1085_, 2);
    lean_dec_ref(v_toFunctor_1079_);
    v___f_1086_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1087_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1087_, 0, v_name_1083_);
    lean_closure_set(v___f_1087_, 1, v_config_1084_);
    lean_closure_set(v___f_1087_, 2, v_toPure_1081_);
    lean_closure_set(v___f_1087_, 3, v_pkg_1082_);
    lean_closure_set(v___f_1087_, 4, v_inst_1075_);
    v___f_1088_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1088_, 0, v_pkg_1082_);
    v___x_1089_ = lean_apply_4(
        v_map_1085_,
        lean_box(0),
        lean_box(0),
        v___f_1086_,
        v_inst_1076_,
    );
    v___x_1090_ = lean_apply_4(
        v_map_1085_,
        lean_box(0),
        lean_box(0),
        v___f_1088_,
        v___x_1089_,
    );
    v___x_1091_ = lean_apply_4(
        v_toBind_1080_,
        lean_box(0),
        lean_box(0),
        v___x_1090_,
        v___f_1087_,
    );
    return v___x_1091_;
}
pub unsafe fn l_Lake_KConfigDecl_get(
    mut v_m_1092_: *mut LeanObject,
    mut v_kind_1093_: *mut LeanObject,
    mut v_inst_1094_: *mut LeanObject,
    mut v_inst_1095_: *mut LeanObject,
    mut v_inst_1096_: *mut LeanObject,
    mut v_self_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = lean_ctor_get(v_inst_1094_, 0);
    lean_inc_ref(v_toApplicative_1098_);
    v_toFunctor_1099_ = lean_ctor_get(v_toApplicative_1098_, 0);
    lean_inc_ref(v_toFunctor_1099_);
    v_toBind_1100_ = lean_ctor_get(v_inst_1094_, 1);
    lean_inc(v_toBind_1100_);
    lean_dec_ref(v_inst_1094_);
    v_toPure_1101_ = lean_ctor_get(v_toApplicative_1098_, 1);
    lean_inc(v_toPure_1101_);
    lean_dec_ref(v_toApplicative_1098_);
    v_pkg_1102_ = lean_ctor_get(v_self_1097_, 0);
    lean_inc_n(v_pkg_1102_, 2);
    v_name_1103_ = lean_ctor_get(v_self_1097_, 1);
    lean_inc(v_name_1103_);
    v_config_1104_ = lean_ctor_get(v_self_1097_, 3);
    lean_inc(v_config_1104_);
    lean_dec_ref(v_self_1097_);
    v_map_1105_ = lean_ctor_get(v_toFunctor_1099_, 0);
    lean_inc_n(v_map_1105_, 2);
    lean_dec_ref(v_toFunctor_1099_);
    v___f_1106_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1107_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1107_, 0, v_name_1103_);
    lean_closure_set(v___f_1107_, 1, v_config_1104_);
    lean_closure_set(v___f_1107_, 2, v_toPure_1101_);
    lean_closure_set(v___f_1107_, 3, v_pkg_1102_);
    lean_closure_set(v___f_1107_, 4, v_inst_1095_);
    v___f_1108_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1108_, 0, v_pkg_1102_);
    v___x_1109_ = lean_apply_4(
        v_map_1105_,
        lean_box(0),
        lean_box(0),
        v___f_1106_,
        v_inst_1096_,
    );
    v___x_1110_ = lean_apply_4(
        v_map_1105_,
        lean_box(0),
        lean_box(0),
        v___f_1108_,
        v___x_1109_,
    );
    v___x_1111_ = lean_apply_4(
        v_toBind_1100_,
        lean_box(0),
        lean_box(0),
        v___x_1110_,
        v___f_1107_,
    );
    return v___x_1111_;
}
pub unsafe fn l_Lake_KConfigDecl_get___boxed(
    mut v_m_1112_: *mut LeanObject,
    mut v_kind_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_inst_1116_: *mut LeanObject,
    mut v_self_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1118_: *mut LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lake_KConfigDecl_get(
        v_m_1112_,
        v_kind_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_inst_1116_,
        v_self_1117_,
    );
    lean_dec(v_kind_1113_);
    return v_res_1118_;
}
pub unsafe fn l_Lake_Package_fetchTargetJob(
    mut v_self_1119_: *mut LeanObject,
    mut v_target_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1128_, 0, v_self_1119_);
                lean_ctor_set(v___x_1128_, 1, v_target_1120_);
                lean_inc_ref(v_a_1125_);
                lean_inc(v_a_1124_);
                lean_inc(v_a_1123_);
                lean_inc(v_a_1122_);
                v___x_1129_ = lean_apply_7(
                    v_a_1121_,
                    v___x_1128_,
                    v_a_1122_,
                    v_a_1123_,
                    v_a_1124_,
                    v_a_1125_,
                    v_a_1126_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1129_) == 0 {
                    v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
                    v_a_1131_ = lean_ctor_get(v___x_1129_, 1);
                    v_isSharedCheck_1139_ = (!lean_is_exclusive(v___x_1129_)) as u8;
                    if v_isSharedCheck_1139_ == 0 {
                        v___x_1133_ = v___x_1129_;
                        v_isShared_1134_ = v_isSharedCheck_1139_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1131_);
                        lean_inc(v_a_1130_);
                        lean_dec(v___x_1129_);
                        v___x_1133_ = lean_box(0);
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
                    lean_ctor_set(v___x_1133_, 0, v___x_1135_);
                    v___x_1137_ = v___x_1133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
                    lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1131_);
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
    mut v_self_1140_: *mut LeanObject,
    mut v_target_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
    mut v_a_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1149_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1146_);
    lean_dec(v_a_1145_);
    lean_dec(v_a_1144_);
    lean_dec(v_a_1143_);
    return v_res_1149_;
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg(
    mut v_self_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v_toContext_1161_ = lean_ctor_get(v_a_1158_, 1);
    v_pkg_1162_ = lean_ctor_get(v_self_1153_, 0);
    lean_inc_n(v_pkg_1162_, 2);
    v_name_1163_ = lean_ctor_get(v_self_1153_, 1);
    lean_inc(v_name_1163_);
    lean_dec_ref(v_self_1153_);
    v_packageMap_1164_ = lean_ctor_get(v_toContext_1161_, 5);
    v___x_1165_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
    lean_inc(v_packageMap_1164_);
    v___x_1166_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1165_, v_packageMap_1164_, v_pkg_1162_);
    if lean_obj_tag(v___x_1166_) == 1 {
        let mut v_val_1167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_pkg_1162_);
        v_val_1167_ = lean_ctor_get(v___x_1166_, 0);
        lean_inc(v_val_1167_);
        lean_dec_ref_known(v___x_1166_, 1);
        v___x_1168_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1168_, 0, v_val_1167_);
        lean_ctor_set(v___x_1168_, 1, v_name_1163_);
        lean_inc_ref(v_a_1158_);
        lean_inc(v_a_1157_);
        lean_inc(v_a_1156_);
        lean_inc(v_a_1155_);
        v___x_1169_ = lean_apply_7(
            v_a_1154_,
            v___x_1168_,
            v_a_1155_,
            v_a_1156_,
            v_a_1157_,
            v_a_1158_,
            v_a_1159_,
            lean_box(0),
        );
        return v___x_1169_;
    } else {
        let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: u8 = 0;
        let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: u8 = 0;
        let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1166_);
        lean_dec_ref(v_a_1154_);
        v___x_1170_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
        v___x_1171_ = 1;
        v___x_1172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_pkg_1162_,
            v___x_1171_,
        );
        v___x_1173_ = lean_string_append(v___x_1170_, v___x_1172_);
        lean_dec_ref(v___x_1172_);
        v___x_1174_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
        v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
        v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_1163_,
            v___x_1171_,
        );
        v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
        lean_dec_ref(v___x_1176_);
        v___x_1178_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
        v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
        v___x_1180_ = 3;
        v___x_1181_ = lean_alloc_ctor(0, 1, (1) as u32);
        lean_ctor_set(v___x_1181_, 0, v___x_1179_);
        lean_ctor_set_uint8(
            v___x_1181_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_1180_,
        );
        v___x_1182_ = lean_array_get_size(v_a_1159_);
        v___x_1183_ = lean_array_push(v_a_1159_, v___x_1181_);
        v___x_1184_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1184_, 0, v___x_1182_);
        lean_ctor_set(v___x_1184_, 1, v___x_1183_);
        return v___x_1184_;
    }
}
pub unsafe fn l_Lake_TargetDecl_fetch___redArg___boxed(
    mut v_self_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1193_: *mut LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_TargetDecl_fetch___redArg(
        v_self_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
        v_a_1189_,
        v_a_1190_,
        v_a_1191_,
    );
    lean_dec_ref(v_a_1190_);
    lean_dec(v_a_1189_);
    lean_dec(v_a_1188_);
    lean_dec(v_a_1187_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_TargetDecl_fetch(
    mut v_00_u03b1_1194_: *mut LeanObject,
    mut v_self_1195_: *mut LeanObject,
    mut v_inst_1196_: *mut LeanObject,
    mut v_a_1197_: *mut LeanObject,
    mut v_a_1198_: *mut LeanObject,
    mut v_a_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1205_: *mut LeanObject,
    mut v_self_1206_: *mut LeanObject,
    mut v_inst_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
    mut v_a_1212_: *mut LeanObject,
    mut v_a_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1215_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1212_);
    lean_dec(v_a_1211_);
    lean_dec(v_a_1210_);
    lean_dec(v_a_1209_);
    return v_res_1215_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
    mut v_t_1216_: *mut LeanObject,
    mut v_k_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1216_) == 0 {
                    v_k_1218_ = lean_ctor_get(v_t_1216_, 1);
                    v_v_1219_ = lean_ctor_get(v_t_1216_, 2);
                    v_l_1220_ = lean_ctor_get(v_t_1216_, 3);
                    v_r_1221_ = lean_ctor_get(v_t_1216_, 4);
                    v___x_1222_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1217_, v_k_1218_);
                    match v___x_1222_ {
                        0 => {
                            v_t_1216_ = v_l_1220_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1219_);
                            v___x_1224_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1224_, 0, v_v_1219_);
                            return v___x_1224_;
                        }
                        _ => {
                            v_t_1216_ = v_r_1221_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1226_ = lean_box(0);
                    return v___x_1226_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(
    mut v_t_1227_: *mut LeanObject,
    mut v_k_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1229_: *mut LeanObject = core::ptr::null_mut();
    v_res_1229_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1227_, v_k_1228_,
        );
    lean_dec(v_k_1228_);
    lean_dec(v_t_1227_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_TargetDecl_fetchJob(
    mut v_self_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
    mut v_a_1233_: *mut LeanObject,
    mut v_a_1234_: *mut LeanObject,
    mut v_a_1235_: *mut LeanObject,
    mut v_a_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1238_ = lean_ctor_get(v_a_1235_, 1);
                v_pkg_1239_ = lean_ctor_get(v_self_1230_, 0);
                lean_inc(v_pkg_1239_);
                v_name_1240_ = lean_ctor_get(v_self_1230_, 1);
                lean_inc(v_name_1240_);
                lean_dec_ref(v_self_1230_);
                v_packageMap_1241_ = lean_ctor_get(v_toContext_1238_, 5);
                v___x_1242_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_packageMap_1241_, v_pkg_1239_);
                if lean_obj_tag(v___x_1242_) == 1 {
                    lean_dec(v_pkg_1239_);
                    v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
                    lean_inc(v_val_1243_);
                    lean_dec_ref_known(v___x_1242_, 1);
                    v___x_1244_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1244_, 0, v_val_1243_);
                    lean_ctor_set(v___x_1244_, 1, v_name_1240_);
                    lean_inc_ref(v_a_1235_);
                    lean_inc(v_a_1234_);
                    lean_inc(v_a_1233_);
                    lean_inc(v_a_1232_);
                    v___x_1245_ = lean_apply_7(
                        v_a_1231_,
                        v___x_1244_,
                        v_a_1232_,
                        v_a_1233_,
                        v_a_1234_,
                        v_a_1235_,
                        v_a_1236_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1245_) == 0 {
                        v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
                        v_a_1247_ = lean_ctor_get(v___x_1245_, 1);
                        v_isSharedCheck_1255_ = (!lean_is_exclusive(v___x_1245_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1249_ = v___x_1245_;
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1247_);
                            lean_inc(v_a_1246_);
                            lean_dec(v___x_1245_);
                            v___x_1249_ = lean_box(0);
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1245_;
                    }
                } else {
                    lean_dec(v___x_1242_);
                    lean_dec_ref(v_a_1231_);
                    v___x_1256_ = l_Lake_TargetDecl_fetch___redArg___closed__0;
                    v___x_1257_ = 1;
                    v___x_1258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1239_,
                        v___x_1257_,
                    );
                    v___x_1259_ = lean_string_append(v___x_1256_, v___x_1258_);
                    lean_dec_ref(v___x_1258_);
                    v___x_1260_ = l_Lake_TargetDecl_fetch___redArg___closed__1;
                    v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
                    v___x_1262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1240_,
                        v___x_1257_,
                    );
                    v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
                    lean_dec_ref(v___x_1262_);
                    v___x_1264_ = l_Lake_TargetDecl_fetch___redArg___closed__2;
                    v___x_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
                    v___x_1266_ = 3;
                    v___x_1267_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1267_, 0, v___x_1265_);
                    lean_ctor_set_uint8(
                        v___x_1267_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1266_,
                    );
                    v___x_1268_ = lean_array_get_size(v_a_1236_);
                    v___x_1269_ = lean_array_push(v_a_1236_, v___x_1267_);
                    v___x_1270_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1270_, 0, v___x_1268_);
                    lean_ctor_set(v___x_1270_, 1, v___x_1269_);
                    return v___x_1270_;
                }
            }
            1 => {
                v___x_1251_ = l_Lake_Job_toOpaque___redArg(v_a_1246_);
                if v_isShared_1250_ == 0 {
                    lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
                    lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1247_);
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
    mut v_self_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v_a_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_a_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1279_: *mut LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lake_TargetDecl_fetchJob(
        v_self_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
        v_a_1275_,
        v_a_1276_,
        v_a_1277_,
    );
    lean_dec_ref(v_a_1276_);
    lean_dec(v_a_1275_);
    lean_dec(v_a_1274_);
    lean_dec(v_a_1273_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
    mut v_00_u03b2_1280_: *mut LeanObject,
    mut v_inst_1281_: *mut LeanObject,
    mut v_t_1282_: *mut LeanObject,
    mut v_k_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(
            v_t_1282_, v_k_1283_,
        );
    return v___x_1284_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(
    mut v_00_u03b2_1285_: *mut LeanObject,
    mut v_inst_1286_: *mut LeanObject,
    mut v_t_1287_: *mut LeanObject,
    mut v_k_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(
        v_00_u03b2_1285_,
        v_inst_1286_,
        v_t_1287_,
        v_k_1288_,
    );
    lean_dec(v_k_1288_);
    lean_dec(v_t_1287_);
    return v_res_1289_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg(
    mut v_pkg_1290_: *mut LeanObject,
    mut v_self_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
    mut v_a_1295_: *mut LeanObject,
    mut v_a_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v_name_1299_ = lean_ctor_get(v_self_1291_, 0);
    v_keyName_1300_ = lean_ctor_get(v_pkg_1290_, 2);
    lean_inc(v_keyName_1300_);
    v___x_1301_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1301_, 0, v_keyName_1300_);
    v___x_1302_ = l_Lake_Package_keyword;
    lean_inc(v_name_1299_);
    v___x_1303_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1303_, 0, v___x_1301_);
    lean_ctor_set(v___x_1303_, 1, v___x_1302_);
    lean_ctor_set(v___x_1303_, 2, v_pkg_1290_);
    lean_ctor_set(v___x_1303_, 3, v_name_1299_);
    lean_inc_ref(v_a_1296_);
    lean_inc(v_a_1295_);
    lean_inc(v_a_1294_);
    lean_inc(v_a_1293_);
    v___x_1304_ = lean_apply_7(
        v_a_1292_,
        v___x_1303_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        lean_box(0),
    );
    return v___x_1304_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___redArg___boxed(
    mut v_pkg_1305_: *mut LeanObject,
    mut v_self_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
    mut v_a_1309_: *mut LeanObject,
    mut v_a_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1311_);
    lean_dec(v_a_1310_);
    lean_dec(v_a_1309_);
    lean_dec(v_a_1308_);
    lean_dec_ref(v_self_1306_);
    return v_res_1314_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch(
    mut v_00_u03b1_1315_: *mut LeanObject,
    mut v_pkg_1316_: *mut LeanObject,
    mut v_self_1317_: *mut LeanObject,
    mut v_inst_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
    mut v_a_1321_: *mut LeanObject,
    mut v_a_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
    mut v_a_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    v_name_1326_ = lean_ctor_get(v_self_1317_, 0);
    v_keyName_1327_ = lean_ctor_get(v_pkg_1316_, 2);
    lean_inc(v_keyName_1327_);
    v___x_1328_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1328_, 0, v_keyName_1327_);
    v___x_1329_ = l_Lake_Package_keyword;
    lean_inc(v_name_1326_);
    v___x_1330_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1330_, 0, v___x_1328_);
    lean_ctor_set(v___x_1330_, 1, v___x_1329_);
    lean_ctor_set(v___x_1330_, 2, v_pkg_1316_);
    lean_ctor_set(v___x_1330_, 3, v_name_1326_);
    lean_inc_ref(v_a_1323_);
    lean_inc(v_a_1322_);
    lean_inc(v_a_1321_);
    lean_inc(v_a_1320_);
    v___x_1331_ = lean_apply_7(
        v_a_1319_,
        v___x_1330_,
        v_a_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        lean_box(0),
    );
    return v___x_1331_;
}
pub unsafe fn l_Lake_PackageFacetDecl_fetch___boxed(
    mut v_00_u03b1_1332_: *mut LeanObject,
    mut v_pkg_1333_: *mut LeanObject,
    mut v_self_1334_: *mut LeanObject,
    mut v_inst_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1343_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1340_);
    lean_dec(v_a_1339_);
    lean_dec(v_a_1338_);
    lean_dec(v_a_1337_);
    lean_dec_ref(v_self_1334_);
    return v_res_1343_;
}
pub unsafe fn l_Lake_Package_fetchFacetJob(
    mut v_name_1344_: *mut LeanObject,
    mut v_self_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keyName_1353_ = lean_ctor_get(v_self_1345_, 2);
                v___x_1354_ = l_Lake_Package_keyword;
                v___x_1355_ = l_Lean_Name_append(v___x_1354_, v_name_1344_);
                lean_inc(v_keyName_1353_);
                v___x_1356_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1356_, 0, v_keyName_1353_);
                v___x_1357_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                lean_ctor_set(v___x_1357_, 1, v___x_1354_);
                lean_ctor_set(v___x_1357_, 2, v_self_1345_);
                lean_ctor_set(v___x_1357_, 3, v___x_1355_);
                lean_inc_ref(v_a_1350_);
                lean_inc(v_a_1349_);
                lean_inc(v_a_1348_);
                lean_inc(v_a_1347_);
                v___x_1358_ = lean_apply_7(
                    v_a_1346_,
                    v___x_1357_,
                    v_a_1347_,
                    v_a_1348_,
                    v_a_1349_,
                    v_a_1350_,
                    v_a_1351_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1358_) == 0 {
                    v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
                    v_a_1360_ = lean_ctor_get(v___x_1358_, 1);
                    v_isSharedCheck_1368_ = (!lean_is_exclusive(v___x_1358_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1362_ = v___x_1358_;
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1360_);
                        lean_inc(v_a_1359_);
                        lean_dec(v___x_1358_);
                        v___x_1362_ = lean_box(0);
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
                    lean_ctor_set(v___x_1362_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1360_);
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
    mut v_name_1369_: *mut LeanObject,
    mut v_self_1370_: *mut LeanObject,
    mut v_a_1371_: *mut LeanObject,
    mut v_a_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1378_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1375_);
    lean_dec(v_a_1374_);
    lean_dec(v_a_1373_);
    lean_dec(v_a_1372_);
    return v_res_1378_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg(
    mut v_mod_1379_: *mut LeanObject,
    mut v_self_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v_name_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_unused_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1388_ = lean_ctor_get(v_mod_1379_, 0);
                v_pkg_1389_ = lean_ctor_get(v_lib_1388_, 0);
                v_name_1390_ = lean_ctor_get(v_self_1380_, 0);
                v_isSharedCheck_1402_ = (!lean_is_exclusive(v_self_1380_)) as u8;
                if v_isSharedCheck_1402_ == 0 {
                    v_unused_1403_ = lean_ctor_get(v_self_1380_, 1);
                    lean_dec(v_unused_1403_);
                    v___x_1392_ = v_self_1380_;
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1390_);
                    lean_dec(v_self_1380_);
                    v___x_1392_ = lean_box(0);
                    v_isShared_1393_ = v_isSharedCheck_1402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1394_ = lean_ctor_get(v_mod_1379_, 1);
                v_keyName_1395_ = lean_ctor_get(v_pkg_1389_, 2);
                lean_inc(v_name_1394_);
                lean_inc(v_keyName_1395_);
                if v_isShared_1393_ == 0 {
                    lean_ctor_set_tag(v___x_1392_, 2);
                    lean_ctor_set(v___x_1392_, 1, v_name_1394_);
                    lean_ctor_set(v___x_1392_, 0, v_keyName_1395_);
                    v___x_1397_ = v___x_1392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1401_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_keyName_1395_);
                    lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_name_1394_);
                    v___x_1397_ = v_reuseFailAlloc_1401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1398_ = l_Lake_Module_keyword;
                v___x_1399_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1399_, 0, v___x_1397_);
                lean_ctor_set(v___x_1399_, 1, v___x_1398_);
                lean_ctor_set(v___x_1399_, 2, v_mod_1379_);
                lean_ctor_set(v___x_1399_, 3, v_name_1390_);
                lean_inc_ref(v_a_1385_);
                lean_inc(v_a_1384_);
                lean_inc(v_a_1383_);
                lean_inc(v_a_1382_);
                v___x_1400_ = lean_apply_7(
                    v_a_1381_,
                    v___x_1399_,
                    v_a_1382_,
                    v_a_1383_,
                    v_a_1384_,
                    v_a_1385_,
                    v_a_1386_,
                    lean_box(0),
                );
                return v___x_1400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___redArg___boxed(
    mut v_mod_1404_: *mut LeanObject,
    mut v_self_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
    mut v_a_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
    mut v_a_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1413_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1410_);
    lean_dec(v_a_1409_);
    lean_dec(v_a_1408_);
    lean_dec(v_a_1407_);
    return v_res_1413_;
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch(
    mut v_00_u03b1_1414_: *mut LeanObject,
    mut v_mod_1415_: *mut LeanObject,
    mut v_self_1416_: *mut LeanObject,
    mut v_inst_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
    mut v_a_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_name_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1439_: u8 = 0;
    let mut v_unused_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1425_ = lean_ctor_get(v_mod_1415_, 0);
                v_pkg_1426_ = lean_ctor_get(v_lib_1425_, 0);
                v_name_1427_ = lean_ctor_get(v_self_1416_, 0);
                v_isSharedCheck_1439_ = (!lean_is_exclusive(v_self_1416_)) as u8;
                if v_isSharedCheck_1439_ == 0 {
                    v_unused_1440_ = lean_ctor_get(v_self_1416_, 1);
                    lean_dec(v_unused_1440_);
                    v___x_1429_ = v_self_1416_;
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1427_);
                    lean_dec(v_self_1416_);
                    v___x_1429_ = lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1431_ = lean_ctor_get(v_mod_1415_, 1);
                v_keyName_1432_ = lean_ctor_get(v_pkg_1426_, 2);
                lean_inc(v_name_1431_);
                lean_inc(v_keyName_1432_);
                if v_isShared_1430_ == 0 {
                    lean_ctor_set_tag(v___x_1429_, 2);
                    lean_ctor_set(v___x_1429_, 1, v_name_1431_);
                    lean_ctor_set(v___x_1429_, 0, v_keyName_1432_);
                    v___x_1434_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_keyName_1432_);
                    lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_name_1431_);
                    v___x_1434_ = v_reuseFailAlloc_1438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1435_ = l_Lake_Module_keyword;
                v___x_1436_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1436_, 0, v___x_1434_);
                lean_ctor_set(v___x_1436_, 1, v___x_1435_);
                lean_ctor_set(v___x_1436_, 2, v_mod_1415_);
                lean_ctor_set(v___x_1436_, 3, v_name_1427_);
                lean_inc_ref(v_a_1422_);
                lean_inc(v_a_1421_);
                lean_inc(v_a_1420_);
                lean_inc(v_a_1419_);
                v___x_1437_ = lean_apply_7(
                    v_a_1418_,
                    v___x_1436_,
                    v_a_1419_,
                    v_a_1420_,
                    v_a_1421_,
                    v_a_1422_,
                    v_a_1423_,
                    lean_box(0),
                );
                return v___x_1437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleFacetDecl_fetch___boxed(
    mut v_00_u03b1_1441_: *mut LeanObject,
    mut v_mod_1442_: *mut LeanObject,
    mut v_self_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_a_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
    mut v_a_1448_: *mut LeanObject,
    mut v_a_1449_: *mut LeanObject,
    mut v_a_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1452_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1449_);
    lean_dec(v_a_1448_);
    lean_dec(v_a_1447_);
    lean_dec(v_a_1446_);
    return v_res_1452_;
}
pub unsafe fn l_Lake_Module_fetchFacetJob(
    mut v_name_1453_: *mut LeanObject,
    mut v_self_1454_: *mut LeanObject,
    mut v_a_1455_: *mut LeanObject,
    mut v_a_1456_: *mut LeanObject,
    mut v_a_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v_a_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_1462_ = lean_ctor_get(v_self_1454_, 0);
                v_pkg_1463_ = lean_ctor_get(v_lib_1462_, 0);
                v_name_1464_ = lean_ctor_get(v_self_1454_, 1);
                v_keyName_1465_ = lean_ctor_get(v_pkg_1463_, 2);
                v___x_1466_ = l_Lake_Module_keyword;
                v___x_1467_ = l_Lean_Name_append(v___x_1466_, v_name_1453_);
                lean_inc(v_name_1464_);
                lean_inc(v_keyName_1465_);
                v___x_1468_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1468_, 0, v_keyName_1465_);
                lean_ctor_set(v___x_1468_, 1, v_name_1464_);
                v___x_1469_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                lean_ctor_set(v___x_1469_, 1, v___x_1466_);
                lean_ctor_set(v___x_1469_, 2, v_self_1454_);
                lean_ctor_set(v___x_1469_, 3, v___x_1467_);
                lean_inc_ref(v_a_1459_);
                lean_inc(v_a_1458_);
                lean_inc(v_a_1457_);
                lean_inc(v_a_1456_);
                v___x_1470_ = lean_apply_7(
                    v_a_1455_,
                    v___x_1469_,
                    v_a_1456_,
                    v_a_1457_,
                    v_a_1458_,
                    v_a_1459_,
                    v_a_1460_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1470_) == 0 {
                    v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
                    v_a_1472_ = lean_ctor_get(v___x_1470_, 1);
                    v_isSharedCheck_1480_ = (!lean_is_exclusive(v___x_1470_)) as u8;
                    if v_isSharedCheck_1480_ == 0 {
                        v___x_1474_ = v___x_1470_;
                        v_isShared_1475_ = v_isSharedCheck_1480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1472_);
                        lean_inc(v_a_1471_);
                        lean_dec(v___x_1470_);
                        v___x_1474_ = lean_box(0);
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
                    lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1472_);
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
    mut v_name_1481_: *mut LeanObject,
    mut v_self_1482_: *mut LeanObject,
    mut v_a_1483_: *mut LeanObject,
    mut v_a_1484_: *mut LeanObject,
    mut v_a_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1490_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1487_);
    lean_dec(v_a_1486_);
    lean_dec(v_a_1485_);
    lean_dec(v_a_1484_);
    return v_res_1490_;
}
pub unsafe fn l_Lake_LeanLibDecl_get___redArg(
    mut v_self_1491_: *mut LeanObject,
    mut v_inst_1492_: *mut LeanObject,
    mut v_inst_1493_: *mut LeanObject,
    mut v_inst_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1495_ = lean_ctor_get(v_inst_1492_, 0);
    lean_inc_ref(v_toApplicative_1495_);
    v_toFunctor_1496_ = lean_ctor_get(v_toApplicative_1495_, 0);
    lean_inc_ref(v_toFunctor_1496_);
    v_toBind_1497_ = lean_ctor_get(v_inst_1492_, 1);
    lean_inc(v_toBind_1497_);
    lean_dec_ref(v_inst_1492_);
    v_toPure_1498_ = lean_ctor_get(v_toApplicative_1495_, 1);
    lean_inc(v_toPure_1498_);
    lean_dec_ref(v_toApplicative_1495_);
    v_pkg_1499_ = lean_ctor_get(v_self_1491_, 0);
    lean_inc_n(v_pkg_1499_, 2);
    v_name_1500_ = lean_ctor_get(v_self_1491_, 1);
    lean_inc(v_name_1500_);
    v_config_1501_ = lean_ctor_get(v_self_1491_, 3);
    lean_inc(v_config_1501_);
    lean_dec_ref(v_self_1491_);
    v_map_1502_ = lean_ctor_get(v_toFunctor_1496_, 0);
    lean_inc_n(v_map_1502_, 2);
    lean_dec_ref(v_toFunctor_1496_);
    v___f_1503_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1504_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1504_, 0, v_name_1500_);
    lean_closure_set(v___f_1504_, 1, v_config_1501_);
    lean_closure_set(v___f_1504_, 2, v_toPure_1498_);
    lean_closure_set(v___f_1504_, 3, v_pkg_1499_);
    lean_closure_set(v___f_1504_, 4, v_inst_1493_);
    v___f_1505_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1505_, 0, v_pkg_1499_);
    v___x_1506_ = lean_apply_4(
        v_map_1502_,
        lean_box(0),
        lean_box(0),
        v___f_1503_,
        v_inst_1494_,
    );
    v___x_1507_ = lean_apply_4(
        v_map_1502_,
        lean_box(0),
        lean_box(0),
        v___f_1505_,
        v___x_1506_,
    );
    v___x_1508_ = lean_apply_4(
        v_toBind_1497_,
        lean_box(0),
        lean_box(0),
        v___x_1507_,
        v___f_1504_,
    );
    return v___x_1508_;
}
pub unsafe fn l_Lake_LeanLibDecl_get(
    mut v_m_1509_: *mut LeanObject,
    mut v_self_1510_: *mut LeanObject,
    mut v_inst_1511_: *mut LeanObject,
    mut v_inst_1512_: *mut LeanObject,
    mut v_inst_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1514_ = lean_ctor_get(v_inst_1511_, 0);
    lean_inc_ref(v_toApplicative_1514_);
    v_toFunctor_1515_ = lean_ctor_get(v_toApplicative_1514_, 0);
    lean_inc_ref(v_toFunctor_1515_);
    v_toBind_1516_ = lean_ctor_get(v_inst_1511_, 1);
    lean_inc(v_toBind_1516_);
    lean_dec_ref(v_inst_1511_);
    v_toPure_1517_ = lean_ctor_get(v_toApplicative_1514_, 1);
    lean_inc(v_toPure_1517_);
    lean_dec_ref(v_toApplicative_1514_);
    v_pkg_1518_ = lean_ctor_get(v_self_1510_, 0);
    lean_inc_n(v_pkg_1518_, 2);
    v_name_1519_ = lean_ctor_get(v_self_1510_, 1);
    lean_inc(v_name_1519_);
    v_config_1520_ = lean_ctor_get(v_self_1510_, 3);
    lean_inc(v_config_1520_);
    lean_dec_ref(v_self_1510_);
    v_map_1521_ = lean_ctor_get(v_toFunctor_1515_, 0);
    lean_inc_n(v_map_1521_, 2);
    lean_dec_ref(v_toFunctor_1515_);
    v___f_1522_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1523_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1523_, 0, v_name_1519_);
    lean_closure_set(v___f_1523_, 1, v_config_1520_);
    lean_closure_set(v___f_1523_, 2, v_toPure_1517_);
    lean_closure_set(v___f_1523_, 3, v_pkg_1518_);
    lean_closure_set(v___f_1523_, 4, v_inst_1512_);
    v___f_1524_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1524_, 0, v_pkg_1518_);
    v___x_1525_ = lean_apply_4(
        v_map_1521_,
        lean_box(0),
        lean_box(0),
        v___f_1522_,
        v_inst_1513_,
    );
    v___x_1526_ = lean_apply_4(
        v_map_1521_,
        lean_box(0),
        lean_box(0),
        v___f_1524_,
        v___x_1525_,
    );
    v___x_1527_ = lean_apply_4(
        v_toBind_1516_,
        lean_box(0),
        lean_box(0),
        v___x_1526_,
        v___f_1523_,
    );
    return v___x_1527_;
}
pub unsafe fn l_Lake_LeanLib_fetch(
    mut v_self_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1539_ = lean_ctor_get(v_self_1531_, 0);
    v_name_1540_ = lean_ctor_get(v_self_1531_, 1);
    v_keyName_1541_ = lean_ctor_get(v_pkg_1539_, 2);
    v___x_1542_ = l_Lake_LeanLib_defaultFacet;
    lean_inc(v_name_1540_);
    lean_inc(v_keyName_1541_);
    v___x_1543_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1543_, 0, v_keyName_1541_);
    lean_ctor_set(v___x_1543_, 1, v_name_1540_);
    v___x_1544_ = l_Lake_LeanLib_fetch___closed__1;
    v___x_1545_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1545_, 0, v___x_1543_);
    lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    lean_ctor_set(v___x_1545_, 2, v_self_1531_);
    lean_ctor_set(v___x_1545_, 3, v___x_1542_);
    lean_inc_ref(v_a_1536_);
    lean_inc(v_a_1535_);
    lean_inc(v_a_1534_);
    lean_inc(v_a_1533_);
    v___x_1546_ = lean_apply_7(
        v_a_1532_,
        v___x_1545_,
        v_a_1533_,
        v_a_1534_,
        v_a_1535_,
        v_a_1536_,
        v_a_1537_,
        lean_box(0),
    );
    return v___x_1546_;
}
pub unsafe fn l_Lake_LeanLib_fetch___boxed(
    mut v_self_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Lake_LeanLib_fetch(
        v_self_1547_,
        v_a_1548_,
        v_a_1549_,
        v_a_1550_,
        v_a_1551_,
        v_a_1552_,
        v_a_1553_,
    );
    lean_dec_ref(v_a_1552_);
    lean_dec(v_a_1551_);
    lean_dec(v_a_1550_);
    lean_dec(v_a_1549_);
    return v_res_1555_;
}
pub unsafe fn l_Lake_LeanLibDecl_fetch(
    mut v_self_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_a_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_packageMap_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_unused_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1564_ = lean_ctor_get(v_a_1561_, 1);
                v_pkg_1565_ = lean_ctor_get(v_self_1556_, 0);
                v_name_1566_ = lean_ctor_get(v_self_1556_, 1);
                v_config_1567_ = lean_ctor_get(v_self_1556_, 3);
                v_isSharedCheck_1599_ = (!lean_is_exclusive(v_self_1556_)) as u8;
                if v_isSharedCheck_1599_ == 0 {
                    v_unused_1600_ = lean_ctor_get(v_self_1556_, 2);
                    lean_dec(v_unused_1600_);
                    v___x_1569_ = v_self_1556_;
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_1567_);
                    lean_inc(v_name_1566_);
                    lean_inc(v_pkg_1565_);
                    lean_dec(v_self_1556_);
                    v___x_1569_ = lean_box(0);
                    v_isShared_1570_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1571_ = lean_ctor_get(v_toContext_1564_, 5);
                v___x_1572_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                lean_inc(v_pkg_1565_);
                lean_inc(v_packageMap_1571_);
                v___x_1573_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1572_,
                    v_packageMap_1571_,
                    v_pkg_1565_,
                );
                if lean_obj_tag(v___x_1573_) == 1 {
                    lean_dec(v_pkg_1565_);
                    v_val_1574_ = lean_ctor_get(v___x_1573_, 0);
                    lean_inc(v_val_1574_);
                    lean_dec_ref_known(v___x_1573_, 1);
                    v_keyName_1575_ = lean_ctor_get(v_val_1574_, 2);
                    lean_inc(v_keyName_1575_);
                    v___x_1576_ = l_Lake_LeanLib_fetch___closed__1;
                    lean_inc(v_name_1566_);
                    v___x_1577_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1577_, 0, v_val_1574_);
                    lean_ctor_set(v___x_1577_, 1, v_name_1566_);
                    lean_ctor_set(v___x_1577_, 2, v_config_1567_);
                    v___x_1578_ = l_Lake_LeanLib_defaultFacet;
                    v___x_1579_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_1579_, 0, v_keyName_1575_);
                    lean_ctor_set(v___x_1579_, 1, v_name_1566_);
                    if v_isShared_1570_ == 0 {
                        lean_ctor_set_tag(v___x_1569_, 1);
                        lean_ctor_set(v___x_1569_, 3, v___x_1578_);
                        lean_ctor_set(v___x_1569_, 2, v___x_1577_);
                        lean_ctor_set(v___x_1569_, 1, v___x_1576_);
                        lean_ctor_set(v___x_1569_, 0, v___x_1579_);
                        v___x_1581_ = v___x_1569_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1576_);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 2, v___x_1577_);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1578_);
                        v___x_1581_ = v_reuseFailAlloc_1583_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1573_);
                    lean_del_object(v___x_1569_);
                    lean_dec(v_config_1567_);
                    lean_dec_ref(v_a_1557_);
                    v___x_1584_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1585_ = 1;
                    v___x_1586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1565_,
                        v___x_1585_,
                    );
                    v___x_1587_ = lean_string_append(v___x_1584_, v___x_1586_);
                    lean_dec_ref(v___x_1586_);
                    v___x_1588_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
                    v___x_1590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1566_,
                        v___x_1585_,
                    );
                    v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
                    lean_dec_ref(v___x_1590_);
                    v___x_1592_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
                    v___x_1594_ = 3;
                    v___x_1595_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1595_, 0, v___x_1593_);
                    lean_ctor_set_uint8(
                        v___x_1595_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1594_,
                    );
                    v___x_1596_ = lean_array_get_size(v_a_1562_);
                    v___x_1597_ = lean_array_push(v_a_1562_, v___x_1595_);
                    v___x_1598_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1598_, 0, v___x_1596_);
                    lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                    return v___x_1598_;
                }
            }
            2 => {
                lean_inc_ref(v_a_1561_);
                lean_inc(v_a_1560_);
                lean_inc(v_a_1559_);
                lean_inc(v_a_1558_);
                v___x_1582_ = lean_apply_7(
                    v_a_1557_,
                    v___x_1581_,
                    v_a_1558_,
                    v_a_1559_,
                    v_a_1560_,
                    v_a_1561_,
                    v_a_1562_,
                    lean_box(0),
                );
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibDecl_fetch___boxed(
    mut v_self_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1609_: *mut LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lake_LeanLibDecl_fetch(
        v_self_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
    );
    lean_dec_ref(v_a_1606_);
    lean_dec(v_a_1605_);
    lean_dec(v_a_1604_);
    lean_dec(v_a_1603_);
    return v_res_1609_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg(
    mut v_lib_1610_: *mut LeanObject,
    mut v_self_1611_: *mut LeanObject,
    mut v_a_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_name_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1619_ = lean_ctor_get(v_lib_1610_, 0);
                v_name_1620_ = lean_ctor_get(v_self_1611_, 0);
                v_isSharedCheck_1632_ = (!lean_is_exclusive(v_self_1611_)) as u8;
                if v_isSharedCheck_1632_ == 0 {
                    v_unused_1633_ = lean_ctor_get(v_self_1611_, 1);
                    lean_dec(v_unused_1633_);
                    v___x_1622_ = v_self_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1620_);
                    lean_dec(v_self_1611_);
                    v___x_1622_ = lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1624_ = lean_ctor_get(v_lib_1610_, 1);
                v_keyName_1625_ = lean_ctor_get(v_pkg_1619_, 2);
                lean_inc(v_name_1624_);
                lean_inc(v_keyName_1625_);
                if v_isShared_1623_ == 0 {
                    lean_ctor_set_tag(v___x_1622_, 3);
                    lean_ctor_set(v___x_1622_, 1, v_name_1624_);
                    lean_ctor_set(v___x_1622_, 0, v_keyName_1625_);
                    v___x_1627_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_keyName_1625_);
                    lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_name_1624_);
                    v___x_1627_ = v_reuseFailAlloc_1631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1629_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1629_, 0, v___x_1627_);
                lean_ctor_set(v___x_1629_, 1, v___x_1628_);
                lean_ctor_set(v___x_1629_, 2, v_lib_1610_);
                lean_ctor_set(v___x_1629_, 3, v_name_1620_);
                lean_inc_ref(v_a_1616_);
                lean_inc(v_a_1615_);
                lean_inc(v_a_1614_);
                lean_inc(v_a_1613_);
                v___x_1630_ = lean_apply_7(
                    v_a_1612_,
                    v___x_1629_,
                    v_a_1613_,
                    v_a_1614_,
                    v_a_1615_,
                    v_a_1616_,
                    v_a_1617_,
                    lean_box(0),
                );
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___redArg___boxed(
    mut v_lib_1634_: *mut LeanObject,
    mut v_self_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v_a_1638_: *mut LeanObject,
    mut v_a_1639_: *mut LeanObject,
    mut v_a_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_a_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1643_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1640_);
    lean_dec(v_a_1639_);
    lean_dec(v_a_1638_);
    lean_dec(v_a_1637_);
    return v_res_1643_;
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch(
    mut v_00_u03b1_1644_: *mut LeanObject,
    mut v_lib_1645_: *mut LeanObject,
    mut v_self_1646_: *mut LeanObject,
    mut v_inst_1647_: *mut LeanObject,
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v_name_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1655_ = lean_ctor_get(v_lib_1645_, 0);
                v_name_1656_ = lean_ctor_get(v_self_1646_, 0);
                v_isSharedCheck_1668_ = (!lean_is_exclusive(v_self_1646_)) as u8;
                if v_isSharedCheck_1668_ == 0 {
                    v_unused_1669_ = lean_ctor_get(v_self_1646_, 1);
                    lean_dec(v_unused_1669_);
                    v___x_1658_ = v_self_1646_;
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1656_);
                    lean_dec(v_self_1646_);
                    v___x_1658_ = lean_box(0);
                    v_isShared_1659_ = v_isSharedCheck_1668_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1660_ = lean_ctor_get(v_lib_1645_, 1);
                v_keyName_1661_ = lean_ctor_get(v_pkg_1655_, 2);
                lean_inc(v_name_1660_);
                lean_inc(v_keyName_1661_);
                if v_isShared_1659_ == 0 {
                    lean_ctor_set_tag(v___x_1658_, 3);
                    lean_ctor_set(v___x_1658_, 1, v_name_1660_);
                    lean_ctor_set(v___x_1658_, 0, v_keyName_1661_);
                    v___x_1663_ = v___x_1658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_keyName_1661_);
                    lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_name_1660_);
                    v___x_1663_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1664_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1665_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1665_, 0, v___x_1663_);
                lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                lean_ctor_set(v___x_1665_, 2, v_lib_1645_);
                lean_ctor_set(v___x_1665_, 3, v_name_1656_);
                lean_inc_ref(v_a_1652_);
                lean_inc(v_a_1651_);
                lean_inc(v_a_1650_);
                lean_inc(v_a_1649_);
                v___x_1666_ = lean_apply_7(
                    v_a_1648_,
                    v___x_1665_,
                    v_a_1649_,
                    v_a_1650_,
                    v_a_1651_,
                    v_a_1652_,
                    v_a_1653_,
                    lean_box(0),
                );
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LibraryFacetDecl_fetch___boxed(
    mut v_00_u03b1_1670_: *mut LeanObject,
    mut v_lib_1671_: *mut LeanObject,
    mut v_self_1672_: *mut LeanObject,
    mut v_inst_1673_: *mut LeanObject,
    mut v_a_1674_: *mut LeanObject,
    mut v_a_1675_: *mut LeanObject,
    mut v_a_1676_: *mut LeanObject,
    mut v_a_1677_: *mut LeanObject,
    mut v_a_1678_: *mut LeanObject,
    mut v_a_1679_: *mut LeanObject,
    mut v_a_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1681_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1678_);
    lean_dec(v_a_1677_);
    lean_dec(v_a_1676_);
    lean_dec(v_a_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Lake_LeanLib_fetchFacetJob(
    mut v_name_1682_: *mut LeanObject,
    mut v_self_1683_: *mut LeanObject,
    mut v_a_1684_: *mut LeanObject,
    mut v_a_1685_: *mut LeanObject,
    mut v_a_1686_: *mut LeanObject,
    mut v_a_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1691_ = lean_ctor_get(v_self_1683_, 0);
                v_name_1692_ = lean_ctor_get(v_self_1683_, 1);
                v_keyName_1693_ = lean_ctor_get(v_pkg_1691_, 2);
                v___x_1694_ = l_Lake_LeanLib_fetch___closed__1;
                v___x_1695_ = l_Lean_Name_append(v___x_1694_, v_name_1682_);
                lean_inc(v_name_1692_);
                lean_inc(v_keyName_1693_);
                v___x_1696_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_1696_, 0, v_keyName_1693_);
                lean_ctor_set(v___x_1696_, 1, v_name_1692_);
                v___x_1697_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                lean_ctor_set(v___x_1697_, 1, v___x_1694_);
                lean_ctor_set(v___x_1697_, 2, v_self_1683_);
                lean_ctor_set(v___x_1697_, 3, v___x_1695_);
                lean_inc_ref(v_a_1688_);
                lean_inc(v_a_1687_);
                lean_inc(v_a_1686_);
                lean_inc(v_a_1685_);
                v___x_1698_ = lean_apply_7(
                    v_a_1684_,
                    v___x_1697_,
                    v_a_1685_,
                    v_a_1686_,
                    v_a_1687_,
                    v_a_1688_,
                    v_a_1689_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1698_) == 0 {
                    v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
                    v_a_1700_ = lean_ctor_get(v___x_1698_, 1);
                    v_isSharedCheck_1708_ = (!lean_is_exclusive(v___x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v___x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1700_);
                        lean_inc(v_a_1699_);
                        lean_dec(v___x_1698_);
                        v___x_1702_ = lean_box(0);
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
                    lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
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
    mut v_name_1709_: *mut LeanObject,
    mut v_self_1710_: *mut LeanObject,
    mut v_a_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
    mut v_a_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1718_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_1715_);
    lean_dec(v_a_1714_);
    lean_dec(v_a_1713_);
    lean_dec(v_a_1712_);
    return v_res_1718_;
}
pub unsafe fn l_Lake_LeanExeDecl_get___redArg(
    mut v_self_1719_: *mut LeanObject,
    mut v_inst_1720_: *mut LeanObject,
    mut v_inst_1721_: *mut LeanObject,
    mut v_inst_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1723_ = lean_ctor_get(v_inst_1720_, 0);
    lean_inc_ref(v_toApplicative_1723_);
    v_toFunctor_1724_ = lean_ctor_get(v_toApplicative_1723_, 0);
    lean_inc_ref(v_toFunctor_1724_);
    v_toBind_1725_ = lean_ctor_get(v_inst_1720_, 1);
    lean_inc(v_toBind_1725_);
    lean_dec_ref(v_inst_1720_);
    v_toPure_1726_ = lean_ctor_get(v_toApplicative_1723_, 1);
    lean_inc(v_toPure_1726_);
    lean_dec_ref(v_toApplicative_1723_);
    v_pkg_1727_ = lean_ctor_get(v_self_1719_, 0);
    lean_inc_n(v_pkg_1727_, 2);
    v_name_1728_ = lean_ctor_get(v_self_1719_, 1);
    lean_inc(v_name_1728_);
    v_config_1729_ = lean_ctor_get(v_self_1719_, 3);
    lean_inc(v_config_1729_);
    lean_dec_ref(v_self_1719_);
    v_map_1730_ = lean_ctor_get(v_toFunctor_1724_, 0);
    lean_inc_n(v_map_1730_, 2);
    lean_dec_ref(v_toFunctor_1724_);
    v___f_1731_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1732_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1732_, 0, v_name_1728_);
    lean_closure_set(v___f_1732_, 1, v_config_1729_);
    lean_closure_set(v___f_1732_, 2, v_toPure_1726_);
    lean_closure_set(v___f_1732_, 3, v_pkg_1727_);
    lean_closure_set(v___f_1732_, 4, v_inst_1721_);
    v___f_1733_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1733_, 0, v_pkg_1727_);
    v___x_1734_ = lean_apply_4(
        v_map_1730_,
        lean_box(0),
        lean_box(0),
        v___f_1731_,
        v_inst_1722_,
    );
    v___x_1735_ = lean_apply_4(
        v_map_1730_,
        lean_box(0),
        lean_box(0),
        v___f_1733_,
        v___x_1734_,
    );
    v___x_1736_ = lean_apply_4(
        v_toBind_1725_,
        lean_box(0),
        lean_box(0),
        v___x_1735_,
        v___f_1732_,
    );
    return v___x_1736_;
}
pub unsafe fn l_Lake_LeanExeDecl_get(
    mut v_m_1737_: *mut LeanObject,
    mut v_self_1738_: *mut LeanObject,
    mut v_inst_1739_: *mut LeanObject,
    mut v_inst_1740_: *mut LeanObject,
    mut v_inst_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1742_ = lean_ctor_get(v_inst_1739_, 0);
    lean_inc_ref(v_toApplicative_1742_);
    v_toFunctor_1743_ = lean_ctor_get(v_toApplicative_1742_, 0);
    lean_inc_ref(v_toFunctor_1743_);
    v_toBind_1744_ = lean_ctor_get(v_inst_1739_, 1);
    lean_inc(v_toBind_1744_);
    lean_dec_ref(v_inst_1739_);
    v_toPure_1745_ = lean_ctor_get(v_toApplicative_1742_, 1);
    lean_inc(v_toPure_1745_);
    lean_dec_ref(v_toApplicative_1742_);
    v_pkg_1746_ = lean_ctor_get(v_self_1738_, 0);
    lean_inc_n(v_pkg_1746_, 2);
    v_name_1747_ = lean_ctor_get(v_self_1738_, 1);
    lean_inc(v_name_1747_);
    v_config_1748_ = lean_ctor_get(v_self_1738_, 3);
    lean_inc(v_config_1748_);
    lean_dec_ref(v_self_1738_);
    v_map_1749_ = lean_ctor_get(v_toFunctor_1743_, 0);
    lean_inc_n(v_map_1749_, 2);
    lean_dec_ref(v_toFunctor_1743_);
    v___f_1750_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1751_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1751_, 0, v_name_1747_);
    lean_closure_set(v___f_1751_, 1, v_config_1748_);
    lean_closure_set(v___f_1751_, 2, v_toPure_1745_);
    lean_closure_set(v___f_1751_, 3, v_pkg_1746_);
    lean_closure_set(v___f_1751_, 4, v_inst_1740_);
    v___f_1752_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1752_, 0, v_pkg_1746_);
    v___x_1753_ = lean_apply_4(
        v_map_1749_,
        lean_box(0),
        lean_box(0),
        v___f_1750_,
        v_inst_1741_,
    );
    v___x_1754_ = lean_apply_4(
        v_map_1749_,
        lean_box(0),
        lean_box(0),
        v___f_1752_,
        v___x_1753_,
    );
    v___x_1755_ = lean_apply_4(
        v_toBind_1744_,
        lean_box(0),
        lean_box(0),
        v___x_1754_,
        v___f_1751_,
    );
    return v___x_1755_;
}
pub unsafe fn l_Lake_LeanExe_fetch(
    mut v_self_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
    mut v_a_1759_: *mut LeanObject,
    mut v_a_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1764_ = lean_ctor_get(v_self_1756_, 0);
    v_name_1765_ = lean_ctor_get(v_self_1756_, 1);
    v_keyName_1766_ = lean_ctor_get(v_pkg_1764_, 2);
    v___x_1767_ = l_Lake_LeanExe_exeFacet;
    lean_inc(v_name_1765_);
    lean_inc(v_keyName_1766_);
    v___x_1768_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1768_, 0, v_keyName_1766_);
    lean_ctor_set(v___x_1768_, 1, v_name_1765_);
    v___x_1769_ = l_Lake_LeanExe_keyword;
    v___x_1770_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1770_, 0, v___x_1768_);
    lean_ctor_set(v___x_1770_, 1, v___x_1769_);
    lean_ctor_set(v___x_1770_, 2, v_self_1756_);
    lean_ctor_set(v___x_1770_, 3, v___x_1767_);
    lean_inc_ref(v_a_1761_);
    lean_inc(v_a_1760_);
    lean_inc(v_a_1759_);
    lean_inc(v_a_1758_);
    v___x_1771_ = lean_apply_7(
        v_a_1757_,
        v___x_1770_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
        v_a_1761_,
        v_a_1762_,
        lean_box(0),
    );
    return v___x_1771_;
}
pub unsafe fn l_Lake_LeanExe_fetch___boxed(
    mut v_self_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_a_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1780_: *mut LeanObject = core::ptr::null_mut();
    v_res_1780_ = l_Lake_LeanExe_fetch(
        v_self_1772_,
        v_a_1773_,
        v_a_1774_,
        v_a_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
    );
    lean_dec_ref(v_a_1777_);
    lean_dec(v_a_1776_);
    lean_dec(v_a_1775_);
    lean_dec(v_a_1774_);
    return v_res_1780_;
}
pub unsafe fn l_Lake_LeanExeDecl_fetch(
    mut v_self_1781_: *mut LeanObject,
    mut v_a_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
    mut v_a_1784_: *mut LeanObject,
    mut v_a_1785_: *mut LeanObject,
    mut v_a_1786_: *mut LeanObject,
    mut v_a_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v_packageMap_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut v_unused_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1789_ = lean_ctor_get(v_a_1786_, 1);
                v_pkg_1790_ = lean_ctor_get(v_self_1781_, 0);
                v_name_1791_ = lean_ctor_get(v_self_1781_, 1);
                v_config_1792_ = lean_ctor_get(v_self_1781_, 3);
                v_isSharedCheck_1824_ = (!lean_is_exclusive(v_self_1781_)) as u8;
                if v_isSharedCheck_1824_ == 0 {
                    v_unused_1825_ = lean_ctor_get(v_self_1781_, 2);
                    lean_dec(v_unused_1825_);
                    v___x_1794_ = v_self_1781_;
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_1792_);
                    lean_inc(v_name_1791_);
                    lean_inc(v_pkg_1790_);
                    lean_dec(v_self_1781_);
                    v___x_1794_ = lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1796_ = lean_ctor_get(v_toContext_1789_, 5);
                v___x_1797_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                lean_inc(v_pkg_1790_);
                lean_inc(v_packageMap_1796_);
                v___x_1798_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1797_,
                    v_packageMap_1796_,
                    v_pkg_1790_,
                );
                if lean_obj_tag(v___x_1798_) == 1 {
                    lean_dec(v_pkg_1790_);
                    v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
                    lean_inc(v_val_1799_);
                    lean_dec_ref_known(v___x_1798_, 1);
                    v_keyName_1800_ = lean_ctor_get(v_val_1799_, 2);
                    lean_inc(v_keyName_1800_);
                    v___x_1801_ = l_Lake_LeanExe_keyword;
                    lean_inc(v_name_1791_);
                    v___x_1802_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1802_, 0, v_val_1799_);
                    lean_ctor_set(v___x_1802_, 1, v_name_1791_);
                    lean_ctor_set(v___x_1802_, 2, v_config_1792_);
                    v___x_1803_ = l_Lake_LeanExe_exeFacet;
                    v___x_1804_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_1804_, 0, v_keyName_1800_);
                    lean_ctor_set(v___x_1804_, 1, v_name_1791_);
                    if v_isShared_1795_ == 0 {
                        lean_ctor_set_tag(v___x_1794_, 1);
                        lean_ctor_set(v___x_1794_, 3, v___x_1803_);
                        lean_ctor_set(v___x_1794_, 2, v___x_1802_);
                        lean_ctor_set(v___x_1794_, 1, v___x_1801_);
                        lean_ctor_set(v___x_1794_, 0, v___x_1804_);
                        v___x_1806_ = v___x_1794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
                        lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1801_);
                        lean_ctor_set(v_reuseFailAlloc_1808_, 2, v___x_1802_);
                        lean_ctor_set(v_reuseFailAlloc_1808_, 3, v___x_1803_);
                        v___x_1806_ = v_reuseFailAlloc_1808_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1798_);
                    lean_del_object(v___x_1794_);
                    lean_dec(v_config_1792_);
                    lean_dec_ref(v_a_1782_);
                    v___x_1809_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1810_ = 1;
                    v___x_1811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1790_,
                        v___x_1810_,
                    );
                    v___x_1812_ = lean_string_append(v___x_1809_, v___x_1811_);
                    lean_dec_ref(v___x_1811_);
                    v___x_1813_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1814_ = lean_string_append(v___x_1812_, v___x_1813_);
                    v___x_1815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1791_,
                        v___x_1810_,
                    );
                    v___x_1816_ = lean_string_append(v___x_1814_, v___x_1815_);
                    lean_dec_ref(v___x_1815_);
                    v___x_1817_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
                    v___x_1819_ = 3;
                    v___x_1820_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1820_, 0, v___x_1818_);
                    lean_ctor_set_uint8(
                        v___x_1820_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1819_,
                    );
                    v___x_1821_ = lean_array_get_size(v_a_1787_);
                    v___x_1822_ = lean_array_push(v_a_1787_, v___x_1820_);
                    v___x_1823_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1823_, 0, v___x_1821_);
                    lean_ctor_set(v___x_1823_, 1, v___x_1822_);
                    return v___x_1823_;
                }
            }
            2 => {
                lean_inc_ref(v_a_1786_);
                lean_inc(v_a_1785_);
                lean_inc(v_a_1784_);
                lean_inc(v_a_1783_);
                v___x_1807_ = lean_apply_7(
                    v_a_1782_,
                    v___x_1806_,
                    v_a_1783_,
                    v_a_1784_,
                    v_a_1785_,
                    v_a_1786_,
                    v_a_1787_,
                    lean_box(0),
                );
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeDecl_fetch___boxed(
    mut v_self_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
    mut v_a_1828_: *mut LeanObject,
    mut v_a_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lake_LeanExeDecl_fetch(
        v_self_1826_,
        v_a_1827_,
        v_a_1828_,
        v_a_1829_,
        v_a_1830_,
        v_a_1831_,
        v_a_1832_,
    );
    lean_dec_ref(v_a_1831_);
    lean_dec(v_a_1830_);
    lean_dec(v_a_1829_);
    lean_dec(v_a_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lake_InputFile_fetch(
    mut v_self_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1843_ = lean_ctor_get(v_self_1835_, 0);
    v_name_1844_ = lean_ctor_get(v_self_1835_, 1);
    v_keyName_1845_ = lean_ctor_get(v_pkg_1843_, 2);
    v___x_1846_ = l_Lake_InputFile_defaultFacet;
    lean_inc(v_name_1844_);
    lean_inc(v_keyName_1845_);
    v___x_1847_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1847_, 0, v_keyName_1845_);
    lean_ctor_set(v___x_1847_, 1, v_name_1844_);
    v___x_1848_ = l_Lake_InputFile_keyword;
    v___x_1849_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1849_, 0, v___x_1847_);
    lean_ctor_set(v___x_1849_, 1, v___x_1848_);
    lean_ctor_set(v___x_1849_, 2, v_self_1835_);
    lean_ctor_set(v___x_1849_, 3, v___x_1846_);
    lean_inc_ref(v_a_1840_);
    lean_inc(v_a_1839_);
    lean_inc(v_a_1838_);
    lean_inc(v_a_1837_);
    v___x_1850_ = lean_apply_7(
        v_a_1836_,
        v___x_1849_,
        v_a_1837_,
        v_a_1838_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
        lean_box(0),
    );
    return v___x_1850_;
}
pub unsafe fn l_Lake_InputFile_fetch___boxed(
    mut v_self_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lake_InputFile_fetch(
        v_self_1851_,
        v_a_1852_,
        v_a_1853_,
        v_a_1854_,
        v_a_1855_,
        v_a_1856_,
        v_a_1857_,
    );
    lean_dec_ref(v_a_1856_);
    lean_dec(v_a_1855_);
    lean_dec(v_a_1854_);
    lean_dec(v_a_1853_);
    return v_res_1859_;
}
pub unsafe fn l_Lake_InputFileDecl_get___redArg(
    mut v_self_1860_: *mut LeanObject,
    mut v_inst_1861_: *mut LeanObject,
    mut v_inst_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = lean_ctor_get(v_inst_1861_, 0);
    lean_inc_ref(v_toApplicative_1864_);
    v_toFunctor_1865_ = lean_ctor_get(v_toApplicative_1864_, 0);
    lean_inc_ref(v_toFunctor_1865_);
    v_toBind_1866_ = lean_ctor_get(v_inst_1861_, 1);
    lean_inc(v_toBind_1866_);
    lean_dec_ref(v_inst_1861_);
    v_toPure_1867_ = lean_ctor_get(v_toApplicative_1864_, 1);
    lean_inc(v_toPure_1867_);
    lean_dec_ref(v_toApplicative_1864_);
    v_pkg_1868_ = lean_ctor_get(v_self_1860_, 0);
    lean_inc_n(v_pkg_1868_, 2);
    v_name_1869_ = lean_ctor_get(v_self_1860_, 1);
    lean_inc(v_name_1869_);
    v_config_1870_ = lean_ctor_get(v_self_1860_, 3);
    lean_inc(v_config_1870_);
    lean_dec_ref(v_self_1860_);
    v_map_1871_ = lean_ctor_get(v_toFunctor_1865_, 0);
    lean_inc_n(v_map_1871_, 2);
    lean_dec_ref(v_toFunctor_1865_);
    v___f_1872_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1873_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1873_, 0, v_name_1869_);
    lean_closure_set(v___f_1873_, 1, v_config_1870_);
    lean_closure_set(v___f_1873_, 2, v_toPure_1867_);
    lean_closure_set(v___f_1873_, 3, v_pkg_1868_);
    lean_closure_set(v___f_1873_, 4, v_inst_1862_);
    v___f_1874_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1874_, 0, v_pkg_1868_);
    v___x_1875_ = lean_apply_4(
        v_map_1871_,
        lean_box(0),
        lean_box(0),
        v___f_1872_,
        v_inst_1863_,
    );
    v___x_1876_ = lean_apply_4(
        v_map_1871_,
        lean_box(0),
        lean_box(0),
        v___f_1874_,
        v___x_1875_,
    );
    v___x_1877_ = lean_apply_4(
        v_toBind_1866_,
        lean_box(0),
        lean_box(0),
        v___x_1876_,
        v___f_1873_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lake_InputFileDecl_get(
    mut v_m_1878_: *mut LeanObject,
    mut v_self_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_inst_1881_: *mut LeanObject,
    mut v_inst_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1883_ = lean_ctor_get(v_inst_1880_, 0);
    lean_inc_ref(v_toApplicative_1883_);
    v_toFunctor_1884_ = lean_ctor_get(v_toApplicative_1883_, 0);
    lean_inc_ref(v_toFunctor_1884_);
    v_toBind_1885_ = lean_ctor_get(v_inst_1880_, 1);
    lean_inc(v_toBind_1885_);
    lean_dec_ref(v_inst_1880_);
    v_toPure_1886_ = lean_ctor_get(v_toApplicative_1883_, 1);
    lean_inc(v_toPure_1886_);
    lean_dec_ref(v_toApplicative_1883_);
    v_pkg_1887_ = lean_ctor_get(v_self_1879_, 0);
    lean_inc_n(v_pkg_1887_, 2);
    v_name_1888_ = lean_ctor_get(v_self_1879_, 1);
    lean_inc(v_name_1888_);
    v_config_1889_ = lean_ctor_get(v_self_1879_, 3);
    lean_inc(v_config_1889_);
    lean_dec_ref(v_self_1879_);
    v_map_1890_ = lean_ctor_get(v_toFunctor_1884_, 0);
    lean_inc_n(v_map_1890_, 2);
    lean_dec_ref(v_toFunctor_1884_);
    v___f_1891_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1892_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1892_, 0, v_name_1888_);
    lean_closure_set(v___f_1892_, 1, v_config_1889_);
    lean_closure_set(v___f_1892_, 2, v_toPure_1886_);
    lean_closure_set(v___f_1892_, 3, v_pkg_1887_);
    lean_closure_set(v___f_1892_, 4, v_inst_1881_);
    v___f_1893_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1893_, 0, v_pkg_1887_);
    v___x_1894_ = lean_apply_4(
        v_map_1890_,
        lean_box(0),
        lean_box(0),
        v___f_1891_,
        v_inst_1882_,
    );
    v___x_1895_ = lean_apply_4(
        v_map_1890_,
        lean_box(0),
        lean_box(0),
        v___f_1893_,
        v___x_1894_,
    );
    v___x_1896_ = lean_apply_4(
        v_toBind_1885_,
        lean_box(0),
        lean_box(0),
        v___x_1895_,
        v___f_1892_,
    );
    return v___x_1896_;
}
pub unsafe fn l_Lake_InputFileDecl_fetch(
    mut v_self_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v_packageMap_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1905_ = lean_ctor_get(v_a_1902_, 1);
                v_pkg_1906_ = lean_ctor_get(v_self_1897_, 0);
                v_name_1907_ = lean_ctor_get(v_self_1897_, 1);
                v_config_1908_ = lean_ctor_get(v_self_1897_, 3);
                v_isSharedCheck_1940_ = (!lean_is_exclusive(v_self_1897_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v_unused_1941_ = lean_ctor_get(v_self_1897_, 2);
                    lean_dec(v_unused_1941_);
                    v___x_1910_ = v_self_1897_;
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_1908_);
                    lean_inc(v_name_1907_);
                    lean_inc(v_pkg_1906_);
                    lean_dec(v_self_1897_);
                    v___x_1910_ = lean_box(0);
                    v_isShared_1911_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_1912_ = lean_ctor_get(v_toContext_1905_, 5);
                v___x_1913_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                lean_inc(v_pkg_1906_);
                lean_inc(v_packageMap_1912_);
                v___x_1914_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_1913_,
                    v_packageMap_1912_,
                    v_pkg_1906_,
                );
                if lean_obj_tag(v___x_1914_) == 1 {
                    lean_dec(v_pkg_1906_);
                    v_val_1915_ = lean_ctor_get(v___x_1914_, 0);
                    lean_inc(v_val_1915_);
                    lean_dec_ref_known(v___x_1914_, 1);
                    v_keyName_1916_ = lean_ctor_get(v_val_1915_, 2);
                    lean_inc(v_keyName_1916_);
                    v___x_1917_ = l_Lake_InputFile_keyword;
                    lean_inc(v_name_1907_);
                    v___x_1918_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1918_, 0, v_val_1915_);
                    lean_ctor_set(v___x_1918_, 1, v_name_1907_);
                    lean_ctor_set(v___x_1918_, 2, v_config_1908_);
                    v___x_1919_ = l_Lake_InputFile_defaultFacet;
                    v___x_1920_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_1920_, 0, v_keyName_1916_);
                    lean_ctor_set(v___x_1920_, 1, v_name_1907_);
                    if v_isShared_1911_ == 0 {
                        lean_ctor_set_tag(v___x_1910_, 1);
                        lean_ctor_set(v___x_1910_, 3, v___x_1919_);
                        lean_ctor_set(v___x_1910_, 2, v___x_1918_);
                        lean_ctor_set(v___x_1910_, 1, v___x_1917_);
                        lean_ctor_set(v___x_1910_, 0, v___x_1920_);
                        v___x_1922_ = v___x_1910_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1920_);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1917_);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 2, v___x_1918_);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 3, v___x_1919_);
                        v___x_1922_ = v_reuseFailAlloc_1924_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1914_);
                    lean_del_object(v___x_1910_);
                    lean_dec(v_config_1908_);
                    lean_dec_ref(v_a_1898_);
                    v___x_1925_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_1926_ = 1;
                    v___x_1927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_1906_,
                        v___x_1926_,
                    );
                    v___x_1928_ = lean_string_append(v___x_1925_, v___x_1927_);
                    lean_dec_ref(v___x_1927_);
                    v___x_1929_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
                    v___x_1931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_1907_,
                        v___x_1926_,
                    );
                    v___x_1932_ = lean_string_append(v___x_1930_, v___x_1931_);
                    lean_dec_ref(v___x_1931_);
                    v___x_1933_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_1934_ = lean_string_append(v___x_1932_, v___x_1933_);
                    v___x_1935_ = 3;
                    v___x_1936_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                    lean_ctor_set_uint8(
                        v___x_1936_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1935_,
                    );
                    v___x_1937_ = lean_array_get_size(v_a_1903_);
                    v___x_1938_ = lean_array_push(v_a_1903_, v___x_1936_);
                    v___x_1939_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1939_, 0, v___x_1937_);
                    lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                    return v___x_1939_;
                }
            }
            2 => {
                lean_inc_ref(v_a_1902_);
                lean_inc(v_a_1901_);
                lean_inc(v_a_1900_);
                lean_inc(v_a_1899_);
                v___x_1923_ = lean_apply_7(
                    v_a_1898_,
                    v___x_1922_,
                    v_a_1899_,
                    v_a_1900_,
                    v_a_1901_,
                    v_a_1902_,
                    v_a_1903_,
                    lean_box(0),
                );
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileDecl_fetch___boxed(
    mut v_self_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
    mut v_a_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1950_: *mut LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lake_InputFileDecl_fetch(
        v_self_1942_,
        v_a_1943_,
        v_a_1944_,
        v_a_1945_,
        v_a_1946_,
        v_a_1947_,
        v_a_1948_,
    );
    lean_dec_ref(v_a_1947_);
    lean_dec(v_a_1946_);
    lean_dec(v_a_1945_);
    lean_dec(v_a_1944_);
    return v_res_1950_;
}
pub unsafe fn l_Lake_InputDir_fetch(
    mut v_self_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1959_ = lean_ctor_get(v_self_1951_, 0);
    v_name_1960_ = lean_ctor_get(v_self_1951_, 1);
    v_keyName_1961_ = lean_ctor_get(v_pkg_1959_, 2);
    v___x_1962_ = l_Lake_InputDir_defaultFacet;
    lean_inc(v_name_1960_);
    lean_inc(v_keyName_1961_);
    v___x_1963_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1963_, 0, v_keyName_1961_);
    lean_ctor_set(v___x_1963_, 1, v_name_1960_);
    v___x_1964_ = l_Lake_InputDir_keyword;
    v___x_1965_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1965_, 0, v___x_1963_);
    lean_ctor_set(v___x_1965_, 1, v___x_1964_);
    lean_ctor_set(v___x_1965_, 2, v_self_1951_);
    lean_ctor_set(v___x_1965_, 3, v___x_1962_);
    lean_inc_ref(v_a_1956_);
    lean_inc(v_a_1955_);
    lean_inc(v_a_1954_);
    lean_inc(v_a_1953_);
    v___x_1966_ = lean_apply_7(
        v_a_1952_,
        v___x_1965_,
        v_a_1953_,
        v_a_1954_,
        v_a_1955_,
        v_a_1956_,
        v_a_1957_,
        lean_box(0),
    );
    return v___x_1966_;
}
pub unsafe fn l_Lake_InputDir_fetch___boxed(
    mut v_self_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lake_InputDir_fetch(
        v_self_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
    );
    lean_dec_ref(v_a_1972_);
    lean_dec(v_a_1971_);
    lean_dec(v_a_1970_);
    lean_dec(v_a_1969_);
    return v_res_1975_;
}
pub unsafe fn l_Lake_InputDirDecl_get___redArg(
    mut v_self_1976_: *mut LeanObject,
    mut v_inst_1977_: *mut LeanObject,
    mut v_inst_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1980_ = lean_ctor_get(v_inst_1977_, 0);
    lean_inc_ref(v_toApplicative_1980_);
    v_toFunctor_1981_ = lean_ctor_get(v_toApplicative_1980_, 0);
    lean_inc_ref(v_toFunctor_1981_);
    v_toBind_1982_ = lean_ctor_get(v_inst_1977_, 1);
    lean_inc(v_toBind_1982_);
    lean_dec_ref(v_inst_1977_);
    v_toPure_1983_ = lean_ctor_get(v_toApplicative_1980_, 1);
    lean_inc(v_toPure_1983_);
    lean_dec_ref(v_toApplicative_1980_);
    v_pkg_1984_ = lean_ctor_get(v_self_1976_, 0);
    lean_inc_n(v_pkg_1984_, 2);
    v_name_1985_ = lean_ctor_get(v_self_1976_, 1);
    lean_inc(v_name_1985_);
    v_config_1986_ = lean_ctor_get(v_self_1976_, 3);
    lean_inc(v_config_1986_);
    lean_dec_ref(v_self_1976_);
    v_map_1987_ = lean_ctor_get(v_toFunctor_1981_, 0);
    lean_inc_n(v_map_1987_, 2);
    lean_dec_ref(v_toFunctor_1981_);
    v___f_1988_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_1989_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1989_, 0, v_name_1985_);
    lean_closure_set(v___f_1989_, 1, v_config_1986_);
    lean_closure_set(v___f_1989_, 2, v_toPure_1983_);
    lean_closure_set(v___f_1989_, 3, v_pkg_1984_);
    lean_closure_set(v___f_1989_, 4, v_inst_1978_);
    v___f_1990_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1990_, 0, v_pkg_1984_);
    v___x_1991_ = lean_apply_4(
        v_map_1987_,
        lean_box(0),
        lean_box(0),
        v___f_1988_,
        v_inst_1979_,
    );
    v___x_1992_ = lean_apply_4(
        v_map_1987_,
        lean_box(0),
        lean_box(0),
        v___f_1990_,
        v___x_1991_,
    );
    v___x_1993_ = lean_apply_4(
        v_toBind_1982_,
        lean_box(0),
        lean_box(0),
        v___x_1992_,
        v___f_1989_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_InputDirDecl_get(
    mut v_m_1994_: *mut LeanObject,
    mut v_self_1995_: *mut LeanObject,
    mut v_inst_1996_: *mut LeanObject,
    mut v_inst_1997_: *mut LeanObject,
    mut v_inst_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1999_ = lean_ctor_get(v_inst_1996_, 0);
    lean_inc_ref(v_toApplicative_1999_);
    v_toFunctor_2000_ = lean_ctor_get(v_toApplicative_1999_, 0);
    lean_inc_ref(v_toFunctor_2000_);
    v_toBind_2001_ = lean_ctor_get(v_inst_1996_, 1);
    lean_inc(v_toBind_2001_);
    lean_dec_ref(v_inst_1996_);
    v_toPure_2002_ = lean_ctor_get(v_toApplicative_1999_, 1);
    lean_inc(v_toPure_2002_);
    lean_dec_ref(v_toApplicative_1999_);
    v_pkg_2003_ = lean_ctor_get(v_self_1995_, 0);
    lean_inc_n(v_pkg_2003_, 2);
    v_name_2004_ = lean_ctor_get(v_self_1995_, 1);
    lean_inc(v_name_2004_);
    v_config_2005_ = lean_ctor_get(v_self_1995_, 3);
    lean_inc(v_config_2005_);
    lean_dec_ref(v_self_1995_);
    v_map_2006_ = lean_ctor_get(v_toFunctor_2000_, 0);
    lean_inc_n(v_map_2006_, 2);
    lean_dec_ref(v_toFunctor_2000_);
    v___f_2007_ = l_Lake_KConfigDecl_get___redArg___closed__0;
    v___f_2008_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2008_, 0, v_name_2004_);
    lean_closure_set(v___f_2008_, 1, v_config_2005_);
    lean_closure_set(v___f_2008_, 2, v_toPure_2002_);
    lean_closure_set(v___f_2008_, 3, v_pkg_2003_);
    lean_closure_set(v___f_2008_, 4, v_inst_1997_);
    v___f_2009_ = lean_alloc_closure(
        l_Lake_KConfigDecl_get___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2009_, 0, v_pkg_2003_);
    v___x_2010_ = lean_apply_4(
        v_map_2006_,
        lean_box(0),
        lean_box(0),
        v___f_2007_,
        v_inst_1998_,
    );
    v___x_2011_ = lean_apply_4(
        v_map_2006_,
        lean_box(0),
        lean_box(0),
        v___f_2009_,
        v___x_2010_,
    );
    v___x_2012_ = lean_apply_4(
        v_toBind_2001_,
        lean_box(0),
        lean_box(0),
        v___x_2011_,
        v___f_2008_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_InputDirDecl_fetch(
    mut v_self_2013_: *mut LeanObject,
    mut v_a_2014_: *mut LeanObject,
    mut v_a_2015_: *mut LeanObject,
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v_packageMap_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_2021_ = lean_ctor_get(v_a_2018_, 1);
                v_pkg_2022_ = lean_ctor_get(v_self_2013_, 0);
                v_name_2023_ = lean_ctor_get(v_self_2013_, 1);
                v_config_2024_ = lean_ctor_get(v_self_2013_, 3);
                v_isSharedCheck_2056_ = (!lean_is_exclusive(v_self_2013_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = lean_ctor_get(v_self_2013_, 2);
                    lean_dec(v_unused_2057_);
                    v___x_2026_ = v_self_2013_;
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_2024_);
                    lean_inc(v_name_2023_);
                    lean_inc(v_pkg_2022_);
                    lean_dec(v_self_2013_);
                    v___x_2026_ = lean_box(0);
                    v_isShared_2027_ = v_isSharedCheck_2056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packageMap_2028_ = lean_ctor_get(v_toContext_2021_, 5);
                v___x_2029_ = l_Lake_KConfigDecl_get___redArg___lam__2___closed__0;
                lean_inc(v_pkg_2022_);
                lean_inc(v_packageMap_2028_);
                v___x_2030_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                    v___x_2029_,
                    v_packageMap_2028_,
                    v_pkg_2022_,
                );
                if lean_obj_tag(v___x_2030_) == 1 {
                    lean_dec(v_pkg_2022_);
                    v_val_2031_ = lean_ctor_get(v___x_2030_, 0);
                    lean_inc(v_val_2031_);
                    lean_dec_ref_known(v___x_2030_, 1);
                    v_keyName_2032_ = lean_ctor_get(v_val_2031_, 2);
                    lean_inc(v_keyName_2032_);
                    v___x_2033_ = l_Lake_InputDir_keyword;
                    lean_inc(v_name_2023_);
                    v___x_2034_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2034_, 0, v_val_2031_);
                    lean_ctor_set(v___x_2034_, 1, v_name_2023_);
                    lean_ctor_set(v___x_2034_, 2, v_config_2024_);
                    v___x_2035_ = l_Lake_InputDir_defaultFacet;
                    v___x_2036_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_2036_, 0, v_keyName_2032_);
                    lean_ctor_set(v___x_2036_, 1, v_name_2023_);
                    if v_isShared_2027_ == 0 {
                        lean_ctor_set_tag(v___x_2026_, 1);
                        lean_ctor_set(v___x_2026_, 3, v___x_2035_);
                        lean_ctor_set(v___x_2026_, 2, v___x_2034_);
                        lean_ctor_set(v___x_2026_, 1, v___x_2033_);
                        lean_ctor_set(v___x_2026_, 0, v___x_2036_);
                        v___x_2038_ = v___x_2026_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
                        lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2033_);
                        lean_ctor_set(v_reuseFailAlloc_2040_, 2, v___x_2034_);
                        lean_ctor_set(v_reuseFailAlloc_2040_, 3, v___x_2035_);
                        v___x_2038_ = v_reuseFailAlloc_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2030_);
                    lean_del_object(v___x_2026_);
                    lean_dec(v_config_2024_);
                    lean_dec_ref(v_a_2014_);
                    v___x_2041_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__0;
                    v___x_2042_ = 1;
                    v___x_2043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_pkg_2022_,
                        v___x_2042_,
                    );
                    v___x_2044_ = lean_string_append(v___x_2041_, v___x_2043_);
                    lean_dec_ref(v___x_2043_);
                    v___x_2045_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__1;
                    v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
                    v___x_2047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2023_,
                        v___x_2042_,
                    );
                    v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
                    lean_dec_ref(v___x_2047_);
                    v___x_2049_ = l_Lake_KConfigDecl_get___redArg___lam__1___closed__2;
                    v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
                    v___x_2051_ = 3;
                    v___x_2052_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2052_, 0, v___x_2050_);
                    lean_ctor_set_uint8(
                        v___x_2052_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2051_,
                    );
                    v___x_2053_ = lean_array_get_size(v_a_2019_);
                    v___x_2054_ = lean_array_push(v_a_2019_, v___x_2052_);
                    v___x_2055_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2055_, 0, v___x_2053_);
                    lean_ctor_set(v___x_2055_, 1, v___x_2054_);
                    return v___x_2055_;
                }
            }
            2 => {
                lean_inc_ref(v_a_2018_);
                lean_inc(v_a_2017_);
                lean_inc(v_a_2016_);
                lean_inc(v_a_2015_);
                v___x_2039_ = lean_apply_7(
                    v_a_2014_,
                    v___x_2038_,
                    v_a_2015_,
                    v_a_2016_,
                    v_a_2017_,
                    v_a_2018_,
                    v_a_2019_,
                    lean_box(0),
                );
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirDecl_fetch___boxed(
    mut v_self_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2066_: *mut LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lake_InputDirDecl_fetch(
        v_self_2058_,
        v_a_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
        v_a_2064_,
    );
    lean_dec_ref(v_a_2063_);
    lean_dec(v_a_2062_);
    lean_dec(v_a_2061_);
    lean_dec(v_a_2060_);
    return v_res_2066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Targets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Targets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Targets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Targets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Targets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Targets(builtin);
}
