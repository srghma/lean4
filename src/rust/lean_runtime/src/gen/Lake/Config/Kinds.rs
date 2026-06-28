// Lean compiler output
// Module: Lake.Config.Kinds
// Imports: Init.Prelude
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Lean_Name_mkStr1, runtime_initialize_Init_Prelude,
};
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Lake_Package_keyword___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 97, 99, 107, 97, 103, 101, 0],
};
static mut l_Lake_Package_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_Package_keyword___closed__0_value) as *mut LeanObject,
        6671755061125946191 as *mut LeanObject,
    ],
};
static mut l_Lake_Package_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Package_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Package_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_keyword___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l_Lake_Module_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_Module_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_Module_keyword___closed__0_value) as *mut LeanObject,
        5134674735115079031 as *mut LeanObject,
    ],
};
static mut l_Lake_Module_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanLib_keyword___closed__0_value: LeanStringObject<9> = LeanStringObject {
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
static mut l_Lake_LeanLib_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__0_value) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanLib_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanLib_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanLib_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanLib_configKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExe_keyword___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0],
};
static mut l_Lake_LeanExe_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExe_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__0_value) as *mut LeanObject,
        10587356296225942211 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExe_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanExe_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanExe_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanExe_configKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_ExternLib_keyword___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0],
};
static mut l_Lake_ExternLib_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_ExternLib_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__0_value) as *mut LeanObject,
        11562366611225967008 as *mut LeanObject,
    ],
};
static mut l_Lake_ExternLib_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_ExternLib_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_ExternLib_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_ExternLib_configKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputFile_keyword___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0],
};
static mut l_Lake_InputFile_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputFile_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__0_value) as *mut LeanObject,
        4067501922346325234 as *mut LeanObject,
    ],
};
static mut l_Lake_InputFile_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputFile_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputFile_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputFile_configKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_keyword___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputDir_keyword___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0],
};
static mut l_Lake_InputDir_keyword___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDir_keyword___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__0_value) as *mut LeanObject,
        9710019104504222840 as *mut LeanObject,
    ],
};
static mut l_Lake_InputDir_keyword___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputDir_keyword: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputDir_facetKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_InputDir_configKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_keyword___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [80, 97, 99, 107, 97, 103, 101, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [77, 111, 100, 117, 108, 101, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [76, 101, 97, 110, 76, 105, 98, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [76, 101, 97, 110, 69, 120, 101, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [69, 120, 116, 101, 114, 110, 76, 105, 98, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [73, 110, 112, 117, 116, 70, 105, 108, 101, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6_value
) as *mut LeanObject;
pub static l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [73, 110, 112, 117, 116, 68, 105, 114, 0],
};
static mut l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7_value
) as *mut LeanObject;
pub unsafe fn l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(
    mut v_ns_130_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ns_130_) {
        0 => {
            return v_ns_130_;
        }
        1 => {
            let mut v_pre_131_: *mut LeanObject = core::ptr::null_mut();
            v_pre_131_ = lean_ctor_get(v_ns_130_, 0);
            match lean_obj_tag(v_pre_131_) {
                0 => {
                    return v_pre_131_;
                }
                1 => {
                    let mut v_pre_132_: *mut LeanObject = core::ptr::null_mut();
                    v_pre_132_ = lean_ctor_get(v_pre_131_, 0);
                    if lean_obj_tag(v_pre_132_) == 0 {
                        let mut v_str_133_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_134_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_136_: u8 = 0;
                        v_str_133_ = lean_ctor_get(v_ns_130_, 1);
                        v_str_134_ = lean_ctor_get(v_pre_131_, 1);
                        v___x_135_ =
                            l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0;
                        v___x_136_ = lean_string_dec_eq(v_str_134_, v___x_135_);
                        if v___x_136_ == 0 {
                            return v_pre_132_;
                        } else {
                            let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_138_: u8 = 0;
                            v___x_137_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1;
                            v___x_138_ = lean_string_dec_eq(v_str_133_, v___x_137_);
                            if v___x_138_ == 0 {
                                let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_140_: u8 = 0;
                                v___x_139_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2;
                                v___x_140_ = lean_string_dec_eq(v_str_133_, v___x_139_);
                                if v___x_140_ == 0 {
                                    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_142_: u8 = 0;
                                    v___x_141_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3;
                                    v___x_142_ = lean_string_dec_eq(v_str_133_, v___x_141_);
                                    if v___x_142_ == 0 {
                                        let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_144_: u8 = 0;
                                        v___x_143_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4;
                                        v___x_144_ = lean_string_dec_eq(v_str_133_, v___x_143_);
                                        if v___x_144_ == 0 {
                                            let mut v___x_145_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_146_: u8 = 0;
                                            v___x_145_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5;
                                            v___x_146_ = lean_string_dec_eq(v_str_133_, v___x_145_);
                                            if v___x_146_ == 0 {
                                                let mut v___x_147_: *mut LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_148_: u8 = 0;
                                                v___x_147_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6;
                                                v___x_148_ =
                                                    lean_string_dec_eq(v_str_133_, v___x_147_);
                                                if v___x_148_ == 0 {
                                                    let mut v___x_149_: *mut LeanObject =
                                                        core::ptr::null_mut();
                                                    let mut v___x_150_: u8 = 0;
                                                    v___x_149_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7;
                                                    v___x_150_ =
                                                        lean_string_dec_eq(v_str_133_, v___x_149_);
                                                    if v___x_150_ == 0 {
                                                        return v_pre_132_;
                                                    } else {
                                                        let mut v___x_151_: *mut LeanObject =
                                                            core::ptr::null_mut();
                                                        v___x_151_ = l_Lake_InputDir_keyword;
                                                        return v___x_151_;
                                                    }
                                                } else {
                                                    let mut v___x_152_: *mut LeanObject =
                                                        core::ptr::null_mut();
                                                    v___x_152_ = l_Lake_InputFile_keyword;
                                                    return v___x_152_;
                                                }
                                            } else {
                                                let mut v___x_153_: *mut LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_153_ = l_Lake_ExternLib_keyword;
                                                return v___x_153_;
                                            }
                                        } else {
                                            let mut v___x_154_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            v___x_154_ = l_Lake_LeanExe_keyword;
                                            return v___x_154_;
                                        }
                                    } else {
                                        let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
                                        v___x_155_ = l_Lake_LeanLib_keyword___closed__1;
                                        return v___x_155_;
                                    }
                                } else {
                                    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
                                    v___x_156_ = l_Lake_Module_keyword;
                                    return v___x_156_;
                                }
                            } else {
                                let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
                                v___x_157_ = l_Lake_Package_keyword;
                                return v___x_157_;
                            }
                        }
                    } else {
                        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
                        v___x_158_ = lean_box(0);
                        return v___x_158_;
                    }
                }
                _ => {
                    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
                    v___x_159_ = lean_box(0);
                    return v___x_159_;
                }
            }
        }
        _ => {
            let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
            v___x_160_ = lean_box(0);
            return v___x_160_;
        }
    }
}
pub unsafe fn l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___boxed(
    mut v_ns_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_162_: *mut LeanObject = core::ptr::null_mut();
    v_res_162_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(v_ns_161_);
    lean_dec(v_ns_161_);
    return v_res_162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Kinds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Kinds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Kinds(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Kinds(builtin);
}
