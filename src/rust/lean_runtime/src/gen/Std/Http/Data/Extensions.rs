// Lean compiler output
// Module: Std.Http.Data.Extensions
// Imports: Init.Dynamic Init.Data.String.Basic Std.Data.TreeMap
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Dynamic::{
    initialize_Init_Dynamic, l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg,
    l___private_Init_Dynamic_0__Dynamic_typeNameImpl, runtime_initialize_Init_Dynamic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___redArg,
};
use crate::r#gen::Std::Data::TreeMap::{
    initialize_Std_Data_TreeMap, runtime_initialize_Std_Data_TreeMap,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_dec_lt;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_tag,
};
pub static mut l_Std_Http_instInhabitedExtensions_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedExtensions: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Extensions_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Extensions_get___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Extensions_get___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Extensions_get___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Http_Extensions_compareName(
    mut v_x_91_: *mut LeanObject,
    mut v_x_92_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_91_) {
        0 => {
            if lean_obj_tag(v_x_92_) == 0 {
                let mut v___x_93_: u8 = 0;
                v___x_93_ = 1;
                return v___x_93_;
            } else {
                let mut v___x_94_: u8 = 0;
                v___x_94_ = 0;
                return v___x_94_;
            }
        }
        1 => match lean_obj_tag(v_x_92_) {
            0 => {
                let mut v___x_95_: u8 = 0;
                v___x_95_ = 2;
                return v___x_95_;
            }
            1 => {
                let mut v_pre_96_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_97_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pre_98_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_99_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_100_: u8 = 0;
                v_pre_96_ = lean_ctor_get(v_x_91_, 0);
                v_str_97_ = lean_ctor_get(v_x_91_, 1);
                v_pre_98_ = lean_ctor_get(v_x_92_, 0);
                v_str_99_ = lean_ctor_get(v_x_92_, 1);
                v___x_100_ = l_Std_Http_Extensions_compareName(v_pre_96_, v_pre_98_);
                if v___x_100_ == 1 {
                    let mut v___x_101_: u8 = 0;
                    v___x_101_ = lean_string_dec_lt(v_str_97_, v_str_99_);
                    if v___x_101_ == 0 {
                        let mut v___x_102_: u8 = 0;
                        v___x_102_ = lean_string_dec_eq(v_str_97_, v_str_99_);
                        if v___x_102_ == 0 {
                            let mut v___x_103_: u8 = 0;
                            v___x_103_ = 2;
                            return v___x_103_;
                        } else {
                            return v___x_100_;
                        }
                    } else {
                        let mut v___x_104_: u8 = 0;
                        v___x_104_ = 0;
                        return v___x_104_;
                    }
                } else {
                    return v___x_100_;
                }
            }
            _ => {
                let mut v___x_105_: u8 = 0;
                v___x_105_ = 0;
                return v___x_105_;
            }
        },
        _ => {
            if lean_obj_tag(v_x_92_) == 2 {
                let mut v_pre_106_: *mut LeanObject = core::ptr::null_mut();
                let mut v_i_107_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pre_108_: *mut LeanObject = core::ptr::null_mut();
                let mut v_i_109_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_110_: u8 = 0;
                v_pre_106_ = lean_ctor_get(v_x_91_, 0);
                v_i_107_ = lean_ctor_get(v_x_91_, 1);
                v_pre_108_ = lean_ctor_get(v_x_92_, 0);
                v_i_109_ = lean_ctor_get(v_x_92_, 1);
                v___x_110_ = l_Std_Http_Extensions_compareName(v_pre_106_, v_pre_108_);
                if v___x_110_ == 1 {
                    let mut v___x_111_: u8 = 0;
                    v___x_111_ = lean_nat_dec_lt(v_i_107_, v_i_109_);
                    if v___x_111_ == 0 {
                        let mut v___x_112_: u8 = 0;
                        v___x_112_ = lean_nat_dec_eq(v_i_107_, v_i_109_);
                        if v___x_112_ == 0 {
                            let mut v___x_113_: u8 = 0;
                            v___x_113_ = 2;
                            return v___x_113_;
                        } else {
                            return v___x_110_;
                        }
                    } else {
                        let mut v___x_114_: u8 = 0;
                        v___x_114_ = 0;
                        return v___x_114_;
                    }
                } else {
                    return v___x_110_;
                }
            } else {
                let mut v___x_115_: u8 = 0;
                v___x_115_ = 2;
                return v___x_115_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_Extensions_compareName___boxed(
    mut v_x_116_: *mut LeanObject,
    mut v_x_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_118_: u8 = 0;
    let mut v_r_119_: *mut LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_Http_Extensions_compareName(v_x_116_, v_x_117_);
    lean_dec(v_x_117_);
    lean_dec(v_x_116_);
    v_r_119_ = lean_box((v_res_118_) as usize);
    return v_r_119_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedExtensions_default() -> *mut LeanObject {
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    v___x_120_ = lean_box(1);
    return v___x_120_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedExtensions() -> *mut LeanObject {
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    v___x_121_ = lean_box(1);
    return v___x_121_;
}
pub unsafe fn _init_l_Std_Http_Extensions_empty() -> *mut LeanObject {
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    v___x_122_ = lean_box(1);
    return v___x_122_;
}
pub unsafe fn l_Std_Http_Extensions_get___redArg(
    mut v_x_124_: *mut LeanObject,
    mut v_inst_125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    v___x_126_ = l_Std_Http_Extensions_get___redArg___closed__0;
    lean_inc(v_inst_125_);
    v___x_127_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_126_, v_x_124_, v_inst_125_);
    if lean_obj_tag(v___x_127_) == 0 {
        let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_125_);
        v___x_128_ = lean_box(0);
        return v___x_128_;
    } else {
        let mut v_val_129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
        v_val_129_ = lean_ctor_get(v___x_127_, 0);
        lean_inc(v_val_129_);
        lean_dec_ref_known(v___x_127_, 1);
        v___x_130_ =
            l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_129_, v_inst_125_);
        lean_dec(v_inst_125_);
        lean_dec(v_val_129_);
        return v___x_130_;
    }
}
pub unsafe fn l_Std_Http_Extensions_get(
    mut v_x_131_: *mut LeanObject,
    mut v_00_u03b1_132_: *mut LeanObject,
    mut v_inst_133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Std_Http_Extensions_get___redArg___closed__0;
    lean_inc(v_inst_133_);
    v___x_135_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_134_, v_x_131_, v_inst_133_);
    if lean_obj_tag(v___x_135_) == 0 {
        let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_133_);
        v___x_136_ = lean_box(0);
        return v___x_136_;
    } else {
        let mut v_val_137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
        v_val_137_ = lean_ctor_get(v___x_135_, 0);
        lean_inc(v_val_137_);
        lean_dec_ref_known(v___x_135_, 1);
        v___x_138_ =
            l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_137_, v_inst_133_);
        lean_dec(v_inst_133_);
        lean_dec(v_val_137_);
        return v___x_138_;
    }
}
pub unsafe fn l_Std_Http_Extensions_insert___redArg(
    mut v_x_139_: *mut LeanObject,
    mut v_inst_140_: *mut LeanObject,
    mut v_data_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dyn_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    v_dyn_142_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_dyn_142_, 0, v_inst_140_);
    lean_ctor_set(v_dyn_142_, 1, v_data_141_);
    v___x_143_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_144_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_142_);
    v___x_145_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_143_, v___x_144_, v_dyn_142_, v_x_139_);
    return v___x_145_;
}
pub unsafe fn l_Std_Http_Extensions_insert(
    mut v_00_u03b1_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_inst_148_: *mut LeanObject,
    mut v_data_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dyn_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    v_dyn_150_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_dyn_150_, 0, v_inst_148_);
    lean_ctor_set(v_dyn_150_, 1, v_data_149_);
    v___x_151_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_152_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_150_);
    v___x_153_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_151_, v___x_152_, v_dyn_150_, v_x_147_);
    return v___x_153_;
}
pub unsafe fn l_Std_Http_Extensions_remove___redArg(
    mut v_x_154_: *mut LeanObject,
    mut v_inst_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_156_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_157_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_156_, v_inst_155_, v_x_154_);
    return v___x_157_;
}
pub unsafe fn l_Std_Http_Extensions_remove(
    mut v_x_158_: *mut LeanObject,
    mut v_00_u03b1_159_: *mut LeanObject,
    mut v_inst_160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    v___x_161_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_162_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_161_, v_inst_160_, v_x_158_);
    return v___x_162_;
}
pub unsafe fn l_Std_Http_Extensions_contains___redArg(
    mut v_x_163_: *mut LeanObject,
    mut v_inst_164_: *mut LeanObject,
) -> u8 {
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: u8 = 0;
    v___x_165_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_166_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_165_, v_inst_164_, v_x_163_);
    return v___x_166_;
}
pub unsafe fn l_Std_Http_Extensions_contains___redArg___boxed(
    mut v_x_167_: *mut LeanObject,
    mut v_inst_168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_169_: u8 = 0;
    let mut v_r_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_169_ = l_Std_Http_Extensions_contains___redArg(v_x_167_, v_inst_168_);
    v_r_170_ = lean_box((v_res_169_) as usize);
    return v_r_170_;
}
pub unsafe fn l_Std_Http_Extensions_contains(
    mut v_x_171_: *mut LeanObject,
    mut v_00_u03b1_172_: *mut LeanObject,
    mut v_inst_173_: *mut LeanObject,
) -> u8 {
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: u8 = 0;
    v___x_174_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_175_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_174_, v_inst_173_, v_x_171_);
    return v___x_175_;
}
pub unsafe fn l_Std_Http_Extensions_contains___boxed(
    mut v_x_176_: *mut LeanObject,
    mut v_00_u03b1_177_: *mut LeanObject,
    mut v_inst_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_179_: u8 = 0;
    let mut v_r_180_: *mut LeanObject = core::ptr::null_mut();
    v_res_179_ = l_Std_Http_Extensions_contains(v_x_176_, v_00_u03b1_177_, v_inst_178_);
    v_r_180_ = lean_box((v_res_179_) as usize);
    return v_r_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Http_instInhabitedExtensions_default = _init_l_Std_Http_instInhabitedExtensions_default();
    lean_mark_persistent(l_Std_Http_instInhabitedExtensions_default);
    l_Std_Http_instInhabitedExtensions = _init_l_Std_Http_instInhabitedExtensions();
    lean_mark_persistent(l_Std_Http_instInhabitedExtensions);
    l_Std_Http_Extensions_empty = _init_l_Std_Http_Extensions_empty();
    lean_mark_persistent(l_Std_Http_Extensions_empty);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Extensions(builtin);
}
