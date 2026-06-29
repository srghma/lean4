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
pub static mut l_Std_Http_instInhabitedExtensions_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedExtensions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Extensions_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Extensions_get___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Extensions_get___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Extensions_get___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Extensions_compareName(
    mut v_x_91_: *mut crate::leanh::LeanObject,
    mut v_x_92_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_91_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_92_) == 0 {
                let mut v___x_93_: u8 = 0;
                v___x_93_ = 1;
                return v___x_93_;
            } else {
                let mut v___x_94_: u8 = 0;
                v___x_94_ = 0;
                return v___x_94_;
            }
        }
        1 => match crate::leanh::lean_obj_tag(v_x_92_) {
            0 => {
                let mut v___x_95_: u8 = 0;
                v___x_95_ = 2;
                return v___x_95_;
            }
            1 => {
                let mut v_pre_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pre_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_100_: u8 = 0;
                v_pre_96_ = crate::leanh::lean_ctor_get(v_x_91_, 0);
                v_str_97_ = crate::leanh::lean_ctor_get(v_x_91_, 1);
                v_pre_98_ = crate::leanh::lean_ctor_get(v_x_92_, 0);
                v_str_99_ = crate::leanh::lean_ctor_get(v_x_92_, 1);
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
            if crate::leanh::lean_obj_tag(v_x_92_) == 2 {
                let mut v_pre_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_i_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pre_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_i_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_110_: u8 = 0;
                v_pre_106_ = crate::leanh::lean_ctor_get(v_x_91_, 0);
                v_i_107_ = crate::leanh::lean_ctor_get(v_x_91_, 1);
                v_pre_108_ = crate::leanh::lean_ctor_get(v_x_92_, 0);
                v_i_109_ = crate::leanh::lean_ctor_get(v_x_92_, 1);
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
    mut v_x_116_: *mut crate::leanh::LeanObject,
    mut v_x_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: u8 = 0;
    let mut v_r_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_Http_Extensions_compareName(v_x_116_, v_x_117_);
    crate::leanh::lean_dec(v_x_117_);
    crate::leanh::lean_dec(v_x_116_);
    v_r_119_ = crate::leanh::lean_box((v_res_118_) as usize);
    return v_r_119_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedExtensions_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120_ = crate::leanh::lean_box(1);
    return v___x_120_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedExtensions() -> *mut crate::leanh::LeanObject {
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = crate::leanh::lean_box(1);
    return v___x_121_;
}
pub unsafe fn _init_l_Std_Http_Extensions_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = crate::leanh::lean_box(1);
    return v___x_122_;
}
pub unsafe fn l_Std_Http_Extensions_get___redArg(
    mut v_x_124_: *mut crate::leanh::LeanObject,
    mut v_inst_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_126_ = l_Std_Http_Extensions_get___redArg___closed__0;
    crate::leanh::lean_inc(v_inst_125_);
    v___x_127_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_126_, v_x_124_, v_inst_125_);
    if crate::leanh::lean_obj_tag(v___x_127_) == 0 {
        let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_125_);
        v___x_128_ = crate::leanh::lean_box(0);
        return v___x_128_;
    } else {
        let mut v_val_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_129_ = crate::leanh::lean_ctor_get(v___x_127_, 0);
        crate::leanh::lean_inc(v_val_129_);
        crate::leanh::lean_dec_ref_known(v___x_127_, 1);
        v___x_130_ =
            l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_129_, v_inst_125_);
        crate::leanh::lean_dec(v_inst_125_);
        crate::leanh::lean_dec(v_val_129_);
        return v___x_130_;
    }
}
pub unsafe fn l_Std_Http_Extensions_get(
    mut v_x_131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_132_: *mut crate::leanh::LeanObject,
    mut v_inst_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Std_Http_Extensions_get___redArg___closed__0;
    crate::leanh::lean_inc(v_inst_133_);
    v___x_135_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_134_, v_x_131_, v_inst_133_);
    if crate::leanh::lean_obj_tag(v___x_135_) == 0 {
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_133_);
        v___x_136_ = crate::leanh::lean_box(0);
        return v___x_136_;
    } else {
        let mut v_val_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_137_ = crate::leanh::lean_ctor_get(v___x_135_, 0);
        crate::leanh::lean_inc(v_val_137_);
        crate::leanh::lean_dec_ref_known(v___x_135_, 1);
        v___x_138_ =
            l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_137_, v_inst_133_);
        crate::leanh::lean_dec(v_inst_133_);
        crate::leanh::lean_dec(v_val_137_);
        return v___x_138_;
    }
}
pub unsafe fn l_Std_Http_Extensions_insert___redArg(
    mut v_x_139_: *mut crate::leanh::LeanObject,
    mut v_inst_140_: *mut crate::leanh::LeanObject,
    mut v_data_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dyn_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dyn_142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_dyn_142_, 0, v_inst_140_);
    crate::leanh::lean_ctor_set(v_dyn_142_, 1, v_data_141_);
    v___x_143_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_144_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_142_);
    v___x_145_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_143_, v___x_144_, v_dyn_142_, v_x_139_);
    return v___x_145_;
}
pub unsafe fn l_Std_Http_Extensions_insert(
    mut v_00_u03b1_146_: *mut crate::leanh::LeanObject,
    mut v_x_147_: *mut crate::leanh::LeanObject,
    mut v_inst_148_: *mut crate::leanh::LeanObject,
    mut v_data_149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dyn_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dyn_150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_dyn_150_, 0, v_inst_148_);
    crate::leanh::lean_ctor_set(v_dyn_150_, 1, v_data_149_);
    v___x_151_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_152_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_150_);
    v___x_153_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_151_, v___x_152_, v_dyn_150_, v_x_147_);
    return v___x_153_;
}
pub unsafe fn l_Std_Http_Extensions_remove___redArg(
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_inst_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_157_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_156_, v_inst_155_, v_x_154_);
    return v___x_157_;
}
pub unsafe fn l_Std_Http_Extensions_remove(
    mut v_x_158_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_159_: *mut crate::leanh::LeanObject,
    mut v_inst_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_162_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_161_, v_inst_160_, v_x_158_);
    return v___x_162_;
}
pub unsafe fn l_Std_Http_Extensions_contains___redArg(
    mut v_x_163_: *mut crate::leanh::LeanObject,
    mut v_inst_164_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: u8 = 0;
    v___x_165_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_166_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_165_, v_inst_164_, v_x_163_);
    return v___x_166_;
}
pub unsafe fn l_Std_Http_Extensions_contains___redArg___boxed(
    mut v_x_167_: *mut crate::leanh::LeanObject,
    mut v_inst_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_169_: u8 = 0;
    let mut v_r_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_169_ = l_Std_Http_Extensions_contains___redArg(v_x_167_, v_inst_168_);
    v_r_170_ = crate::leanh::lean_box((v_res_169_) as usize);
    return v_r_170_;
}
pub unsafe fn l_Std_Http_Extensions_contains(
    mut v_x_171_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
    mut v_inst_173_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: u8 = 0;
    v___x_174_ = l_Std_Http_Extensions_get___redArg___closed__0;
    v___x_175_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_174_, v_inst_173_, v_x_171_);
    return v___x_175_;
}
pub unsafe fn l_Std_Http_Extensions_contains___boxed(
    mut v_x_176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_177_: *mut crate::leanh::LeanObject,
    mut v_inst_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_179_: u8 = 0;
    let mut v_r_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_179_ = l_Std_Http_Extensions_contains(v_x_176_, v_00_u03b1_177_, v_inst_178_);
    v_r_180_ = crate::leanh::lean_box((v_res_179_) as usize);
    return v_r_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Extensions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_instInhabitedExtensions_default = _init_l_Std_Http_instInhabitedExtensions_default();
    crate::leanh::lean_mark_persistent(l_Std_Http_instInhabitedExtensions_default);
    l_Std_Http_instInhabitedExtensions = _init_l_Std_Http_instInhabitedExtensions();
    crate::leanh::lean_mark_persistent(l_Std_Http_instInhabitedExtensions);
    l_Std_Http_Extensions_empty = _init_l_Std_Http_Extensions_empty();
    crate::leanh::lean_mark_persistent(l_Std_Http_Extensions_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Extensions(
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
pub unsafe fn initialize_Std_Http_Data_Extensions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Extensions(builtin);
}
