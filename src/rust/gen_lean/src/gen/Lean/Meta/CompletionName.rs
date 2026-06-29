// Lean compiler output
// Module: Lean.Meta.CompletionName
// Imports: Lean.Meta.Match.MatcherInfo
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Lean::AuxRecursor::{l_Lean_isAuxRecursor, l_Lean_isNoConfusion};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_TagDeclarationExtension_isTagged, l_Lean_TagDeclarationExtension_tag,
    l_Lean_mkTagDeclarationExtension,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, lean_is_matcher,
    runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isRecCore;
use crate::r#gen::Lean::PrivateName::l_Lean_privateHeader;
use crate::ffi::{
    lean_name_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
pub static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 66, 108, 97, 99, 107, 76, 105, 115, 116, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12848672962440955961 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_completionBlackListExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_78_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
    v___x_79_ = crate::leanh::lean_box(2);
    v___x_80_ = l_Lean_mkTagDeclarationExtension(v___x_78_, v___x_79_);
    return v___x_80_;
}
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(
    mut v_a_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_82_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
    return v_res_82_;
}
pub unsafe fn l_Lean_Meta_addToCompletionBlackList(
    mut v_env_83_: *mut crate::leanh::LeanObject,
    mut v_declName_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_85_ = l_Lean_Meta_completionBlackListExt;
    v___x_86_ = l_Lean_TagDeclarationExtension_tag(v___x_85_, v_env_83_, v_declName_84_);
    return v___x_86_;
}
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(
    mut v_x_87_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_pre_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_91_: u8 = 0;
    let mut v___y_94_: u32 = 0;
    let mut v___x_95_: u32 = 0;
    let mut v___x_96_: u8 = 0;
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: u8 = 0;
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u32 = 0;
    let mut v_val_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: u32 = 0;
    let mut v_pre_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_87_) {
                1 => {
                    v_pre_88_ = crate::leanh::lean_ctor_get(v_x_87_, 0);
                    v_str_89_ = crate::leanh::lean_ctor_get(v_x_87_, 1);
                    v___x_100_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_101_ = lean_string_utf8_byte_size(v_str_89_);
                    crate::leanh::lean_inc_ref(v_str_89_);
                    v___x_102_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_102_, 0, v_str_89_);
                    crate::leanh::lean_ctor_set(v___x_102_, 1, v___x_100_);
                    crate::leanh::lean_ctor_set(v___x_102_, 2, v___x_101_);
                    v___x_103_ = l_String_Slice_Pos_get_x3f(v___x_102_, v___x_100_);
                    crate::leanh::lean_dec_ref_known(v___x_102_, 3);
                    if crate::leanh::lean_obj_tag(v___x_103_) == 0 {
                        v___x_104_ = 65;
                        v___y_94_ = v___x_104_;
                        state = 2;
                        continue;
                    } else {
                        v_val_105_ = crate::leanh::lean_ctor_get(v___x_103_, 0);
                        crate::leanh::lean_inc(v_val_105_);
                        crate::leanh::lean_dec_ref_known(v___x_103_, 1);
                        v___x_106_ = crate::leanh::lean_unbox_uint32(v_val_105_);
                        crate::leanh::lean_dec(v_val_105_);
                        v___y_94_ = v___x_106_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_pre_107_ = crate::leanh::lean_ctor_get(v_x_87_, 0);
                    v_x_87_ = v_pre_107_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_109_ = 0;
                    return v___x_109_;
                }
            },
            1 => {
                if v___y_91_ == 0 {
                    v_x_87_ = v_pre_88_;
                    state = 0;
                    continue;
                } else {
                    return v___y_91_;
                }
            }
            2 => {
                v___x_95_ = 95;
                v___x_96_ = lean_uint32_dec_eq(v___y_94_, v___x_95_);
                if v___x_96_ == 0 {
                    v___y_91_ = v___x_96_;
                    state = 1;
                    continue;
                } else {
                    v___x_97_ = l_Lean_privateHeader;
                    v___x_98_ = lean_name_eq(v_x_87_, v___x_97_);
                    if v___x_98_ == 0 {
                        v___y_91_ = v___x_96_;
                        state = 1;
                        continue;
                    } else {
                        v_x_87_ = v_pre_88_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(
    mut v_x_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_111_: u8 = 0;
    let mut v_r_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ =
        l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_x_110_);
    crate::leanh::lean_dec(v_x_110_);
    v_r_112_ = crate::leanh::lean_box((v_res_111_) as usize);
    return v_r_112_;
}
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(
    mut v_env_113_: *mut crate::leanh::LeanObject,
    mut v_declName_114_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_116_: u8 = 0;
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: u8 = 0;
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: u8 = 0;
    let mut v___x_124_: u8 = 0;
    let mut v___x_125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_124_ =
                    l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(
                        v_declName_114_,
                    );
                if v___x_124_ == 0 {
                    crate::leanh::lean_inc(v_declName_114_);
                    crate::leanh::lean_inc_ref(v_env_113_);
                    v___x_125_ = l_Lean_isAuxRecursor(v_env_113_, v_declName_114_);
                    v___y_116_ = v___x_125_;
                    state = 1;
                    continue;
                } else {
                    v___y_116_ = v___x_124_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_116_ == 0 {
                    crate::leanh::lean_inc(v_declName_114_);
                    crate::leanh::lean_inc_ref(v_env_113_);
                    v___x_117_ = l_Lean_isNoConfusion(v_env_113_, v_declName_114_);
                    if v___x_117_ == 0 {
                        crate::leanh::lean_inc(v_declName_114_);
                        crate::leanh::lean_inc_ref(v_env_113_);
                        v___x_118_ = l_Lean_isRecCore(v_env_113_, v_declName_114_);
                        if v___x_118_ == 0 {
                            v___x_119_ = l_Lean_Meta_completionBlackListExt;
                            v_toEnvExtension_120_ = crate::leanh::lean_ctor_get(v___x_119_, 0);
                            v_asyncMode_121_ =
                                crate::leanh::lean_ctor_get(v_toEnvExtension_120_, 2);
                            crate::leanh::lean_inc(v_declName_114_);
                            crate::leanh::lean_inc_ref(v_env_113_);
                            v___x_122_ = l_Lean_TagDeclarationExtension_isTagged(
                                v___x_119_,
                                v_env_113_,
                                v_declName_114_,
                                v_asyncMode_121_,
                            );
                            if v___x_122_ == 0 {
                                v___x_123_ = lean_is_matcher(v_env_113_, v_declName_114_);
                                return v___x_123_;
                            } else {
                                crate::leanh::lean_dec(v_declName_114_);
                                crate::leanh::lean_dec_ref(v_env_113_);
                                return v___x_122_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_114_);
                            crate::leanh::lean_dec_ref(v_env_113_);
                            return v___x_118_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_114_);
                        crate::leanh::lean_dec_ref(v_env_113_);
                        return v___x_117_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_114_);
                    crate::leanh::lean_dec_ref(v_env_113_);
                    return v___y_116_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(
    mut v_env_126_: *mut crate::leanh::LeanObject,
    mut v_declName_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: u8 = 0;
    let mut v_r_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(
        v_env_126_,
        v_declName_127_,
    );
    v_r_129_ = crate::leanh::lean_box((v_res_128_) as usize);
    return v_r_129_;
}
pub unsafe fn l_Lean_Meta_allowCompletion(
    mut v_env_130_: *mut crate::leanh::LeanObject,
    mut v_declName_131_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_132_: u8 = 0;
    v___x_132_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(
        v_env_130_,
        v_declName_131_,
    );
    if v___x_132_ == 0 {
        let mut v___x_133_: u8 = 0;
        v___x_133_ = 1;
        return v___x_133_;
    } else {
        let mut v___x_134_: u8 = 0;
        v___x_134_ = 0;
        return v___x_134_;
    }
}
pub unsafe fn l_Lean_Meta_allowCompletion___boxed(
    mut v_env_135_: *mut crate::leanh::LeanObject,
    mut v_declName_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_137_: u8 = 0;
    let mut v_r_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l_Lean_Meta_allowCompletion(v_env_135_, v_declName_136_);
    v_r_138_ = crate::leanh::lean_box((v_res_137_) as usize);
    return v_r_138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CompletionName(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_completionBlackListExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CompletionName(
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
pub unsafe fn initialize_Lean_Meta_CompletionName(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CompletionName(builtin);
}
