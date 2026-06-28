// Lean compiler output
// Module: Lake.Config.ExternLib
// Imports: Lake.Config.ConfigTarget
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Lake::Config::ConfigTarget::{
    initialize_Lake_Config_ConfigTarget, runtime_initialize_Lake_Config_ConfigTarget,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_ExternLib_keyword;
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_del_object,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_Package_externLibs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Package_externLibs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__1_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__2_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__3_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__4_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__5_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__6_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__7_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Package_externLibs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__7_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_externLibs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__8_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__9_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_externLibs___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__9_value) as *mut LeanObject;
pub static l_Lake_Package_externLibs___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_externLibs___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_externLibs___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__10_value) as *mut LeanObject;
pub static l_Lake_ExternLib_staticTargetName___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 116, 97, 116, 105, 99, 0],
    };
static mut l_Lake_ExternLib_staticTargetName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticTargetName___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_Package_externLibs___lam__0(
    mut v___x_91_: *mut LeanObject,
    mut v_self_92_: *mut LeanObject,
    mut v_x1_93_: *mut LeanObject,
    mut v_x2_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: u8 = 0;
    v_name_95_ = lean_ctor_get(v_x2_94_, 1);
    v_kind_96_ = lean_ctor_get(v_x2_94_, 2);
    v_config_97_ = lean_ctor_get(v_x2_94_, 3);
    v___x_98_ = lean_name_eq(v_kind_96_, v___x_91_);
    if v___x_98_ == 0 {
        lean_dec_ref(v_self_92_);
        return v_x1_93_;
    } else {
        let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_97_);
        lean_inc(v_name_95_);
        v___x_99_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_99_, 0, v_self_92_);
        lean_ctor_set(v___x_99_, 1, v_name_95_);
        lean_ctor_set(v___x_99_, 2, v_config_97_);
        v___x_100_ = lean_array_push(v_x1_93_, v___x_99_);
        return v___x_100_;
    }
}
pub unsafe fn l_Lake_Package_externLibs___lam__0___boxed(
    mut v___x_101_: *mut LeanObject,
    mut v_self_102_: *mut LeanObject,
    mut v_x1_103_: *mut LeanObject,
    mut v_x2_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_105_: *mut LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Lake_Package_externLibs___lam__0(v___x_101_, v_self_102_, v_x1_103_, v_x2_104_);
    lean_dec_ref(v_x2_104_);
    lean_dec(v___x_101_);
    return v_res_105_;
}
pub unsafe fn l_Lake_Package_externLibs(mut v_self_127_: *mut LeanObject) -> *mut LeanObject {
    let mut v_targetDecls_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: u8 = 0;
    v_targetDecls_128_ = lean_ctor_get(v_self_127_, 14);
    lean_inc_ref(v_targetDecls_128_);
    v___x_129_ = lean_unsigned_to_nat(0);
    v___x_130_ = l_Lake_Package_externLibs___closed__0;
    v___x_131_ = lean_array_get_size(v_targetDecls_128_);
    v___x_132_ = l_Lake_Package_externLibs___closed__10;
    v___x_133_ = lean_nat_dec_lt(v___x_129_, v___x_131_);
    if v___x_133_ == 0 {
        lean_dec_ref(v_targetDecls_128_);
        lean_dec_ref(v_self_127_);
        return v___x_130_;
    } else {
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_136_: u8 = 0;
        v___x_134_ = l_Lake_ExternLib_keyword;
        v___f_135_ = lean_alloc_closure(
            l_Lake_Package_externLibs___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_135_, 0, v___x_134_);
        lean_closure_set(v___f_135_, 1, v_self_127_);
        v___x_136_ = lean_nat_dec_le(v___x_131_, v___x_131_);
        if v___x_136_ == 0 {
            if v___x_133_ == 0 {
                lean_dec_ref(v___f_135_);
                lean_dec_ref(v_targetDecls_128_);
                return v___x_130_;
            } else {
                let mut v___x_137_: usize = 0;
                let mut v___x_138_: usize = 0;
                let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
                v___x_137_ = 0usize;
                v___x_138_ = lean_usize_of_nat(v___x_131_);
                v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_132_,
                    v___f_135_,
                    v_targetDecls_128_,
                    v___x_137_,
                    v___x_138_,
                    v___x_130_,
                );
                return v___x_139_;
            }
        } else {
            let mut v___x_140_: usize = 0;
            let mut v___x_141_: usize = 0;
            let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
            v___x_140_ = 0usize;
            v___x_141_ = lean_usize_of_nat(v___x_131_);
            v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_132_,
                v___f_135_,
                v_targetDecls_128_,
                v___x_140_,
                v___x_141_,
                v___x_130_,
            );
            return v___x_142_;
        }
    }
}
pub unsafe fn l_Lake_Package_findExternLib_x3f(
    mut v_name_143_: *mut LeanObject,
    mut v_self_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_150_: u8 = 0;
    let mut v_name_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_145_ = l_Lake_Package_findTargetDecl_x3f(v_name_143_, v_self_144_);
                if lean_obj_tag(v___x_145_) == 0 {
                    lean_dec_ref(v_self_144_);
                    v___x_146_ = lean_box(0);
                    return v___x_146_;
                } else {
                    v_val_147_ = lean_ctor_get(v___x_145_, 0);
                    v_isSharedCheck_161_ = (!lean_is_exclusive(v___x_145_)) as u8;
                    if v_isSharedCheck_161_ == 0 {
                        v___x_149_ = v___x_145_;
                        v_isShared_150_ = v_isSharedCheck_161_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_147_);
                        lean_dec(v___x_145_);
                        v___x_149_ = lean_box(0);
                        v_isShared_150_ = v_isSharedCheck_161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_151_ = lean_ctor_get(v_val_147_, 1);
                lean_inc(v_name_151_);
                v_kind_152_ = lean_ctor_get(v_val_147_, 2);
                lean_inc(v_kind_152_);
                v_config_153_ = lean_ctor_get(v_val_147_, 3);
                lean_inc(v_config_153_);
                lean_dec(v_val_147_);
                v___x_154_ = l_Lake_ExternLib_keyword;
                v___x_155_ = lean_name_eq(v_kind_152_, v___x_154_);
                lean_dec(v_kind_152_);
                if v___x_155_ == 0 {
                    lean_dec(v_config_153_);
                    lean_dec(v_name_151_);
                    lean_del_object(v___x_149_);
                    lean_dec_ref(v_self_144_);
                    v___x_156_ = lean_box(0);
                    return v___x_156_;
                } else {
                    v___x_157_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_157_, 0, v_self_144_);
                    lean_ctor_set(v___x_157_, 1, v_name_151_);
                    lean_ctor_set(v___x_157_, 2, v_config_153_);
                    if v_isShared_150_ == 0 {
                        lean_ctor_set(v___x_149_, 0, v___x_157_);
                        v___x_159_ = v___x_149_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
                        v___x_159_ = v_reuseFailAlloc_160_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_findExternLib_x3f___boxed(
    mut v_name_162_: *mut LeanObject,
    mut v_self_163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_164_: *mut LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Lake_Package_findExternLib_x3f(v_name_162_, v_self_163_);
    lean_dec(v_name_162_);
    return v_res_164_;
}
pub unsafe fn l_Lake_ExternLib_config(mut v_self_165_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_166_: *mut LeanObject = core::ptr::null_mut();
    v_config_166_ = lean_ctor_get(v_self_165_, 2);
    lean_inc(v_config_166_);
    return v_config_166_;
}
pub unsafe fn l_Lake_ExternLib_config___boxed(mut v_self_167_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_168_: *mut LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Lake_ExternLib_config(v_self_167_);
    lean_dec_ref(v_self_167_);
    return v_res_168_;
}
pub unsafe fn l_Lake_ExternLib_linkArgs(mut v_self_169_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_173_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_170_ = lean_ctor_get(v_self_169_, 0);
    v_config_171_ = lean_ctor_get(v_pkg_170_, 6);
    v_toLeanConfig_172_ = lean_ctor_get(v_config_171_, 1);
    v_moreLinkArgs_173_ = lean_ctor_get(v_toLeanConfig_172_, 8);
    lean_inc_ref(v_moreLinkArgs_173_);
    return v_moreLinkArgs_173_;
}
pub unsafe fn l_Lake_ExternLib_linkArgs___boxed(
    mut v_self_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Lake_ExternLib_linkArgs(v_self_174_);
    lean_dec_ref(v_self_174_);
    return v_res_175_;
}
pub unsafe fn l_Lake_ExternLib_staticTargetName(
    mut v_self_177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    v_name_178_ = lean_ctor_get(v_self_177_, 1);
    lean_inc(v_name_178_);
    lean_dec_ref(v_self_177_);
    v___x_179_ = l_Lake_ExternLib_staticTargetName___closed__0;
    v___x_180_ = l_Lean_Name_str___override(v_name_178_, v___x_179_);
    return v___x_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ExternLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ExternLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ExternLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_ConfigTarget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_ExternLib(builtin);
}
