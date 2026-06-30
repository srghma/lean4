// Lean compiler output
// Module: Lake.Config.ExternLib
// Imports: Lake.Config.ConfigTarget
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_of_nat,
};
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
pub static l_Lake_Package_externLibs___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Package_externLibs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__7_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_externLibs___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_externLibs___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__9_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_externLibs___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_externLibs___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_externLibs___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_externLibs___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_externLibs___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ExternLib_staticTargetName___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_ExternLib_staticTargetName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticTargetName___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Package_externLibs___lam__0(
    mut v___x_91_: *mut leanh::LeanObject,
    mut v_self_92_: *mut leanh::LeanObject,
    mut v_x1_93_: *mut leanh::LeanObject,
    mut v_x2_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: u8 = 0;
    v_name_95_ = leanh::lean_ctor_get(v_x2_94_, 1);
    v_kind_96_ = leanh::lean_ctor_get(v_x2_94_, 2);
    v_config_97_ = leanh::lean_ctor_get(v_x2_94_, 3);
    v___x_98_ = lean_name_eq(v_kind_96_, v___x_91_);
    if v___x_98_ == 0 {
        leanh::lean_dec_ref(v_self_92_);
        return v_x1_93_;
    } else {
        let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_config_97_);
        leanh::lean_inc(v_name_95_);
        v___x_99_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_99_, 0, v_self_92_);
        leanh::lean_ctor_set(v___x_99_, 1, v_name_95_);
        leanh::lean_ctor_set(v___x_99_, 2, v_config_97_);
        v___x_100_ = lean_array_push(v_x1_93_, v___x_99_);
        return v___x_100_;
    }
}
pub unsafe fn l_Lake_Package_externLibs___lam__0___boxed(
    mut v___x_101_: *mut leanh::LeanObject,
    mut v_self_102_: *mut leanh::LeanObject,
    mut v_x1_103_: *mut leanh::LeanObject,
    mut v_x2_104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Lake_Package_externLibs___lam__0(v___x_101_, v_self_102_, v_x1_103_, v_x2_104_);
    leanh::lean_dec_ref(v_x2_104_);
    leanh::lean_dec(v___x_101_);
    return v_res_105_;
}
pub unsafe fn l_Lake_Package_externLibs(
    mut v_self_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_targetDecls_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: u8 = 0;
    v_targetDecls_128_ = leanh::lean_ctor_get(v_self_127_, 14);
    leanh::lean_inc_ref(v_targetDecls_128_);
    v___x_129_ = leanh::lean_unsigned_to_nat(0);
    v___x_130_ = l_Lake_Package_externLibs___closed__0;
    v___x_131_ = lean_array_get_size(v_targetDecls_128_);
    v___x_132_ = l_Lake_Package_externLibs___closed__10;
    v___x_133_ = lean_nat_dec_lt(v___x_129_, v___x_131_);
    if v___x_133_ == 0 {
        leanh::lean_dec_ref(v_targetDecls_128_);
        leanh::lean_dec_ref(v_self_127_);
        return v___x_130_;
    } else {
        let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: u8 = 0;
        v___x_134_ = l_Lake_ExternLib_keyword;
        v___f_135_ = leanh::lean_alloc_closure(
            l_Lake_Package_externLibs___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_135_, 0, v___x_134_);
        leanh::lean_closure_set(v___f_135_, 1, v_self_127_);
        v___x_136_ = lean_nat_dec_le(v___x_131_, v___x_131_);
        if v___x_136_ == 0 {
            if v___x_133_ == 0 {
                leanh::lean_dec_ref(v___f_135_);
                leanh::lean_dec_ref(v_targetDecls_128_);
                return v___x_130_;
            } else {
                let mut v___x_137_: usize = 0;
                let mut v___x_138_: usize = 0;
                let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_137_ = 0usize;
                v___x_138_ = lean_usize_of_nat(v___x_131_);
                v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_140_ = 0usize;
            v___x_141_ = lean_usize_of_nat(v___x_131_);
            v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_name_143_: *mut leanh::LeanObject,
    mut v_self_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_150_: u8 = 0;
    let mut v_name_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_145_ = l_Lake_Package_findTargetDecl_x3f(v_name_143_, v_self_144_);
                if leanh::lean_obj_tag(v___x_145_) == 0 {
                    leanh::lean_dec_ref(v_self_144_);
                    v___x_146_ = leanh::lean_box(0);
                    return v___x_146_;
                } else {
                    v_val_147_ = leanh::lean_ctor_get(v___x_145_, 0);
                    v_isSharedCheck_161_ = (!leanh::lean_is_exclusive(v___x_145_)) as u8;
                    if v_isSharedCheck_161_ == 0 {
                        v___x_149_ = v___x_145_;
                        v_isShared_150_ = v_isSharedCheck_161_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_147_);
                        leanh::lean_dec(v___x_145_);
                        v___x_149_ = leanh::lean_box(0);
                        v_isShared_150_ = v_isSharedCheck_161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_151_ = leanh::lean_ctor_get(v_val_147_, 1);
                leanh::lean_inc(v_name_151_);
                v_kind_152_ = leanh::lean_ctor_get(v_val_147_, 2);
                leanh::lean_inc(v_kind_152_);
                v_config_153_ = leanh::lean_ctor_get(v_val_147_, 3);
                leanh::lean_inc(v_config_153_);
                leanh::lean_dec(v_val_147_);
                v___x_154_ = l_Lake_ExternLib_keyword;
                v___x_155_ = lean_name_eq(v_kind_152_, v___x_154_);
                leanh::lean_dec(v_kind_152_);
                if v___x_155_ == 0 {
                    leanh::lean_dec(v_config_153_);
                    leanh::lean_dec(v_name_151_);
                    leanh::lean_del_object(v___x_149_);
                    leanh::lean_dec_ref(v_self_144_);
                    v___x_156_ = leanh::lean_box(0);
                    return v___x_156_;
                } else {
                    v___x_157_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_157_, 0, v_self_144_);
                    leanh::lean_ctor_set(v___x_157_, 1, v_name_151_);
                    leanh::lean_ctor_set(v___x_157_, 2, v_config_153_);
                    if v_isShared_150_ == 0 {
                        leanh::lean_ctor_set(v___x_149_, 0, v___x_157_);
                        v___x_159_ = v___x_149_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
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
    mut v_name_162_: *mut leanh::LeanObject,
    mut v_self_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Lake_Package_findExternLib_x3f(v_name_162_, v_self_163_);
    leanh::lean_dec(v_name_162_);
    return v_res_164_;
}
pub unsafe fn l_Lake_ExternLib_config(
    mut v_self_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_166_ = leanh::lean_ctor_get(v_self_165_, 2);
    leanh::lean_inc(v_config_166_);
    return v_config_166_;
}
pub unsafe fn l_Lake_ExternLib_config___boxed(
    mut v_self_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Lake_ExternLib_config(v_self_167_);
    leanh::lean_dec_ref(v_self_167_);
    return v_res_168_;
}
pub unsafe fn l_Lake_ExternLib_linkArgs(
    mut v_self_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_170_ = leanh::lean_ctor_get(v_self_169_, 0);
    v_config_171_ = leanh::lean_ctor_get(v_pkg_170_, 6);
    v_toLeanConfig_172_ = leanh::lean_ctor_get(v_config_171_, 1);
    v_moreLinkArgs_173_ = leanh::lean_ctor_get(v_toLeanConfig_172_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_173_);
    return v_moreLinkArgs_173_;
}
pub unsafe fn l_Lake_ExternLib_linkArgs___boxed(
    mut v_self_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Lake_ExternLib_linkArgs(v_self_174_);
    leanh::lean_dec_ref(v_self_174_);
    return v_res_175_;
}
pub unsafe fn l_Lake_ExternLib_staticTargetName(
    mut v_self_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_178_ = leanh::lean_ctor_get(v_self_177_, 1);
    leanh::lean_inc(v_name_178_);
    leanh::lean_dec_ref(v_self_177_);
    v___x_179_ = l_Lake_ExternLib_staticTargetName___closed__0;
    v___x_180_ = l_Lean_Name_str___override(v_name_178_, v___x_179_);
    return v___x_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ExternLib(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ExternLib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ExternLib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_ConfigTarget(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_ExternLib(builtin);
}