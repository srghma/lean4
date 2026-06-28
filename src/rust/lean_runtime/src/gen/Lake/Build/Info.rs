// Lean compiler output
// Module: Lake.Build.Info
// Imports: Lake.Config.Package Lake.Build.Data
use crate::r#gen::Lake::Build::Data::{
    initialize_Lake_Build_Data, meta_initialize_Lake_Build_Data,
};
use crate::r#gen::Lake::Build::Key::l_Lake_BuildKey_toString;
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_apply_4, lean_box,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_instToStringBuildInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instToStringBuildInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringBuildInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringBuildInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToStringBuildInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringBuildInfo___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_BuildInfo_ctorIdx(mut v_x_75_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_75_) == 0 {
        let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
        v___x_76_ = lean_unsigned_to_nat(0);
        return v___x_76_;
    } else {
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        v___x_77_ = lean_unsigned_to_nat(1);
        return v___x_77_;
    }
}
pub unsafe fn l_Lake_BuildInfo_ctorIdx___boxed(mut v_x_78_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_79_: *mut LeanObject = core::ptr::null_mut();
    v_res_79_ = l_Lake_BuildInfo_ctorIdx(v_x_78_);
    lean_dec_ref(v_x_78_);
    return v_res_79_;
}
pub unsafe fn l_Lake_BuildInfo_ctorElim___redArg(
    mut v_t_80_: *mut LeanObject,
    mut v_k_81_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_80_) == 0 {
        let mut v_package_82_: *mut LeanObject = core::ptr::null_mut();
        let mut v_target_83_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        v_package_82_ = lean_ctor_get(v_t_80_, 0);
        lean_inc_ref(v_package_82_);
        v_target_83_ = lean_ctor_get(v_t_80_, 1);
        lean_inc(v_target_83_);
        lean_dec_ref_known(v_t_80_, 2);
        v___x_84_ = lean_apply_2(v_k_81_, v_package_82_, v_target_83_);
        return v___x_84_;
    } else {
        let mut v_target_85_: *mut LeanObject = core::ptr::null_mut();
        let mut v_kind_86_: *mut LeanObject = core::ptr::null_mut();
        let mut v_data_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v_facet_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        v_target_85_ = lean_ctor_get(v_t_80_, 0);
        lean_inc_ref(v_target_85_);
        v_kind_86_ = lean_ctor_get(v_t_80_, 1);
        lean_inc(v_kind_86_);
        v_data_87_ = lean_ctor_get(v_t_80_, 2);
        lean_inc(v_data_87_);
        v_facet_88_ = lean_ctor_get(v_t_80_, 3);
        lean_inc(v_facet_88_);
        lean_dec_ref_known(v_t_80_, 4);
        v___x_89_ = lean_apply_4(v_k_81_, v_target_85_, v_kind_86_, v_data_87_, v_facet_88_);
        return v___x_89_;
    }
}
pub unsafe fn l_Lake_BuildInfo_ctorElim(
    mut v_motive_90_: *mut LeanObject,
    mut v_ctorIdx_91_: *mut LeanObject,
    mut v_t_92_: *mut LeanObject,
    mut v_h_93_: *mut LeanObject,
    mut v_k_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    v___x_95_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_92_, v_k_94_);
    return v___x_95_;
}
pub unsafe fn l_Lake_BuildInfo_ctorElim___boxed(
    mut v_motive_96_: *mut LeanObject,
    mut v_ctorIdx_97_: *mut LeanObject,
    mut v_t_98_: *mut LeanObject,
    mut v_h_99_: *mut LeanObject,
    mut v_k_100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_101_: *mut LeanObject = core::ptr::null_mut();
    v_res_101_ = l_Lake_BuildInfo_ctorElim(v_motive_96_, v_ctorIdx_97_, v_t_98_, v_h_99_, v_k_100_);
    lean_dec(v_ctorIdx_97_);
    return v_res_101_;
}
pub unsafe fn l_Lake_BuildInfo_target_elim___redArg(
    mut v_t_102_: *mut LeanObject,
    mut v_target_103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    v___x_104_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_102_, v_target_103_);
    return v___x_104_;
}
pub unsafe fn l_Lake_BuildInfo_target_elim(
    mut v_motive_105_: *mut LeanObject,
    mut v_t_106_: *mut LeanObject,
    mut v_h_107_: *mut LeanObject,
    mut v_target_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    v___x_109_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_106_, v_target_108_);
    return v___x_109_;
}
pub unsafe fn l_Lake_BuildInfo_facet_elim___redArg(
    mut v_t_110_: *mut LeanObject,
    mut v_facet_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    v___x_112_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_110_, v_facet_111_);
    return v___x_112_;
}
pub unsafe fn l_Lake_BuildInfo_facet_elim(
    mut v_motive_113_: *mut LeanObject,
    mut v_t_114_: *mut LeanObject,
    mut v_h_115_: *mut LeanObject,
    mut v_facet_116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    v___x_117_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_114_, v_facet_116_);
    return v___x_117_;
}
pub unsafe fn l_Lake_Package_key(mut v_self_118_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_119_ = lean_ctor_get(v_self_118_, 2);
    lean_inc(v_keyName_119_);
    v___x_120_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_120_, 0, v_keyName_119_);
    return v___x_120_;
}
pub unsafe fn l_Lake_Package_key___boxed(mut v_self_121_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_122_: *mut LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Lake_Package_key(v_self_121_);
    lean_dec_ref(v_self_121_);
    return v_res_122_;
}
pub unsafe fn l_Lake_Package_targetKey(
    mut v_target_123_: *mut LeanObject,
    mut v_self_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_125_ = lean_ctor_get(v_self_124_, 2);
    lean_inc(v_keyName_125_);
    v___x_126_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_126_, 0, v_keyName_125_);
    lean_ctor_set(v___x_126_, 1, v_target_123_);
    return v___x_126_;
}
pub unsafe fn l_Lake_Package_targetKey___boxed(
    mut v_target_127_: *mut LeanObject,
    mut v_self_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_129_: *mut LeanObject = core::ptr::null_mut();
    v_res_129_ = l_Lake_Package_targetKey(v_target_127_, v_self_128_);
    lean_dec_ref(v_self_128_);
    return v_res_129_;
}
pub unsafe fn l_Lake_BuildInfo_key(mut v_x_130_: *mut LeanObject) -> *mut LeanObject {
    let mut v_package_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_135_: u8 = 0;
    let mut v_keyName_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_140_: u8 = 0;
    let mut v_target_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_130_) == 0 {
                    v_package_131_ = lean_ctor_get(v_x_130_, 0);
                    v_target_132_ = lean_ctor_get(v_x_130_, 1);
                    v_isSharedCheck_140_ = (!lean_is_exclusive(v_x_130_)) as u8;
                    if v_isSharedCheck_140_ == 0 {
                        v___x_134_ = v_x_130_;
                        v_isShared_135_ = v_isSharedCheck_140_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_target_132_);
                        lean_inc(v_package_131_);
                        lean_dec(v_x_130_);
                        v___x_134_ = lean_box(0);
                        v_isShared_135_ = v_isSharedCheck_140_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_target_141_ = lean_ctor_get(v_x_130_, 0);
                    lean_inc_ref(v_target_141_);
                    v_facet_142_ = lean_ctor_get(v_x_130_, 3);
                    lean_inc(v_facet_142_);
                    lean_dec_ref_known(v_x_130_, 4);
                    v___x_143_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v___x_143_, 0, v_target_141_);
                    lean_ctor_set(v___x_143_, 1, v_facet_142_);
                    return v___x_143_;
                }
            }
            1 => {
                v_keyName_136_ = lean_ctor_get(v_package_131_, 2);
                lean_inc(v_keyName_136_);
                lean_dec_ref(v_package_131_);
                if v_isShared_135_ == 0 {
                    lean_ctor_set_tag(v___x_134_, 3);
                    lean_ctor_set(v___x_134_, 0, v_keyName_136_);
                    v___x_138_ = v___x_134_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_139_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_139_, 0, v_keyName_136_);
                    lean_ctor_set(v_reuseFailAlloc_139_, 1, v_target_132_);
                    v___x_138_ = v_reuseFailAlloc_139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToStringBuildInfo___lam__0(
    mut v_x_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Lake_BuildInfo_key(v_x_144_);
    v___x_146_ = l_Lake_BuildKey_toString(v___x_145_);
    return v___x_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Info(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Info(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Info(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Info(builtin);
}
