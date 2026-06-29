// Lean compiler output
// Module: Lake.Config.ConfigTarget
// Imports: Lake.Config.Package
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, l_Lake_Package_findTargetDecl_x3f,
    runtime_initialize_Lake_Config_Package,
};
use crate::ffi::lean_usize_of_nat;
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint64_of_nat,
};
static mut l_Lake_instHashableConfigTarget___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableConfigTarget___lam__0___closed__0: u64 = 0;
pub static l_Lake_instHashableConfigTarget___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instHashableConfigTarget___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instHashableConfigTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableConfigTarget___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instBEqConfigTarget___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instBEqConfigTarget___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instBEqConfigTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instBEqConfigTarget___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Package_configTargets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_configTargets___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_configTargets___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__9_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_configTargets___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_configTargets___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_configTargets___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_configTargets___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_configTargets___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_instHashableConfigTarget___lam__0___closed__0() -> u64 {
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: u64 = 0;
    v___x_112_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_113_ = lean_uint64_of_nat(v___x_112_);
    return v___x_113_;
}
pub unsafe fn l_Lake_instHashableConfigTarget___lam__0(
    mut v_x_114_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_name_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_115_ = crate::leanh::lean_ctor_get(v_x_114_, 1);
    if crate::leanh::lean_obj_tag(v_name_115_) == 0 {
        let mut v___x_116_: u64 = 0;
        v___x_116_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_instHashableConfigTarget___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Lake_instHashableConfigTarget___lam__0___closed__0_once),
            _init_l_Lake_instHashableConfigTarget___lam__0___closed__0,
        );
        return v___x_116_;
    } else {
        let mut v_hash_117_: u64 = 0;
        v_hash_117_ = crate::leanh::lean_ctor_get_uint64(
            v_name_115_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        return v_hash_117_;
    }
}
pub unsafe fn l_Lake_instHashableConfigTarget___lam__0___boxed(
    mut v_x_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_119_: u64 = 0;
    let mut v_r_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_119_ = l_Lake_instHashableConfigTarget___lam__0(v_x_118_);
    crate::leanh::lean_dec_ref(v_x_118_);
    v_r_120_ = crate::leanh::lean_box_uint64(v_res_119_);
    return v_r_120_;
}
pub unsafe fn l_Lake_instHashableConfigTarget(
    mut v_k_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_123_ = l_Lake_instHashableConfigTarget___closed__0;
    return v___f_123_;
}
pub unsafe fn l_Lake_instHashableConfigTarget___boxed(
    mut v_k_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_125_ = l_Lake_instHashableConfigTarget(v_k_124_);
    crate::leanh::lean_dec(v_k_124_);
    return v_res_125_;
}
pub unsafe fn l_Lake_instBEqConfigTarget___lam__0(
    mut v_x1_126_: *mut crate::leanh::LeanObject,
    mut v_x2_127_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: u8 = 0;
    v_name_128_ = crate::leanh::lean_ctor_get(v_x1_126_, 1);
    v_name_129_ = crate::leanh::lean_ctor_get(v_x2_127_, 1);
    v___x_130_ = lean_name_eq(v_name_128_, v_name_129_);
    return v___x_130_;
}
pub unsafe fn l_Lake_instBEqConfigTarget___lam__0___boxed(
    mut v_x1_131_: *mut crate::leanh::LeanObject,
    mut v_x2_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: u8 = 0;
    let mut v_r_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Lake_instBEqConfigTarget___lam__0(v_x1_131_, v_x2_132_);
    crate::leanh::lean_dec_ref(v_x2_132_);
    crate::leanh::lean_dec_ref(v_x1_131_);
    v_r_134_ = crate::leanh::lean_box((v_res_133_) as usize);
    return v_r_134_;
}
pub unsafe fn l_Lake_instBEqConfigTarget(
    mut v_k_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_137_ = l_Lake_instBEqConfigTarget___closed__0;
    return v___f_137_;
}
pub unsafe fn l_Lake_instBEqConfigTarget___boxed(
    mut v_k_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Lake_instBEqConfigTarget(v_k_138_);
    crate::leanh::lean_dec(v_k_138_);
    return v_res_139_;
}
pub unsafe fn l_Lake_PConfigDecl_mkConfigTarget(
    mut v_pkg_140_: *mut crate::leanh::LeanObject,
    mut v_self_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_142_ = crate::leanh::lean_ctor_get(v_self_141_, 1);
    v_config_143_ = crate::leanh::lean_ctor_get(v_self_141_, 3);
    crate::leanh::lean_inc(v_config_143_);
    crate::leanh::lean_inc(v_name_142_);
    v___x_144_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_144_, 0, v_pkg_140_);
    crate::leanh::lean_ctor_set(v___x_144_, 1, v_name_142_);
    crate::leanh::lean_ctor_set(v___x_144_, 2, v_config_143_);
    return v___x_144_;
}
pub unsafe fn l_Lake_PConfigDecl_mkConfigTarget___boxed(
    mut v_pkg_145_: *mut crate::leanh::LeanObject,
    mut v_self_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lake_PConfigDecl_mkConfigTarget(v_pkg_145_, v_self_146_);
    crate::leanh::lean_dec_ref(v_self_146_);
    return v_res_147_;
}
pub unsafe fn l_Lake_Package_configTargets___lam__0(
    mut v_kind_148_: *mut crate::leanh::LeanObject,
    mut v_self_149_: *mut crate::leanh::LeanObject,
    mut v_x1_150_: *mut crate::leanh::LeanObject,
    mut v_x2_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    v_name_152_ = crate::leanh::lean_ctor_get(v_x2_151_, 1);
    v_kind_153_ = crate::leanh::lean_ctor_get(v_x2_151_, 2);
    v_config_154_ = crate::leanh::lean_ctor_get(v_x2_151_, 3);
    v___x_155_ = lean_name_eq(v_kind_153_, v_kind_148_);
    if v___x_155_ == 0 {
        crate::leanh::lean_dec_ref(v_self_149_);
        return v_x1_150_;
    } else {
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_154_);
        crate::leanh::lean_inc(v_name_152_);
        v___x_156_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_156_, 0, v_self_149_);
        crate::leanh::lean_ctor_set(v___x_156_, 1, v_name_152_);
        crate::leanh::lean_ctor_set(v___x_156_, 2, v_config_154_);
        v___x_157_ = lean_array_push(v_x1_150_, v___x_156_);
        return v___x_157_;
    }
}
pub unsafe fn l_Lake_Package_configTargets___lam__0___boxed(
    mut v_kind_158_: *mut crate::leanh::LeanObject,
    mut v_self_159_: *mut crate::leanh::LeanObject,
    mut v_x1_160_: *mut crate::leanh::LeanObject,
    mut v_x2_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ =
        l_Lake_Package_configTargets___lam__0(v_kind_158_, v_self_159_, v_x1_160_, v_x2_161_);
    crate::leanh::lean_dec_ref(v_x2_161_);
    crate::leanh::lean_dec(v_kind_158_);
    return v_res_162_;
}
pub unsafe fn l_Lake_Package_configTargets(
    mut v_kind_184_: *mut crate::leanh::LeanObject,
    mut v_self_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_targetDecls_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    v_targetDecls_186_ = crate::leanh::lean_ctor_get(v_self_185_, 14);
    crate::leanh::lean_inc_ref(v_targetDecls_186_);
    v___x_187_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_188_ = l_Lake_Package_configTargets___closed__0;
    v___x_189_ = lean_array_get_size(v_targetDecls_186_);
    v___x_190_ = l_Lake_Package_configTargets___closed__10;
    v___x_191_ = lean_nat_dec_lt(v___x_187_, v___x_189_);
    if v___x_191_ == 0 {
        crate::leanh::lean_dec_ref(v_targetDecls_186_);
        crate::leanh::lean_dec_ref(v_self_185_);
        crate::leanh::lean_dec(v_kind_184_);
        return v___x_188_;
    } else {
        let mut v___f_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: u8 = 0;
        v___f_192_ = crate::leanh::lean_alloc_closure(
            l_Lake_Package_configTargets___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_192_, 0, v_kind_184_);
        crate::leanh::lean_closure_set(v___f_192_, 1, v_self_185_);
        v___x_193_ = lean_nat_dec_le(v___x_189_, v___x_189_);
        if v___x_193_ == 0 {
            if v___x_191_ == 0 {
                crate::leanh::lean_dec_ref(v___f_192_);
                crate::leanh::lean_dec_ref(v_targetDecls_186_);
                return v___x_188_;
            } else {
                let mut v___x_194_: usize = 0;
                let mut v___x_195_: usize = 0;
                let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_194_ = 0usize;
                v___x_195_ = lean_usize_of_nat(v___x_189_);
                v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_190_,
                    v___f_192_,
                    v_targetDecls_186_,
                    v___x_194_,
                    v___x_195_,
                    v___x_188_,
                );
                return v___x_196_;
            }
        } else {
            let mut v___x_197_: usize = 0;
            let mut v___x_198_: usize = 0;
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_197_ = 0usize;
            v___x_198_ = lean_usize_of_nat(v___x_189_);
            v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_190_,
                v___f_192_,
                v_targetDecls_186_,
                v___x_197_,
                v___x_198_,
                v___x_188_,
            );
            return v___x_199_;
        }
    }
}
pub unsafe fn l_Lake_Package_findConfigTarget_x3f(
    mut v_kind_200_: *mut crate::leanh::LeanObject,
    mut v_name_201_: *mut crate::leanh::LeanObject,
    mut v_self_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_208_: u8 = 0;
    let mut v_name_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_203_ = l_Lake_Package_findTargetDecl_x3f(v_name_201_, v_self_202_);
                if crate::leanh::lean_obj_tag(v___x_203_) == 0 {
                    crate::leanh::lean_dec_ref(v_self_202_);
                    v___x_204_ = crate::leanh::lean_box(0);
                    return v___x_204_;
                } else {
                    v_val_205_ = crate::leanh::lean_ctor_get(v___x_203_, 0);
                    v_isSharedCheck_218_ = (!crate::leanh::lean_is_exclusive(v___x_203_)) as u8;
                    if v_isSharedCheck_218_ == 0 {
                        v___x_207_ = v___x_203_;
                        v_isShared_208_ = v_isSharedCheck_218_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_205_);
                        crate::leanh::lean_dec(v___x_203_);
                        v___x_207_ = crate::leanh::lean_box(0);
                        v_isShared_208_ = v_isSharedCheck_218_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_209_ = crate::leanh::lean_ctor_get(v_val_205_, 1);
                crate::leanh::lean_inc(v_name_209_);
                v_kind_210_ = crate::leanh::lean_ctor_get(v_val_205_, 2);
                crate::leanh::lean_inc(v_kind_210_);
                v_config_211_ = crate::leanh::lean_ctor_get(v_val_205_, 3);
                crate::leanh::lean_inc(v_config_211_);
                crate::leanh::lean_dec(v_val_205_);
                v___x_212_ = lean_name_eq(v_kind_210_, v_kind_200_);
                crate::leanh::lean_dec(v_kind_210_);
                if v___x_212_ == 0 {
                    crate::leanh::lean_dec(v_config_211_);
                    crate::leanh::lean_dec(v_name_209_);
                    crate::leanh::lean_del_object(v___x_207_);
                    crate::leanh::lean_dec_ref(v_self_202_);
                    v___x_213_ = crate::leanh::lean_box(0);
                    return v___x_213_;
                } else {
                    v___x_214_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_214_, 0, v_self_202_);
                    crate::leanh::lean_ctor_set(v___x_214_, 1, v_name_209_);
                    crate::leanh::lean_ctor_set(v___x_214_, 2, v_config_211_);
                    if v_isShared_208_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_207_, 0, v___x_214_);
                        v___x_216_ = v___x_207_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
                        v___x_216_ = v_reuseFailAlloc_217_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_findConfigTarget_x3f___boxed(
    mut v_kind_219_: *mut crate::leanh::LeanObject,
    mut v_name_220_: *mut crate::leanh::LeanObject,
    mut v_self_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lake_Package_findConfigTarget_x3f(v_kind_219_, v_name_220_, v_self_221_);
    crate::leanh::lean_dec(v_name_220_);
    crate::leanh::lean_dec(v_kind_219_);
    return v_res_222_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ConfigTarget(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ConfigTarget(
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
pub unsafe fn initialize_Lake_Config_ConfigTarget(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ConfigTarget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_ConfigTarget(builtin);
}
