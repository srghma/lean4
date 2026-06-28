// Lean compiler output
// Module: Lake.Build.InitFacets
// Imports: Lake.Config.FacetConfig Lake.Build.Module Lake.Build.Package Lake.Build.Library Lake.Build.Executable Lake.Build.ExternLib Lake.Build.InputFile
use crate::r#gen::Lake::Build::Executable::{
    initialize_Lake_Build_Executable, l_Lake_LeanExe_initFacetConfigs,
    runtime_initialize_Lake_Build_Executable,
};
use crate::r#gen::Lake::Build::ExternLib::{
    initialize_Lake_Build_ExternLib, l_Lake_ExternLib_initFacetConfigs,
    runtime_initialize_Lake_Build_ExternLib,
};
use crate::r#gen::Lake::Build::InputFile::{
    initialize_Lake_Build_InputFile, l_Lake_InputDir_initFacetConfigs,
    l_Lake_InputFile_initFacetConfigs, runtime_initialize_Lake_Build_InputFile,
};
use crate::r#gen::Lake::Build::Library::{
    initialize_Lake_Build_Library, l_Lake_LeanLib_initFacetConfigs,
    runtime_initialize_Lake_Build_Library,
};
use crate::r#gen::Lake::Build::Module::{
    initialize_Lake_Build_Module, l_Lake_Module_initFacetConfigs,
    runtime_initialize_Lake_Build_Module,
};
use crate::r#gen::Lake::Build::Package::{
    initialize_Lake_Build_Package, l_Lake_Package_initFacetConfigs,
    runtime_initialize_Lake_Build_Package,
};
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, l_Lake_FacetConfigMap_insert,
    runtime_initialize_Lake_Config_FacetConfig,
};
static mut l_Lake_initFacetConfigs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_initFacetConfigs___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initFacetConfigs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_initFacetConfigs: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(
    mut v_init_46_: *mut crate::leanh::LeanObject,
    mut v_x_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_47_) == 0 {
                    v_k_48_ = crate::leanh::lean_ctor_get(v_x_47_, 1);
                    crate::leanh::lean_inc(v_k_48_);
                    v_v_49_ = crate::leanh::lean_ctor_get(v_x_47_, 2);
                    crate::leanh::lean_inc(v_v_49_);
                    v_l_50_ = crate::leanh::lean_ctor_get(v_x_47_, 3);
                    crate::leanh::lean_inc(v_l_50_);
                    v_r_51_ = crate::leanh::lean_ctor_get(v_x_47_, 4);
                    crate::leanh::lean_inc(v_r_51_);
                    crate::leanh::lean_dec_ref_known(v_x_47_, 5);
                    v___x_52_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_init_46_, v_l_50_);
                    v___x_53_ = l_Lake_FacetConfigMap_insert(v_k_48_, v_v_49_, v___x_52_);
                    v_init_46_ = v___x_53_;
                    v_x_47_ = v_r_51_;
                    state = 0;
                    continue;
                } else {
                    return v_init_46_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___redArg(
    mut v_group_55_: *mut crate::leanh::LeanObject,
    mut v_map_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_57_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_map_56_, v_group_55_);
    return v___x_57_;
}
pub unsafe fn l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(
    mut v_k_58_: *mut crate::leanh::LeanObject,
    mut v_group_59_: *mut crate::leanh::LeanObject,
    mut v_map_60_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_61_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_map_60_, v_group_59_);
    return v___x_61_;
}
pub unsafe fn l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___boxed(
    mut v_k_62_: *mut crate::leanh::LeanObject,
    mut v_group_63_: *mut crate::leanh::LeanObject,
    mut v_map_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_65_ = l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(
        v_k_62_,
        v_group_63_,
        v_map_64_,
    );
    crate::leanh::lean_dec(v_k_62_);
    return v_res_65_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0(
    mut v_init_66_: *mut crate::leanh::LeanObject,
    mut v_t_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_init_66_, v_t_67_);
    return v___x_68_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = l_Lake_Module_initFacetConfigs;
    v___x_70_ = crate::leanh::lean_box(1);
    v___x_71_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_70_, v___x_69_);
    return v___x_71_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_72_ = l_Lake_Package_initFacetConfigs;
    v___x_73_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__0_once),
        _init_l_Lake_initFacetConfigs___closed__0,
    );
    v___x_74_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_73_, v___x_72_);
    return v___x_74_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = l_Lake_LeanLib_initFacetConfigs;
    v___x_76_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__1_once),
        _init_l_Lake_initFacetConfigs___closed__1,
    );
    v___x_77_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_76_, v___x_75_);
    return v___x_77_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_78_ = l_Lake_LeanExe_initFacetConfigs;
    v___x_79_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__2),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__2_once),
        _init_l_Lake_initFacetConfigs___closed__2,
    );
    v___x_80_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_79_, v___x_78_);
    return v___x_80_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lake_ExternLib_initFacetConfigs;
    v___x_82_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__3),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__3_once),
        _init_l_Lake_initFacetConfigs___closed__3,
    );
    v___x_83_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_82_, v___x_81_);
    return v___x_83_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = l_Lake_InputFile_initFacetConfigs;
    v___x_85_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__4),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__4_once),
        _init_l_Lake_initFacetConfigs___closed__4,
    );
    v___x_86_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_85_, v___x_84_);
    return v___x_86_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_87_ = l_Lake_InputDir_initFacetConfigs;
    v___x_88_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__5),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__5_once),
        _init_l_Lake_initFacetConfigs___closed__5,
    );
    v___x_89_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_88_, v___x_87_);
    return v___x_89_;
}
pub unsafe fn _init_l_Lake_initFacetConfigs() -> *mut crate::leanh::LeanObject {
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_90_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__6),
        core::ptr::addr_of_mut!(l_Lake_initFacetConfigs___closed__6_once),
        _init_l_Lake_initFacetConfigs___closed__6,
    );
    return v___x_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_InitFacets(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Library(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Executable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_initFacetConfigs = _init_l_Lake_initFacetConfigs();
    crate::leanh::lean_mark_persistent(l_Lake_initFacetConfigs);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_InitFacets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_InitFacets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Library(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Executable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_InitFacets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_InitFacets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_InitFacets(builtin);
}
