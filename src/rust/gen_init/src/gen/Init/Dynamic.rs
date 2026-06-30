// Lean compiler output
// Module: Init.Dynamic
// Imports: Init.Prelude Init.Core
use crate::ffi::lean_name_eq;
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub static mut l___private_Init_Dynamic_0__DynamicPointed: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_TypeNameData(
    mut v_00_u03b1_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = leanh::lean_box(0);
    return v___x_50_;
}
pub unsafe fn l_TypeName_mk___redArg(
    mut v_typeName_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_typeName_51_);
    return v_typeName_51_;
}
pub unsafe fn l_TypeName_mk___redArg___boxed(
    mut v_typeName_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_53_ = l_TypeName_mk___redArg(v_typeName_52_);
    leanh::lean_dec(v_typeName_52_);
    return v_res_53_;
}
pub unsafe fn l_TypeName_mk(
    mut v_00_u03b1_54_: *mut leanh::LeanObject,
    mut v_typeName_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_typeName_55_);
    return v_typeName_55_;
}
pub unsafe fn l_TypeName_mk___boxed(
    mut v_00_u03b1_56_: *mut leanh::LeanObject,
    mut v_typeName_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_58_ = l_TypeName_mk(v_00_u03b1_56_, v_typeName_57_);
    leanh::lean_dec(v_typeName_57_);
    return v_res_58_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg(
    mut v_inst_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_59_);
    return v_inst_59_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg___boxed(
    mut v_inst_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_61_ = l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg(v_inst_60_);
    leanh::lean_dec(v_inst_60_);
    return v_res_61_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl(
    mut v_00_u03b1_62_: *mut leanh::LeanObject,
    mut v_inst_63_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_63_);
    return v_inst_63_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___boxed(
    mut v_00_u03b1_64_: *mut leanh::LeanObject,
    mut v_inst_65_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l___private_Init_Dynamic_0__TypeName_typeNameImpl(v_00_u03b1_64_, v_inst_65_);
    leanh::lean_dec(v_inst_65_);
    return v_res_66_;
}
pub unsafe fn _init_l___private_Init_Dynamic_0__DynamicPointed() -> *mut leanh::LeanObject {
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_67_ = leanh::lean_box(0);
    return v___x_67_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_typeNameImpl(
    mut v_any_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_69_ = leanh::lean_ctor_get(v_any_68_, 0);
    leanh::lean_inc(v_fst_69_);
    return v_fst_69_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_typeNameImpl___boxed(
    mut v_any_70_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_71_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_any_70_);
    leanh::lean_dec(v_any_70_);
    return v_res_71_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
    mut v_any_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: u8 = 0;
    v_fst_74_ = leanh::lean_ctor_get(v_any_72_, 0);
    v_snd_75_ = leanh::lean_ctor_get(v_any_72_, 1);
    v___x_76_ = lean_name_eq(v_fst_74_, v_inst_73_);
    if v___x_76_ == 0 {
        let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_77_ = leanh::lean_box(0);
        return v___x_77_;
    } else {
        let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_snd_75_);
        v___x_78_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_78_, 0, v_snd_75_);
        return v___x_78_;
    }
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg___boxed(
    mut v_any_79_: *mut leanh::LeanObject,
    mut v_inst_80_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_81_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_any_79_, v_inst_80_);
    leanh::lean_dec(v_inst_80_);
    leanh::lean_dec(v_any_79_);
    return v_res_81_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl(
    mut v_00_u03b1_82_: *mut leanh::LeanObject,
    mut v_any_83_: *mut leanh::LeanObject,
    mut v_inst_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_85_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_any_83_, v_inst_84_);
    return v___x_85_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___boxed(
    mut v_00_u03b1_86_: *mut leanh::LeanObject,
    mut v_any_87_: *mut leanh::LeanObject,
    mut v_inst_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_89_ =
        l___private_Init_Dynamic_0__Dynamic_get_x3fImpl(v_00_u03b1_86_, v_any_87_, v_inst_88_);
    leanh::lean_dec(v_inst_88_);
    leanh::lean_dec(v_any_87_);
    return v_res_89_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_mkImpl___redArg(
    mut v_inst_90_: *mut leanh::LeanObject,
    mut v_obj_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_92_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_92_, 0, v_inst_90_);
    leanh::lean_ctor_set(v___x_92_, 1, v_obj_91_);
    return v___x_92_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_mkImpl(
    mut v_00_u03b1_93_: *mut leanh::LeanObject,
    mut v_inst_94_: *mut leanh::LeanObject,
    mut v_obj_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_96_, 0, v_inst_94_);
    leanh::lean_ctor_set(v___x_96_, 1, v_obj_95_);
    return v___x_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Dynamic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Init_Dynamic_0__DynamicPointed = _init_l___private_Init_Dynamic_0__DynamicPointed();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Dynamic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Dynamic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Dynamic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Dynamic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Dynamic(builtin);
}