// Lean compiler output
// Module: Init.Dynamic
// Imports: Init.Prelude Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::lean_imports_rs::Init::Prelude::lean_name_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static mut l___private_Init_Dynamic_0__DynamicPointed: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_TypeNameData(mut v_00_u03b1_49_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    v___x_50_ = lean_box(0);
    return v___x_50_;
}
pub unsafe fn l_TypeName_mk___redArg(mut v_typeName_51_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_typeName_51_);
    return v_typeName_51_;
}
pub unsafe fn l_TypeName_mk___redArg___boxed(
    mut v_typeName_52_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_53_: *mut LeanObject = core::ptr::null_mut();
    v_res_53_ = l_TypeName_mk___redArg(v_typeName_52_);
    lean_dec(v_typeName_52_);
    return v_res_53_;
}
pub unsafe fn l_TypeName_mk(
    mut v_00_u03b1_54_: *mut LeanObject,
    mut v_typeName_55_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_typeName_55_);
    return v_typeName_55_;
}
pub unsafe fn l_TypeName_mk___boxed(
    mut v_00_u03b1_56_: *mut LeanObject,
    mut v_typeName_57_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_58_: *mut LeanObject = core::ptr::null_mut();
    v_res_58_ = l_TypeName_mk(v_00_u03b1_56_, v_typeName_57_);
    lean_dec(v_typeName_57_);
    return v_res_58_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg(
    mut v_inst_59_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_59_);
    return v_inst_59_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg___boxed(
    mut v_inst_60_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_61_: *mut LeanObject = core::ptr::null_mut();
    v_res_61_ = l___private_Init_Dynamic_0__TypeName_typeNameImpl___redArg(v_inst_60_);
    lean_dec(v_inst_60_);
    return v_res_61_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl(
    mut v_00_u03b1_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_63_);
    return v_inst_63_;
}
pub unsafe fn l___private_Init_Dynamic_0__TypeName_typeNameImpl___boxed(
    mut v_00_u03b1_64_: *mut LeanObject,
    mut v_inst_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l___private_Init_Dynamic_0__TypeName_typeNameImpl(v_00_u03b1_64_, v_inst_65_);
    lean_dec(v_inst_65_);
    return v_res_66_;
}
pub unsafe fn _init_l___private_Init_Dynamic_0__DynamicPointed() -> *mut LeanObject {
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    v___x_67_ = lean_box(0);
    return v___x_67_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_typeNameImpl(
    mut v_any_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_69_: *mut LeanObject = core::ptr::null_mut();
    v_fst_69_ = lean_ctor_get(v_any_68_, 0);
    lean_inc(v_fst_69_);
    return v_fst_69_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_typeNameImpl___boxed(
    mut v_any_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_71_: *mut LeanObject = core::ptr::null_mut();
    v_res_71_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_any_70_);
    lean_dec(v_any_70_);
    return v_res_71_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
    mut v_any_72_: *mut LeanObject,
    mut v_inst_73_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_76_: u8 = 0;
    v_fst_74_ = lean_ctor_get(v_any_72_, 0);
    v_snd_75_ = lean_ctor_get(v_any_72_, 1);
    v___x_76_ = lean_name_eq(v_fst_74_, v_inst_73_);
    if v___x_76_ == 0 {
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        v___x_77_ = lean_box(0);
        return v___x_77_;
    } else {
        let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_snd_75_);
        v___x_78_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_78_, 0, v_snd_75_);
        return v___x_78_;
    }
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg___boxed(
    mut v_any_79_: *mut LeanObject,
    mut v_inst_80_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_81_: *mut LeanObject = core::ptr::null_mut();
    v_res_81_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_any_79_, v_inst_80_);
    lean_dec(v_inst_80_);
    lean_dec(v_any_79_);
    return v_res_81_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl(
    mut v_00_u03b1_82_: *mut LeanObject,
    mut v_any_83_: *mut LeanObject,
    mut v_inst_84_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    v___x_85_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_any_83_, v_inst_84_);
    return v___x_85_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___boxed(
    mut v_00_u03b1_86_: *mut LeanObject,
    mut v_any_87_: *mut LeanObject,
    mut v_inst_88_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_89_: *mut LeanObject = core::ptr::null_mut();
    v_res_89_ =
        l___private_Init_Dynamic_0__Dynamic_get_x3fImpl(v_00_u03b1_86_, v_any_87_, v_inst_88_);
    lean_dec(v_inst_88_);
    lean_dec(v_any_87_);
    return v_res_89_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_mkImpl___redArg(
    mut v_inst_90_: *mut LeanObject,
    mut v_obj_91_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
    v___x_92_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_92_, 0, v_inst_90_);
    lean_ctor_set(v___x_92_, 1, v_obj_91_);
    return v___x_92_;
}
pub unsafe fn l___private_Init_Dynamic_0__Dynamic_mkImpl(
    mut v_00_u03b1_93_: *mut LeanObject,
    mut v_inst_94_: *mut LeanObject,
    mut v_obj_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_96_, 0, v_inst_94_);
    lean_ctor_set(v___x_96_, 1, v_obj_95_);
    return v___x_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Dynamic(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Init_Dynamic_0__DynamicPointed = _init_l___private_Init_Dynamic_0__DynamicPointed();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Dynamic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Dynamic(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Dynamic(builtin);
}
