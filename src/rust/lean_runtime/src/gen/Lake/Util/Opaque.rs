// Lean compiler output
// Module: Lake.Util.Opaque
// Imports: Init.Prelude Init.Tactics
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static mut l___private_Lake_Util_Opaque_0__Lake_POpaque_nonemptyType: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lake_Util_Opaque_0__Lake_POpaque_nonemptyType() -> *mut LeanObject {
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    v___x_42_ = lean_box(0);
    return v___x_42_;
}
pub unsafe fn l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1___redArg(
    mut v_a_43_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_43_);
    return v_a_43_;
}
pub unsafe fn l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1___redArg___boxed(
    mut v_a_44_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_45_: *mut LeanObject = core::ptr::null_mut();
    v_res_45_ = l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1___redArg(v_a_44_);
    lean_dec(v_a_44_);
    return v_res_45_;
}
pub unsafe fn l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1(
    mut v_00_u03b1_46_: *mut LeanObject,
    mut v_a_47_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_47_);
    return v_a_47_;
}
pub unsafe fn l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1___boxed(
    mut v_00_u03b1_48_: *mut LeanObject,
    mut v_a_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l___private_Lake_Util_Opaque_0__Lake_POpaque_mk_unsafe__1(v_00_u03b1_48_, v_a_49_);
    lean_dec(v_a_49_);
    return v_res_50_;
}
pub unsafe fn l_Lake_POpaque_mk___redArg(mut v_a_51_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_51_);
    return v_a_51_;
}
pub unsafe fn l_Lake_POpaque_mk___redArg___boxed(mut v_a_52_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_53_: *mut LeanObject = core::ptr::null_mut();
    v_res_53_ = l_Lake_POpaque_mk___redArg(v_a_52_);
    lean_dec(v_a_52_);
    return v_res_53_;
}
pub unsafe fn l_Lake_POpaque_mk(
    mut v_00_u03b1_54_: *mut LeanObject,
    mut v_a_55_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_55_);
    return v_a_55_;
}
pub unsafe fn l_Lake_POpaque_mk___boxed(
    mut v_00_u03b1_56_: *mut LeanObject,
    mut v_a_57_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_58_: *mut LeanObject = core::ptr::null_mut();
    v_res_58_ = l_Lake_POpaque_mk(v_00_u03b1_56_, v_a_57_);
    lean_dec(v_a_57_);
    return v_res_58_;
}
pub unsafe fn l_Opaque_mk___redArg(mut v_a_59_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_59_);
    return v_a_59_;
}
pub unsafe fn l_Opaque_mk___redArg___boxed(mut v_a_60_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_61_: *mut LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Opaque_mk___redArg(v_a_60_);
    lean_dec(v_a_60_);
    return v_res_61_;
}
pub unsafe fn l_Opaque_mk(
    mut v_00_u03b1_62_: *mut LeanObject,
    mut v_a_63_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_63_);
    return v_a_63_;
}
pub unsafe fn l_Opaque_mk___boxed(
    mut v_00_u03b1_64_: *mut LeanObject,
    mut v_a_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Opaque_mk(v_00_u03b1_64_, v_a_65_);
    lean_dec(v_a_65_);
    return v_res_66_;
}
pub unsafe fn l_Lake_POpaque_cast___redArg(mut v_self_67_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_self_67_);
    return v_self_67_;
}
pub unsafe fn l_Lake_POpaque_cast___redArg___boxed(
    mut v_self_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_69_: *mut LeanObject = core::ptr::null_mut();
    v_res_69_ = l_Lake_POpaque_cast___redArg(v_self_68_);
    lean_dec(v_self_68_);
    return v_res_69_;
}
pub unsafe fn l_Lake_POpaque_cast(
    mut v_00_u03b1_70_: *mut LeanObject,
    mut v_self_71_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_self_71_);
    return v_self_71_;
}
pub unsafe fn l_Lake_POpaque_cast___boxed(
    mut v_00_u03b1_72_: *mut LeanObject,
    mut v_self_73_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_74_: *mut LeanObject = core::ptr::null_mut();
    v_res_74_ = l_Lake_POpaque_cast(v_00_u03b1_72_, v_self_73_);
    lean_dec(v_self_73_);
    return v_res_74_;
}
pub unsafe fn l_Lake_POpaque_castTo___redArg(mut v_self_75_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_self_75_);
    return v_self_75_;
}
pub unsafe fn l_Lake_POpaque_castTo___redArg___boxed(
    mut v_self_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_77_: *mut LeanObject = core::ptr::null_mut();
    v_res_77_ = l_Lake_POpaque_castTo___redArg(v_self_76_);
    lean_dec(v_self_76_);
    return v_res_77_;
}
pub unsafe fn l_Lake_POpaque_castTo(
    mut v_00_u03b1_78_: *mut LeanObject,
    mut v_self_79_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_self_79_);
    return v_self_79_;
}
pub unsafe fn l_Lake_POpaque_castTo___boxed(
    mut v_00_u03b1_80_: *mut LeanObject,
    mut v_self_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_82_: *mut LeanObject = core::ptr::null_mut();
    v_res_82_ = l_Lake_POpaque_castTo(v_00_u03b1_80_, v_self_81_);
    lean_dec(v_self_81_);
    return v_res_82_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Opaque(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lake_Util_Opaque_0__Lake_POpaque_nonemptyType =
        _init_l___private_Lake_Util_Opaque_0__Lake_POpaque_nonemptyType();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Opaque(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Opaque(builtin);
}
