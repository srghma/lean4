// Lean compiler output
// Module: Lake.Config.LeanLib
// Imports: Lake.Config.ConfigTarget Lake.Util.NativeLib Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_normalize,
};
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Lake::Config::ConfigTarget::{
    initialize_Lake_Config_ConfigTarget, runtime_initialize_Lake_Config_ConfigTarget,
};
use crate::r#gen::Lake::Config::LeanConfig::{
    l_Lake_Backend_orPreferLeft, l_Lake_BuildType_leanArgs, l_Lake_BuildType_leanOptions,
    l_Lake_BuildType_leancArgs, l_Lake_instOrdBuildType_ord,
};
use crate::r#gen::Lake::Config::LeanLibConfig::{
    l_Lake_LeanLibConfig_isBuildableModule___redArg, l_Lake_LeanLibConfig_isLocalModule___redArg,
};
use crate::r#gen::Lake::Config::Package::{
    l_Lake_Package_findTargetDecl_x3f, l_Lake_Package_id_x3f,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::NativeLib::{
    initialize_Lake_Util_NativeLib, l_Lake_nameToSharedLib, l_Lake_nameToStaticLib,
    runtime_initialize_Lake_Util_NativeLib,
};
use crate::r#gen::Lean::Compiler::NameMangling::l_Lean_mkModuleInitializationStem;
use crate::r#gen::Lean::Util::LeanOptions::{
    l_Lean_LeanOptions_append, l_Lean_LeanOptions_appendArray, l_Lean_LeanOptions_ofArray,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq,
    lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lake_Package_leanLibs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Package_leanLibs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__1_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__2_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__3_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__4_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__5_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__6_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__7_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Package_leanLibs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__7_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanLibs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__8_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__9_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanLibs___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__9_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanLibs___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__10_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__11_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0],
};
static mut l_Lake_Package_leanLibs___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__11_value) as *mut LeanObject;
pub static l_Lake_Package_leanLibs___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__11_value) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
static mut l_Lake_Package_leanLibs___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__12_value) as *mut LeanObject;
pub static l_Lake_LeanLib_libName___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 105, 98, 0],
};
static mut l_Lake_LeanLib_libName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_libName___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_staticExportLibFile___closed__0_value: LeanStringObject<7> =
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
        m_data: [101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_LeanLib_staticExportLibFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticExportLibFile___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_Package_leanLibs___lam__0(
    mut v___x_448_: *mut LeanObject,
    mut v_self_449_: *mut LeanObject,
    mut v_x1_450_: *mut LeanObject,
    mut v_x2_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    v_name_452_ = lean_ctor_get(v_x2_451_, 1);
    v_kind_453_ = lean_ctor_get(v_x2_451_, 2);
    v_config_454_ = lean_ctor_get(v_x2_451_, 3);
    v___x_455_ = lean_name_eq(v_kind_453_, v___x_448_);
    if v___x_455_ == 0 {
        lean_dec_ref(v_self_449_);
        return v_x1_450_;
    } else {
        let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_454_);
        lean_inc(v_name_452_);
        v___x_456_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_456_, 0, v_self_449_);
        lean_ctor_set(v___x_456_, 1, v_name_452_);
        lean_ctor_set(v___x_456_, 2, v_config_454_);
        v___x_457_ = lean_array_push(v_x1_450_, v___x_456_);
        return v___x_457_;
    }
}
pub unsafe fn l_Lake_Package_leanLibs___lam__0___boxed(
    mut v___x_458_: *mut LeanObject,
    mut v_self_459_: *mut LeanObject,
    mut v_x1_460_: *mut LeanObject,
    mut v_x2_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lake_Package_leanLibs___lam__0(v___x_458_, v_self_459_, v_x1_460_, v_x2_461_);
    lean_dec_ref(v_x2_461_);
    lean_dec(v___x_458_);
    return v_res_462_;
}
pub unsafe fn l_Lake_Package_leanLibs(mut v_self_487_: *mut LeanObject) -> *mut LeanObject {
    let mut v_targetDecls_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    v_targetDecls_488_ = lean_ctor_get(v_self_487_, 14);
    lean_inc_ref(v_targetDecls_488_);
    v___x_489_ = lean_unsigned_to_nat(0);
    v___x_490_ = l_Lake_Package_leanLibs___closed__0;
    v___x_491_ = lean_array_get_size(v_targetDecls_488_);
    v___x_492_ = l_Lake_Package_leanLibs___closed__10;
    v___x_493_ = lean_nat_dec_lt(v___x_489_, v___x_491_);
    if v___x_493_ == 0 {
        lean_dec_ref(v_targetDecls_488_);
        lean_dec_ref(v_self_487_);
        return v___x_490_;
    } else {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_496_: u8 = 0;
        v___x_494_ = l_Lake_Package_leanLibs___closed__12;
        v___f_495_ = lean_alloc_closure(
            l_Lake_Package_leanLibs___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_495_, 0, v___x_494_);
        lean_closure_set(v___f_495_, 1, v_self_487_);
        v___x_496_ = lean_nat_dec_le(v___x_491_, v___x_491_);
        if v___x_496_ == 0 {
            if v___x_493_ == 0 {
                lean_dec_ref(v___f_495_);
                lean_dec_ref(v_targetDecls_488_);
                return v___x_490_;
            } else {
                let mut v___x_497_: usize = 0;
                let mut v___x_498_: usize = 0;
                let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
                v___x_497_ = 0usize;
                v___x_498_ = lean_usize_of_nat(v___x_491_);
                v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_492_,
                    v___f_495_,
                    v_targetDecls_488_,
                    v___x_497_,
                    v___x_498_,
                    v___x_490_,
                );
                return v___x_499_;
            }
        } else {
            let mut v___x_500_: usize = 0;
            let mut v___x_501_: usize = 0;
            let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
            v___x_500_ = 0usize;
            v___x_501_ = lean_usize_of_nat(v___x_491_);
            v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_492_,
                v___f_495_,
                v_targetDecls_488_,
                v___x_500_,
                v___x_501_,
                v___x_490_,
            );
            return v___x_502_;
        }
    }
}
pub unsafe fn l_Lake_Package_findLeanLib_x3f(
    mut v_name_503_: *mut LeanObject,
    mut v_self_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_510_: u8 = 0;
    let mut v_name_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_505_ = l_Lake_Package_findTargetDecl_x3f(v_name_503_, v_self_504_);
                if lean_obj_tag(v___x_505_) == 0 {
                    lean_dec_ref(v_self_504_);
                    v___x_506_ = lean_box(0);
                    return v___x_506_;
                } else {
                    v_val_507_ = lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_521_ = (!lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_509_ = v___x_505_;
                        v_isShared_510_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_507_);
                        lean_dec(v___x_505_);
                        v___x_509_ = lean_box(0);
                        v_isShared_510_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_511_ = lean_ctor_get(v_val_507_, 1);
                lean_inc(v_name_511_);
                v_kind_512_ = lean_ctor_get(v_val_507_, 2);
                lean_inc(v_kind_512_);
                v_config_513_ = lean_ctor_get(v_val_507_, 3);
                lean_inc(v_config_513_);
                lean_dec(v_val_507_);
                v___x_514_ = l_Lake_Package_leanLibs___closed__12;
                v___x_515_ = lean_name_eq(v_kind_512_, v___x_514_);
                lean_dec(v_kind_512_);
                if v___x_515_ == 0 {
                    lean_dec(v_config_513_);
                    lean_dec(v_name_511_);
                    lean_del_object(v___x_509_);
                    lean_dec_ref(v_self_504_);
                    v___x_516_ = lean_box(0);
                    return v___x_516_;
                } else {
                    v___x_517_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_517_, 0, v_self_504_);
                    lean_ctor_set(v___x_517_, 1, v_name_511_);
                    lean_ctor_set(v___x_517_, 2, v_config_513_);
                    if v_isShared_510_ == 0 {
                        lean_ctor_set(v___x_509_, 0, v___x_517_);
                        v___x_519_ = v___x_509_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
                        v___x_519_ = v_reuseFailAlloc_520_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_findLeanLib_x3f___boxed(
    mut v_name_522_: *mut LeanObject,
    mut v_self_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lake_Package_findLeanLib_x3f(v_name_522_, v_self_523_);
    lean_dec(v_name_522_);
    return v_res_524_;
}
pub unsafe fn l_Lake_LeanLib_config(mut v_self_525_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_526_: *mut LeanObject = core::ptr::null_mut();
    v_config_526_ = lean_ctor_get(v_self_525_, 2);
    lean_inc(v_config_526_);
    return v_config_526_;
}
pub unsafe fn l_Lake_LeanLib_config___boxed(mut v_self_527_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Lake_LeanLib_config(v_self_527_);
    lean_dec_ref(v_self_527_);
    return v_res_528_;
}
pub unsafe fn l_Lake_LeanLib_srcDir(mut v_self_529_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_530_ = lean_ctor_get(v_self_529_, 0);
    lean_inc_ref(v_pkg_530_);
    v_config_531_ = lean_ctor_get(v_pkg_530_, 6);
    lean_inc_ref(v_config_531_);
    v_config_532_ = lean_ctor_get(v_self_529_, 2);
    lean_inc(v_config_532_);
    lean_dec_ref(v_self_529_);
    v_dir_533_ = lean_ctor_get(v_pkg_530_, 4);
    lean_inc_ref(v_dir_533_);
    lean_dec_ref(v_pkg_530_);
    v_srcDir_534_ = lean_ctor_get(v_config_531_, 4);
    lean_inc_ref(v_srcDir_534_);
    lean_dec_ref(v_config_531_);
    v_srcDir_535_ = lean_ctor_get(v_config_532_, 1);
    lean_inc_ref(v_srcDir_535_);
    lean_dec(v_config_532_);
    v___x_536_ = l_System_FilePath_normalize(v_srcDir_534_);
    v___x_537_ = l_Lake_joinRelative(v_dir_533_, v___x_536_);
    v___x_538_ = l_System_FilePath_normalize(v_srcDir_535_);
    v___x_539_ = l_Lake_joinRelative(v___x_537_, v___x_538_);
    return v___x_539_;
}
pub unsafe fn l_Lake_LeanLib_rootDir(mut v_self_540_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_541_ = lean_ctor_get(v_self_540_, 0);
    lean_inc_ref(v_pkg_541_);
    v_config_542_ = lean_ctor_get(v_pkg_541_, 6);
    lean_inc_ref(v_config_542_);
    v_config_543_ = lean_ctor_get(v_self_540_, 2);
    lean_inc(v_config_543_);
    lean_dec_ref(v_self_540_);
    v_dir_544_ = lean_ctor_get(v_pkg_541_, 4);
    lean_inc_ref(v_dir_544_);
    lean_dec_ref(v_pkg_541_);
    v_srcDir_545_ = lean_ctor_get(v_config_542_, 4);
    lean_inc_ref(v_srcDir_545_);
    lean_dec_ref(v_config_542_);
    v_srcDir_546_ = lean_ctor_get(v_config_543_, 1);
    lean_inc_ref(v_srcDir_546_);
    lean_dec(v_config_543_);
    v___x_547_ = l_System_FilePath_normalize(v_srcDir_545_);
    v___x_548_ = l_Lake_joinRelative(v_dir_544_, v___x_547_);
    v___x_549_ = l_System_FilePath_normalize(v_srcDir_546_);
    v___x_550_ = l_Lake_joinRelative(v___x_548_, v___x_549_);
    return v___x_550_;
}
pub unsafe fn l_Lake_LeanLib_roots(mut v_self_551_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_roots_553_: *mut LeanObject = core::ptr::null_mut();
    v_config_552_ = lean_ctor_get(v_self_551_, 2);
    v_roots_553_ = lean_ctor_get(v_config_552_, 2);
    lean_inc_ref(v_roots_553_);
    return v_roots_553_;
}
pub unsafe fn l_Lake_LeanLib_roots___boxed(mut v_self_554_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lake_LeanLib_roots(v_self_554_);
    lean_dec_ref(v_self_554_);
    return v_res_555_;
}
pub unsafe fn l_Lake_LeanLib_isLocalModule(
    mut v_mod_556_: *mut LeanObject,
    mut v_self_557_: *mut LeanObject,
) -> u8 {
    let mut v_config_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    v_config_558_ = lean_ctor_get(v_self_557_, 2);
    v___x_559_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_556_, v_config_558_);
    return v___x_559_;
}
pub unsafe fn l_Lake_LeanLib_isLocalModule___boxed(
    mut v_mod_560_: *mut LeanObject,
    mut v_self_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: u8 = 0;
    let mut v_r_563_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lake_LeanLib_isLocalModule(v_mod_560_, v_self_561_);
    lean_dec_ref(v_self_561_);
    lean_dec(v_mod_560_);
    v_r_563_ = lean_box((v_res_562_) as usize);
    return v_r_563_;
}
pub unsafe fn l_Lake_LeanLib_isBuildableModule(
    mut v_mod_564_: *mut LeanObject,
    mut v_self_565_: *mut LeanObject,
) -> u8 {
    let mut v_config_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    v_config_566_ = lean_ctor_get(v_self_565_, 2);
    v___x_567_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_564_, v_config_566_);
    return v___x_567_;
}
pub unsafe fn l_Lake_LeanLib_isBuildableModule___boxed(
    mut v_mod_568_: *mut LeanObject,
    mut v_self_569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut LeanObject = core::ptr::null_mut();
    v_res_570_ = l_Lake_LeanLib_isBuildableModule(v_mod_568_, v_self_569_);
    lean_dec_ref(v_self_569_);
    lean_dec(v_mod_568_);
    v_r_571_ = lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_Lake_LeanLib_libPrefixOnWindows(mut v_self_572_: *mut LeanObject) -> u8 {
    let mut v_config_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_574_: u8 = 0;
    v_config_573_ = lean_ctor_get(v_self_572_, 2);
    v_libPrefixOnWindows_574_ = lean_ctor_get_uint8(
        v_config_573_,
        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
    );
    if v_libPrefixOnWindows_574_ == 0 {
        let mut v_pkg_575_: *mut LeanObject = core::ptr::null_mut();
        let mut v_config_576_: *mut LeanObject = core::ptr::null_mut();
        let mut v_libPrefixOnWindows_577_: u8 = 0;
        v_pkg_575_ = lean_ctor_get(v_self_572_, 0);
        v_config_576_ = lean_ctor_get(v_pkg_575_, 6);
        v_libPrefixOnWindows_577_ = lean_ctor_get_uint8(
            v_config_576_,
            (core::mem::size_of::<*mut LeanObject>() * 27 + 4) as u32,
        );
        return v_libPrefixOnWindows_577_;
    } else {
        return v_libPrefixOnWindows_574_;
    }
}
pub unsafe fn l_Lake_LeanLib_libPrefixOnWindows___boxed(
    mut v_self_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_579_: u8 = 0;
    let mut v_r_580_: *mut LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_578_);
    lean_dec_ref(v_self_578_);
    v_r_580_ = lean_box((v_res_579_) as usize);
    return v_r_580_;
}
pub unsafe fn l_Lake_LeanLib_libName(mut v_self_582_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libName_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_592_: u8 = 0;
    let mut v___y_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_596_: u8 = 0;
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_588_ = lean_ctor_get(v_self_582_, 2);
                lean_inc(v_config_588_);
                v_pkg_589_ = lean_ctor_get(v_self_582_, 0);
                lean_inc_ref(v_pkg_589_);
                v_name_590_ = lean_ctor_get(v_self_582_, 1);
                lean_inc(v_name_590_);
                lean_dec_ref(v_self_582_);
                v_libName_591_ = lean_ctor_get(v_config_588_, 4);
                lean_inc_ref(v_libName_591_);
                v_libPrefixOnWindows_592_ = lean_ctor_get_uint8(
                    v_config_588_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                lean_dec(v_config_588_);
                v___x_597_ = lean_string_utf8_byte_size(v_libName_591_);
                v___x_598_ = lean_unsigned_to_nat(0);
                v___x_599_ = lean_nat_dec_eq(v___x_597_, v___x_598_);
                if v___x_599_ == 0 {
                    lean_dec(v_name_590_);
                    v___y_594_ = v_libName_591_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_libName_591_);
                    lean_inc_ref(v_pkg_589_);
                    v___x_600_ = l_Lake_Package_id_x3f(v_pkg_589_);
                    v___x_601_ = l_Lean_mkModuleInitializationStem(v_name_590_, v___x_600_);
                    lean_dec(v___x_600_);
                    v___y_594_ = v___x_601_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_585_ = l_System_Platform_isWindows;
                if v___x_585_ == 0 {
                    return v___y_584_;
                } else {
                    v___x_586_ = l_Lake_LeanLib_libName___closed__0;
                    v___x_587_ = lean_string_append(v___x_586_, v___y_584_);
                    lean_dec_ref(v___y_584_);
                    return v___x_587_;
                }
            }
            2 => {
                if v_libPrefixOnWindows_592_ == 0 {
                    v_config_595_ = lean_ctor_get(v_pkg_589_, 6);
                    lean_inc_ref(v_config_595_);
                    lean_dec_ref(v_pkg_589_);
                    v_libPrefixOnWindows_596_ = lean_ctor_get_uint8(
                        v_config_595_,
                        (core::mem::size_of::<*mut LeanObject>() * 27 + 4) as u32,
                    );
                    lean_dec_ref(v_config_595_);
                    if v_libPrefixOnWindows_596_ == 0 {
                        return v___y_594_;
                    } else {
                        v___y_584_ = v___y_594_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_589_);
                    v___y_584_ = v___y_594_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_staticLibFileName(
    mut v_self_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    v___x_603_ = l_Lake_LeanLib_libName(v_self_602_);
    v___x_604_ = 0;
    v___x_605_ = l_Lake_nameToStaticLib(v___x_603_, v___x_604_);
    return v___x_605_;
}
pub unsafe fn l_Lake_LeanLib_staticLibFile(mut v_self_606_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_607_ = lean_ctor_get(v_self_606_, 0);
    v_config_608_ = lean_ctor_get(v_pkg_607_, 6);
    v_dir_609_ = lean_ctor_get(v_pkg_607_, 4);
    v_buildDir_610_ = lean_ctor_get(v_config_608_, 5);
    v_nativeLibDir_611_ = lean_ctor_get(v_config_608_, 7);
    lean_inc_ref(v_buildDir_610_);
    v___x_612_ = l_System_FilePath_normalize(v_buildDir_610_);
    lean_inc_ref(v_dir_609_);
    v___x_613_ = l_Lake_joinRelative(v_dir_609_, v___x_612_);
    lean_inc_ref(v_nativeLibDir_611_);
    v___x_614_ = l_System_FilePath_normalize(v_nativeLibDir_611_);
    v___x_615_ = l_Lake_joinRelative(v___x_613_, v___x_614_);
    v___x_616_ = l_Lake_LeanLib_libName(v_self_606_);
    v___x_617_ = 0;
    v___x_618_ = l_Lake_nameToStaticLib(v___x_616_, v___x_617_);
    v___x_619_ = l_Lake_joinRelative(v___x_615_, v___x_618_);
    return v___x_619_;
}
pub unsafe fn l_Lake_LeanLib_staticExportLibFile(
    mut v_self_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_622_ = lean_ctor_get(v_self_621_, 0);
    v_config_623_ = lean_ctor_get(v_pkg_622_, 6);
    v_dir_624_ = lean_ctor_get(v_pkg_622_, 4);
    v_buildDir_625_ = lean_ctor_get(v_config_623_, 5);
    v_nativeLibDir_626_ = lean_ctor_get(v_config_623_, 7);
    lean_inc_ref(v_buildDir_625_);
    v___x_627_ = l_System_FilePath_normalize(v_buildDir_625_);
    lean_inc_ref(v_dir_624_);
    v___x_628_ = l_Lake_joinRelative(v_dir_624_, v___x_627_);
    lean_inc_ref(v_nativeLibDir_626_);
    v___x_629_ = l_System_FilePath_normalize(v_nativeLibDir_626_);
    v___x_630_ = l_Lake_joinRelative(v___x_628_, v___x_629_);
    v___x_631_ = l_Lake_LeanLib_libName(v_self_621_);
    v___x_632_ = 0;
    v___x_633_ = l_Lake_nameToStaticLib(v___x_631_, v___x_632_);
    v___x_634_ = l_Lake_LeanLib_staticExportLibFile___closed__0;
    v___x_635_ = l_System_FilePath_addExtension(v___x_633_, v___x_634_);
    v___x_636_ = l_Lake_joinRelative(v___x_630_, v___x_635_);
    return v___x_636_;
}
pub unsafe fn l_Lake_LeanLib_sharedLibFileName(
    mut v_self_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lake_LeanLib_libName(v_self_637_);
    v___x_639_ = 0;
    v___x_640_ = l_Lake_nameToSharedLib(v___x_638_, v___x_639_);
    lean_dec_ref(v___x_638_);
    return v___x_640_;
}
pub unsafe fn l_Lake_LeanLib_sharedLibFile(mut v_self_641_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_642_ = lean_ctor_get(v_self_641_, 0);
    v_config_643_ = lean_ctor_get(v_pkg_642_, 6);
    v_dir_644_ = lean_ctor_get(v_pkg_642_, 4);
    v_buildDir_645_ = lean_ctor_get(v_config_643_, 5);
    v_nativeLibDir_646_ = lean_ctor_get(v_config_643_, 7);
    lean_inc_ref(v_buildDir_645_);
    v___x_647_ = l_System_FilePath_normalize(v_buildDir_645_);
    lean_inc_ref(v_dir_644_);
    v___x_648_ = l_Lake_joinRelative(v_dir_644_, v___x_647_);
    lean_inc_ref(v_nativeLibDir_646_);
    v___x_649_ = l_System_FilePath_normalize(v_nativeLibDir_646_);
    v___x_650_ = l_Lake_joinRelative(v___x_648_, v___x_649_);
    v___x_651_ = l_Lake_LeanLib_libName(v_self_641_);
    v___x_652_ = 0;
    v___x_653_ = l_Lake_nameToSharedLib(v___x_651_, v___x_652_);
    lean_dec_ref(v___x_651_);
    v___x_654_ = l_Lake_joinRelative(v___x_650_, v___x_653_);
    return v___x_654_;
}
pub unsafe fn l_Lake_LeanLib_isPlugin(mut v_self_655_: *mut LeanObject) -> u8 {
    let mut v_config_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_roots_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u8 = 0;
    v_config_656_ = lean_ctor_get(v_self_655_, 2);
    v_pkg_657_ = lean_ctor_get(v_self_655_, 0);
    lean_inc_ref(v_pkg_657_);
    v_roots_658_ = lean_ctor_get(v_config_656_, 2);
    lean_inc_ref(v_roots_658_);
    v___x_659_ = lean_array_get_size(v_roots_658_);
    v___x_660_ = lean_unsigned_to_nat(1);
    v___x_661_ = lean_nat_dec_eq(v___x_659_, v___x_660_);
    if v___x_661_ == 0 {
        lean_dec_ref(v_roots_658_);
        lean_dec_ref(v_pkg_657_);
        lean_dec_ref(v_self_655_);
        return v___x_661_;
    } else {
        let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_667_: u8 = 0;
        v___x_662_ = l_Lake_LeanLib_libName(v_self_655_);
        v___x_663_ = lean_unsigned_to_nat(0);
        v___x_664_ = lean_array_fget(v_roots_658_, v___x_663_);
        lean_dec_ref(v_roots_658_);
        v___x_665_ = l_Lake_Package_id_x3f(v_pkg_657_);
        v___x_666_ = l_Lean_mkModuleInitializationStem(v___x_664_, v___x_665_);
        lean_dec(v___x_665_);
        v___x_667_ = lean_string_dec_eq(v___x_662_, v___x_666_);
        lean_dec_ref(v___x_666_);
        lean_dec_ref(v___x_662_);
        return v___x_667_;
    }
}
pub unsafe fn l_Lake_LeanLib_isPlugin___boxed(mut v_self_668_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_669_: u8 = 0;
    let mut v_r_670_: *mut LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lake_LeanLib_isPlugin(v_self_668_);
    v_r_670_ = lean_box((v_res_669_) as usize);
    return v_r_670_;
}
pub unsafe fn l_Lake_LeanLib_extraDepTargets(mut v_self_671_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_673_: *mut LeanObject = core::ptr::null_mut();
    v_config_672_ = lean_ctor_get(v_self_671_, 2);
    v_extraDepTargets_673_ = lean_ctor_get(v_config_672_, 6);
    lean_inc_ref(v_extraDepTargets_673_);
    return v_extraDepTargets_673_;
}
pub unsafe fn l_Lake_LeanLib_extraDepTargets___boxed(
    mut v_self_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_675_: *mut LeanObject = core::ptr::null_mut();
    v_res_675_ = l_Lake_LeanLib_extraDepTargets(v_self_674_);
    lean_dec_ref(v_self_674_);
    return v_res_675_;
}
pub unsafe fn l_Lake_LeanLib_precompileModules(mut v_self_676_: *mut LeanObject) -> u8 {
    let mut v_pkg_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_679_: u8 = 0;
    v_pkg_677_ = lean_ctor_get(v_self_676_, 0);
    v_config_678_ = lean_ctor_get(v_pkg_677_, 6);
    v_precompileModules_679_ = lean_ctor_get_uint8(
        v_config_678_,
        (core::mem::size_of::<*mut LeanObject>() * 27 + 1) as u32,
    );
    if v_precompileModules_679_ == 0 {
        let mut v_config_680_: *mut LeanObject = core::ptr::null_mut();
        let mut v_precompileModules_681_: u8 = 0;
        v_config_680_ = lean_ctor_get(v_self_676_, 2);
        v_precompileModules_681_ = lean_ctor_get_uint8(
            v_config_680_,
            (core::mem::size_of::<*mut LeanObject>() * 9 + 1) as u32,
        );
        return v_precompileModules_681_;
    } else {
        return v_precompileModules_679_;
    }
}
pub unsafe fn l_Lake_LeanLib_precompileModules___boxed(
    mut v_self_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_683_: u8 = 0;
    let mut v_r_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lake_LeanLib_precompileModules(v_self_682_);
    lean_dec_ref(v_self_682_);
    v_r_684_ = lean_box((v_res_683_) as usize);
    return v_r_684_;
}
pub unsafe fn l_Lake_LeanLib_platformIndependent(
    mut v_self_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_688_: *mut LeanObject = core::ptr::null_mut();
    v_config_686_ = lean_ctor_get(v_self_685_, 2);
    v_toLeanConfig_687_ = lean_ctor_get(v_config_686_, 0);
    v_platformIndependent_688_ = lean_ctor_get(v_toLeanConfig_687_, 10);
    if lean_obj_tag(v_platformIndependent_688_) == 0 {
        let mut v_pkg_689_: *mut LeanObject = core::ptr::null_mut();
        let mut v_config_690_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toLeanConfig_691_: *mut LeanObject = core::ptr::null_mut();
        let mut v_platformIndependent_692_: *mut LeanObject = core::ptr::null_mut();
        v_pkg_689_ = lean_ctor_get(v_self_685_, 0);
        v_config_690_ = lean_ctor_get(v_pkg_689_, 6);
        v_toLeanConfig_691_ = lean_ctor_get(v_config_690_, 1);
        v_platformIndependent_692_ = lean_ctor_get(v_toLeanConfig_691_, 10);
        lean_inc(v_platformIndependent_692_);
        return v_platformIndependent_692_;
    } else {
        lean_inc_ref(v_platformIndependent_688_);
        return v_platformIndependent_688_;
    }
}
pub unsafe fn l_Lake_LeanLib_platformIndependent___boxed(
    mut v_self_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lake_LeanLib_platformIndependent(v_self_693_);
    lean_dec_ref(v_self_693_);
    return v_res_694_;
}
pub unsafe fn l_Lake_LeanLib_defaultFacets(mut v_self_695_: *mut LeanObject) -> *mut LeanObject {
    let mut v_config_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultFacets_697_: *mut LeanObject = core::ptr::null_mut();
    v_config_696_ = lean_ctor_get(v_self_695_, 2);
    v_defaultFacets_697_ = lean_ctor_get(v_config_696_, 7);
    lean_inc_ref(v_defaultFacets_697_);
    return v_defaultFacets_697_;
}
pub unsafe fn l_Lake_LeanLib_defaultFacets___boxed(
    mut v_self_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_699_: *mut LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Lake_LeanLib_defaultFacets(v_self_698_);
    lean_dec_ref(v_self_698_);
    return v_res_699_;
}
pub unsafe fn l_Lake_LeanLib_nativeFacets(
    mut v_self_700_: *mut LeanObject,
    mut v_shouldExport_701_: u8,
) -> *mut LeanObject {
    let mut v_config_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v_config_702_ = lean_ctor_get(v_self_700_, 2);
    lean_inc(v_config_702_);
    lean_dec_ref(v_self_700_);
    v_nativeFacets_703_ = lean_ctor_get(v_config_702_, 8);
    lean_inc_ref(v_nativeFacets_703_);
    lean_dec(v_config_702_);
    v___x_704_ = lean_box((v_shouldExport_701_) as usize);
    v___x_705_ = lean_apply_1(v_nativeFacets_703_, v___x_704_);
    return v___x_705_;
}
pub unsafe fn l_Lake_LeanLib_nativeFacets___boxed(
    mut v_self_706_: *mut LeanObject,
    mut v_shouldExport_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_708_ = (lean_unbox(v_shouldExport_707_) as u8);
    v_res_709_ = l_Lake_LeanLib_nativeFacets(v_self_706_, v_shouldExport_boxed_708_);
    return v_res_709_;
}
pub unsafe fn l_Lake_LeanLib_buildType(mut v_self_710_: *mut LeanObject) -> u8 {
    let mut v_pkg_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_716_: u8 = 0;
    let mut v_buildType_717_: u8 = 0;
    let mut v___x_718_: u8 = 0;
    v_pkg_711_ = lean_ctor_get(v_self_710_, 0);
    v_config_712_ = lean_ctor_get(v_pkg_711_, 6);
    v_toLeanConfig_713_ = lean_ctor_get(v_config_712_, 1);
    v_config_714_ = lean_ctor_get(v_self_710_, 2);
    v_toLeanConfig_715_ = lean_ctor_get(v_config_714_, 0);
    v_buildType_716_ = lean_ctor_get_uint8(
        v_toLeanConfig_713_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
    );
    v_buildType_717_ = lean_ctor_get_uint8(
        v_toLeanConfig_715_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
    );
    v___x_718_ = l_Lake_instOrdBuildType_ord(v_buildType_716_, v_buildType_717_);
    if v___x_718_ == 2 {
        return v_buildType_717_;
    } else {
        return v_buildType_716_;
    }
}
pub unsafe fn l_Lake_LeanLib_buildType___boxed(
    mut v_self_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: u8 = 0;
    let mut v_r_721_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Lake_LeanLib_buildType(v_self_719_);
    lean_dec_ref(v_self_719_);
    v_r_721_ = lean_box((v_res_720_) as usize);
    return v_r_721_;
}
pub unsafe fn l_Lake_LeanLib_serverOptions(mut v_self_722_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_728_: u8 = 0;
    let mut v_leanOptions_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_731_: u8 = 0;
    let mut v_leanOptions_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_736_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_723_ = lean_ctor_get(v_self_722_, 0);
                v_config_724_ = lean_ctor_get(v_pkg_723_, 6);
                v_toLeanConfig_725_ = lean_ctor_get(v_config_724_, 1);
                v_config_726_ = lean_ctor_get(v_self_722_, 2);
                v_toLeanConfig_727_ = lean_ctor_get(v_config_726_, 0);
                v_buildType_728_ = lean_ctor_get_uint8(
                    v_toLeanConfig_725_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_729_ = lean_ctor_get(v_toLeanConfig_725_, 0);
                v_moreServerOptions_730_ = lean_ctor_get(v_toLeanConfig_725_, 4);
                v_buildType_731_ = lean_ctor_get_uint8(
                    v_toLeanConfig_727_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_732_ = lean_ctor_get(v_toLeanConfig_727_, 0);
                v_moreServerOptions_733_ = lean_ctor_get(v_toLeanConfig_727_, 4);
                v___x_734_ = lean_box(1);
                v___x_744_ = l_Lake_instOrdBuildType_ord(v_buildType_728_, v_buildType_731_);
                if v___x_744_ == 2 {
                    v___y_736_ = v_buildType_731_;
                    state = 1;
                    continue;
                } else {
                    v___y_736_ = v_buildType_728_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_737_ = l_Lake_BuildType_leanOptions(v___y_736_);
                v___x_738_ = l_Lean_LeanOptions_append(v___x_734_, v___x_737_);
                v___x_739_ = l_Lean_LeanOptions_ofArray(v_leanOptions_729_);
                v___x_740_ = l_Lean_LeanOptions_appendArray(v___x_739_, v_moreServerOptions_730_);
                v___x_741_ = l_Lean_LeanOptions_append(v___x_738_, v___x_740_);
                v___x_742_ = l_Lean_LeanOptions_appendArray(v___x_741_, v_leanOptions_732_);
                v___x_743_ = l_Lean_LeanOptions_appendArray(v___x_742_, v_moreServerOptions_733_);
                return v___x_743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_serverOptions___boxed(
    mut v_self_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lake_LeanLib_serverOptions(v_self_745_);
    lean_dec_ref(v_self_745_);
    return v_res_746_;
}
pub unsafe fn l_Lake_LeanLib_backend(mut v_self_747_: *mut LeanObject) -> u8 {
    let mut v_config_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_753_: u8 = 0;
    let mut v_backend_754_: u8 = 0;
    let mut v___x_755_: u8 = 0;
    v_config_748_ = lean_ctor_get(v_self_747_, 2);
    v_toLeanConfig_749_ = lean_ctor_get(v_config_748_, 0);
    v_pkg_750_ = lean_ctor_get(v_self_747_, 0);
    v_config_751_ = lean_ctor_get(v_pkg_750_, 6);
    v_toLeanConfig_752_ = lean_ctor_get(v_config_751_, 1);
    v_backend_753_ = lean_ctor_get_uint8(
        v_toLeanConfig_749_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
    );
    v_backend_754_ = lean_ctor_get_uint8(
        v_toLeanConfig_752_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
    );
    v___x_755_ = l_Lake_Backend_orPreferLeft(v_backend_753_, v_backend_754_);
    return v___x_755_;
}
pub unsafe fn l_Lake_LeanLib_backend___boxed(mut v_self_756_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_757_: u8 = 0;
    let mut v_r_758_: *mut LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lake_LeanLib_backend(v_self_756_);
    lean_dec_ref(v_self_756_);
    v_r_758_ = lean_box((v_res_757_) as usize);
    return v_r_758_;
}
pub unsafe fn l_Lake_LeanLib_allowImportAll(mut v_self_759_: *mut LeanObject) -> u8 {
    let mut v_config_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_761_: u8 = 0;
    v_config_760_ = lean_ctor_get(v_self_759_, 2);
    v_allowImportAll_761_ = lean_ctor_get_uint8(
        v_config_760_,
        (core::mem::size_of::<*mut LeanObject>() * 9 + 2) as u32,
    );
    if v_allowImportAll_761_ == 0 {
        let mut v_pkg_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v_config_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_allowImportAll_764_: u8 = 0;
        v_pkg_762_ = lean_ctor_get(v_self_759_, 0);
        v_config_763_ = lean_ctor_get(v_pkg_762_, 6);
        v_allowImportAll_764_ = lean_ctor_get_uint8(
            v_config_763_,
            (core::mem::size_of::<*mut LeanObject>() * 27 + 5) as u32,
        );
        return v_allowImportAll_764_;
    } else {
        return v_allowImportAll_761_;
    }
}
pub unsafe fn l_Lake_LeanLib_allowImportAll___boxed(
    mut v_self_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_766_: u8 = 0;
    let mut v_r_767_: *mut LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Lake_LeanLib_allowImportAll(v_self_765_);
    lean_dec_ref(v_self_765_);
    v_r_767_ = lean_box((v_res_766_) as usize);
    return v_r_767_;
}
pub unsafe fn l_Lake_LeanLib_dynlibs(mut v_self_768_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_769_ = lean_ctor_get(v_self_768_, 0);
    v_config_770_ = lean_ctor_get(v_pkg_769_, 6);
    v_toLeanConfig_771_ = lean_ctor_get(v_config_770_, 1);
    lean_inc_ref(v_toLeanConfig_771_);
    v_config_772_ = lean_ctor_get(v_self_768_, 2);
    lean_inc(v_config_772_);
    lean_dec_ref(v_self_768_);
    v_toLeanConfig_773_ = lean_ctor_get(v_config_772_, 0);
    lean_inc_ref(v_toLeanConfig_773_);
    lean_dec(v_config_772_);
    v_dynlibs_774_ = lean_ctor_get(v_toLeanConfig_771_, 11);
    lean_inc_ref(v_dynlibs_774_);
    lean_dec_ref(v_toLeanConfig_771_);
    v_dynlibs_775_ = lean_ctor_get(v_toLeanConfig_773_, 11);
    lean_inc_ref(v_dynlibs_775_);
    lean_dec_ref(v_toLeanConfig_773_);
    v___x_776_ = l_Array_append___redArg(v_dynlibs_774_, v_dynlibs_775_);
    lean_dec_ref(v_dynlibs_775_);
    return v___x_776_;
}
pub unsafe fn l_Lake_LeanLib_plugins(mut v_self_777_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_778_ = lean_ctor_get(v_self_777_, 0);
    v_config_779_ = lean_ctor_get(v_pkg_778_, 6);
    v_toLeanConfig_780_ = lean_ctor_get(v_config_779_, 1);
    lean_inc_ref(v_toLeanConfig_780_);
    v_config_781_ = lean_ctor_get(v_self_777_, 2);
    lean_inc(v_config_781_);
    lean_dec_ref(v_self_777_);
    v_toLeanConfig_782_ = lean_ctor_get(v_config_781_, 0);
    lean_inc_ref(v_toLeanConfig_782_);
    lean_dec(v_config_781_);
    v_plugins_783_ = lean_ctor_get(v_toLeanConfig_780_, 12);
    lean_inc_ref(v_plugins_783_);
    lean_dec_ref(v_toLeanConfig_780_);
    v_plugins_784_ = lean_ctor_get(v_toLeanConfig_782_, 12);
    lean_inc_ref(v_plugins_784_);
    lean_dec_ref(v_toLeanConfig_782_);
    v___x_785_ = l_Array_append___redArg(v_plugins_783_, v_plugins_784_);
    lean_dec_ref(v_plugins_784_);
    return v___x_785_;
}
pub unsafe fn l_Lake_LeanLib_leanOptions(mut v_self_786_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_792_: u8 = 0;
    let mut v_leanOptions_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_794_: u8 = 0;
    let mut v_leanOptions_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_797_: u8 = 0;
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_787_ = lean_ctor_get(v_self_786_, 0);
                v_config_788_ = lean_ctor_get(v_pkg_787_, 6);
                v_toLeanConfig_789_ = lean_ctor_get(v_config_788_, 1);
                v_config_790_ = lean_ctor_get(v_self_786_, 2);
                v_toLeanConfig_791_ = lean_ctor_get(v_config_790_, 0);
                v_buildType_792_ = lean_ctor_get_uint8(
                    v_toLeanConfig_789_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_793_ = lean_ctor_get(v_toLeanConfig_789_, 0);
                v_buildType_794_ = lean_ctor_get_uint8(
                    v_toLeanConfig_791_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_795_ = lean_ctor_get(v_toLeanConfig_791_, 0);
                v___x_802_ = l_Lake_instOrdBuildType_ord(v_buildType_792_, v_buildType_794_);
                if v___x_802_ == 2 {
                    v___y_797_ = v_buildType_794_;
                    state = 1;
                    continue;
                } else {
                    v___y_797_ = v_buildType_792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_798_ = l_Lake_BuildType_leanOptions(v___y_797_);
                v___x_799_ = l_Lean_LeanOptions_ofArray(v_leanOptions_793_);
                v___x_800_ = l_Lean_LeanOptions_append(v___x_798_, v___x_799_);
                v___x_801_ = l_Lean_LeanOptions_appendArray(v___x_800_, v_leanOptions_795_);
                return v___x_801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_leanOptions___boxed(
    mut v_self_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_LeanLib_leanOptions(v_self_803_);
    lean_dec_ref(v_self_803_);
    return v_res_804_;
}
pub unsafe fn l_Lake_LeanLib_leanArgs(mut v_self_805_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_811_: u8 = 0;
    let mut v_moreLeanArgs_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_813_: u8 = 0;
    let mut v_moreLeanArgs_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_816_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_806_ = lean_ctor_get(v_self_805_, 0);
                v_config_807_ = lean_ctor_get(v_pkg_806_, 6);
                v_toLeanConfig_808_ = lean_ctor_get(v_config_807_, 1);
                v_config_809_ = lean_ctor_get(v_self_805_, 2);
                v_toLeanConfig_810_ = lean_ctor_get(v_config_809_, 0);
                v_buildType_811_ = lean_ctor_get_uint8(
                    v_toLeanConfig_808_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_812_ = lean_ctor_get(v_toLeanConfig_808_, 1);
                v_buildType_813_ = lean_ctor_get_uint8(
                    v_toLeanConfig_810_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_814_ = lean_ctor_get(v_toLeanConfig_810_, 1);
                v___x_820_ = l_Lake_instOrdBuildType_ord(v_buildType_811_, v_buildType_813_);
                if v___x_820_ == 2 {
                    v___y_816_ = v_buildType_813_;
                    state = 1;
                    continue;
                } else {
                    v___y_816_ = v_buildType_811_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_817_ = l_Lake_BuildType_leanArgs(v___y_816_);
                v___x_818_ = l_Array_append___redArg(v___x_817_, v_moreLeanArgs_812_);
                v___x_819_ = l_Array_append___redArg(v___x_818_, v_moreLeanArgs_814_);
                return v___x_819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_leanArgs___boxed(mut v_self_821_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_822_: *mut LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lake_LeanLib_leanArgs(v_self_821_);
    lean_dec_ref(v_self_821_);
    return v_res_822_;
}
pub unsafe fn l_Lake_LeanLib_weakLeanArgs(mut v_self_823_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_824_ = lean_ctor_get(v_self_823_, 0);
    v_config_825_ = lean_ctor_get(v_pkg_824_, 6);
    v_toLeanConfig_826_ = lean_ctor_get(v_config_825_, 1);
    lean_inc_ref(v_toLeanConfig_826_);
    v_config_827_ = lean_ctor_get(v_self_823_, 2);
    lean_inc(v_config_827_);
    lean_dec_ref(v_self_823_);
    v_toLeanConfig_828_ = lean_ctor_get(v_config_827_, 0);
    lean_inc_ref(v_toLeanConfig_828_);
    lean_dec(v_config_827_);
    v_weakLeanArgs_829_ = lean_ctor_get(v_toLeanConfig_826_, 2);
    lean_inc_ref(v_weakLeanArgs_829_);
    lean_dec_ref(v_toLeanConfig_826_);
    v_weakLeanArgs_830_ = lean_ctor_get(v_toLeanConfig_828_, 2);
    lean_inc_ref(v_weakLeanArgs_830_);
    lean_dec_ref(v_toLeanConfig_828_);
    v___x_831_ = l_Array_append___redArg(v_weakLeanArgs_829_, v_weakLeanArgs_830_);
    lean_dec_ref(v_weakLeanArgs_830_);
    return v___x_831_;
}
pub unsafe fn l_Lake_LeanLib_leancArgs(mut v_self_832_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_838_: u8 = 0;
    let mut v_moreLeancArgs_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildType_840_: u8 = 0;
    let mut v_moreLeancArgs_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_843_: u8 = 0;
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_833_ = lean_ctor_get(v_self_832_, 0);
                v_config_834_ = lean_ctor_get(v_pkg_833_, 6);
                v_toLeanConfig_835_ = lean_ctor_get(v_config_834_, 1);
                v_config_836_ = lean_ctor_get(v_self_832_, 2);
                v_toLeanConfig_837_ = lean_ctor_get(v_config_836_, 0);
                v_buildType_838_ = lean_ctor_get_uint8(
                    v_toLeanConfig_835_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_839_ = lean_ctor_get(v_toLeanConfig_835_, 3);
                v_buildType_840_ = lean_ctor_get_uint8(
                    v_toLeanConfig_837_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_841_ = lean_ctor_get(v_toLeanConfig_837_, 3);
                v___x_847_ = l_Lake_instOrdBuildType_ord(v_buildType_838_, v_buildType_840_);
                if v___x_847_ == 2 {
                    v___y_843_ = v_buildType_840_;
                    state = 1;
                    continue;
                } else {
                    v___y_843_ = v_buildType_838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_844_ = l_Lake_BuildType_leancArgs(v___y_843_);
                v___x_845_ = l_Array_append___redArg(v___x_844_, v_moreLeancArgs_839_);
                v___x_846_ = l_Array_append___redArg(v___x_845_, v_moreLeancArgs_841_);
                return v___x_846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_leancArgs___boxed(
    mut v_self_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_849_: *mut LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Lake_LeanLib_leancArgs(v_self_848_);
    lean_dec_ref(v_self_848_);
    return v_res_849_;
}
pub unsafe fn l_Lake_LeanLib_weakLeancArgs(mut v_self_850_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_851_ = lean_ctor_get(v_self_850_, 0);
    v_config_852_ = lean_ctor_get(v_pkg_851_, 6);
    v_toLeanConfig_853_ = lean_ctor_get(v_config_852_, 1);
    lean_inc_ref(v_toLeanConfig_853_);
    v_config_854_ = lean_ctor_get(v_self_850_, 2);
    lean_inc(v_config_854_);
    lean_dec_ref(v_self_850_);
    v_toLeanConfig_855_ = lean_ctor_get(v_config_854_, 0);
    lean_inc_ref(v_toLeanConfig_855_);
    lean_dec(v_config_854_);
    v_weakLeancArgs_856_ = lean_ctor_get(v_toLeanConfig_853_, 5);
    lean_inc_ref(v_weakLeancArgs_856_);
    lean_dec_ref(v_toLeanConfig_853_);
    v_weakLeancArgs_857_ = lean_ctor_get(v_toLeanConfig_855_, 5);
    lean_inc_ref(v_weakLeancArgs_857_);
    lean_dec_ref(v_toLeanConfig_855_);
    v___x_858_ = l_Array_append___redArg(v_weakLeancArgs_856_, v_weakLeancArgs_857_);
    lean_dec_ref(v_weakLeancArgs_857_);
    return v___x_858_;
}
pub unsafe fn l_Lake_LeanLib_moreLinkObjs(mut v_self_859_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_860_ = lean_ctor_get(v_self_859_, 0);
    v_config_861_ = lean_ctor_get(v_pkg_860_, 6);
    v_toLeanConfig_862_ = lean_ctor_get(v_config_861_, 1);
    lean_inc_ref(v_toLeanConfig_862_);
    v_config_863_ = lean_ctor_get(v_self_859_, 2);
    lean_inc(v_config_863_);
    lean_dec_ref(v_self_859_);
    v_toLeanConfig_864_ = lean_ctor_get(v_config_863_, 0);
    lean_inc_ref(v_toLeanConfig_864_);
    lean_dec(v_config_863_);
    v_moreLinkObjs_865_ = lean_ctor_get(v_toLeanConfig_862_, 6);
    lean_inc_ref(v_moreLinkObjs_865_);
    lean_dec_ref(v_toLeanConfig_862_);
    v_moreLinkObjs_866_ = lean_ctor_get(v_toLeanConfig_864_, 6);
    lean_inc_ref(v_moreLinkObjs_866_);
    lean_dec_ref(v_toLeanConfig_864_);
    v___x_867_ = l_Array_append___redArg(v_moreLinkObjs_865_, v_moreLinkObjs_866_);
    lean_dec_ref(v_moreLinkObjs_866_);
    return v___x_867_;
}
pub unsafe fn l_Lake_LeanLib_moreLinkLibs(mut v_self_868_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_869_ = lean_ctor_get(v_self_868_, 0);
    v_config_870_ = lean_ctor_get(v_pkg_869_, 6);
    v_toLeanConfig_871_ = lean_ctor_get(v_config_870_, 1);
    lean_inc_ref(v_toLeanConfig_871_);
    v_config_872_ = lean_ctor_get(v_self_868_, 2);
    lean_inc(v_config_872_);
    lean_dec_ref(v_self_868_);
    v_toLeanConfig_873_ = lean_ctor_get(v_config_872_, 0);
    lean_inc_ref(v_toLeanConfig_873_);
    lean_dec(v_config_872_);
    v_moreLinkLibs_874_ = lean_ctor_get(v_toLeanConfig_871_, 7);
    lean_inc_ref(v_moreLinkLibs_874_);
    lean_dec_ref(v_toLeanConfig_871_);
    v_moreLinkLibs_875_ = lean_ctor_get(v_toLeanConfig_873_, 7);
    lean_inc_ref(v_moreLinkLibs_875_);
    lean_dec_ref(v_toLeanConfig_873_);
    v___x_876_ = l_Array_append___redArg(v_moreLinkLibs_874_, v_moreLinkLibs_875_);
    lean_dec_ref(v_moreLinkLibs_875_);
    return v___x_876_;
}
pub unsafe fn l_Lake_LeanLib_linkArgs(mut v_self_877_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_878_ = lean_ctor_get(v_self_877_, 0);
    v_config_879_ = lean_ctor_get(v_pkg_878_, 6);
    v_toLeanConfig_880_ = lean_ctor_get(v_config_879_, 1);
    lean_inc_ref(v_toLeanConfig_880_);
    v_config_881_ = lean_ctor_get(v_self_877_, 2);
    lean_inc(v_config_881_);
    lean_dec_ref(v_self_877_);
    v_toLeanConfig_882_ = lean_ctor_get(v_config_881_, 0);
    lean_inc_ref(v_toLeanConfig_882_);
    lean_dec(v_config_881_);
    v_moreLinkArgs_883_ = lean_ctor_get(v_toLeanConfig_880_, 8);
    lean_inc_ref(v_moreLinkArgs_883_);
    lean_dec_ref(v_toLeanConfig_880_);
    v_moreLinkArgs_884_ = lean_ctor_get(v_toLeanConfig_882_, 8);
    lean_inc_ref(v_moreLinkArgs_884_);
    lean_dec_ref(v_toLeanConfig_882_);
    v___x_885_ = l_Array_append___redArg(v_moreLinkArgs_883_, v_moreLinkArgs_884_);
    lean_dec_ref(v_moreLinkArgs_884_);
    return v___x_885_;
}
pub unsafe fn l_Lake_LeanLib_weakLinkArgs(mut v_self_886_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_887_ = lean_ctor_get(v_self_886_, 0);
    v_config_888_ = lean_ctor_get(v_pkg_887_, 6);
    v_toLeanConfig_889_ = lean_ctor_get(v_config_888_, 1);
    lean_inc_ref(v_toLeanConfig_889_);
    v_config_890_ = lean_ctor_get(v_self_886_, 2);
    lean_inc(v_config_890_);
    lean_dec_ref(v_self_886_);
    v_toLeanConfig_891_ = lean_ctor_get(v_config_890_, 0);
    lean_inc_ref(v_toLeanConfig_891_);
    lean_dec(v_config_890_);
    v_weakLinkArgs_892_ = lean_ctor_get(v_toLeanConfig_889_, 9);
    lean_inc_ref(v_weakLinkArgs_892_);
    lean_dec_ref(v_toLeanConfig_889_);
    v_weakLinkArgs_893_ = lean_ctor_get(v_toLeanConfig_891_, 9);
    lean_inc_ref(v_weakLinkArgs_893_);
    lean_dec_ref(v_toLeanConfig_891_);
    v___x_894_ = l_Array_append___redArg(v_weakLinkArgs_892_, v_weakLinkArgs_893_);
    lean_dec_ref(v_weakLinkArgs_893_);
    return v___x_894_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanLib(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanLib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanLib(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_LeanLib(builtin);
}
