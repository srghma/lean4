// Lean compiler output
// Module: Lake.Config.LeanLib
// Imports: Lake.Config.ConfigTarget Lake.Util.NativeLib Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_append, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
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
pub static l_Lake_Package_leanLibs___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__7_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Package_leanLibs___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_leanLibs___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__9_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_leanLibs___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_leanLibs___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__11_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Package_leanLibs___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_leanLibs___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__11_value)
                as *mut leanh::LeanObject,
            12295998048739818339 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_leanLibs___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_leanLibs___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_libName___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_LeanLib_libName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_libName___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_staticExportLibFile___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_LeanLib_staticExportLibFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticExportLibFile___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Package_leanLibs___lam__0(
    mut v___x_448_: *mut leanh::LeanObject,
    mut v_self_449_: *mut leanh::LeanObject,
    mut v_x1_450_: *mut leanh::LeanObject,
    mut v_x2_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    v_name_452_ = leanh::lean_ctor_get(v_x2_451_, 1);
    v_kind_453_ = leanh::lean_ctor_get(v_x2_451_, 2);
    v_config_454_ = leanh::lean_ctor_get(v_x2_451_, 3);
    v___x_455_ = lean_name_eq(v_kind_453_, v___x_448_);
    if v___x_455_ == 0 {
        leanh::lean_dec_ref(v_self_449_);
        return v_x1_450_;
    } else {
        let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_config_454_);
        leanh::lean_inc(v_name_452_);
        v___x_456_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_456_, 0, v_self_449_);
        leanh::lean_ctor_set(v___x_456_, 1, v_name_452_);
        leanh::lean_ctor_set(v___x_456_, 2, v_config_454_);
        v___x_457_ = lean_array_push(v_x1_450_, v___x_456_);
        return v___x_457_;
    }
}
pub unsafe fn l_Lake_Package_leanLibs___lam__0___boxed(
    mut v___x_458_: *mut leanh::LeanObject,
    mut v_self_459_: *mut leanh::LeanObject,
    mut v_x1_460_: *mut leanh::LeanObject,
    mut v_x2_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lake_Package_leanLibs___lam__0(v___x_458_, v_self_459_, v_x1_460_, v_x2_461_);
    leanh::lean_dec_ref(v_x2_461_);
    leanh::lean_dec(v___x_458_);
    return v_res_462_;
}
pub unsafe fn l_Lake_Package_leanLibs(
    mut v_self_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_targetDecls_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    v_targetDecls_488_ = leanh::lean_ctor_get(v_self_487_, 14);
    leanh::lean_inc_ref(v_targetDecls_488_);
    v___x_489_ = leanh::lean_unsigned_to_nat(0);
    v___x_490_ = l_Lake_Package_leanLibs___closed__0;
    v___x_491_ = lean_array_get_size(v_targetDecls_488_);
    v___x_492_ = l_Lake_Package_leanLibs___closed__10;
    v___x_493_ = lean_nat_dec_lt(v___x_489_, v___x_491_);
    if v___x_493_ == 0 {
        leanh::lean_dec_ref(v_targetDecls_488_);
        leanh::lean_dec_ref(v_self_487_);
        return v___x_490_;
    } else {
        let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_496_: u8 = 0;
        v___x_494_ = l_Lake_Package_leanLibs___closed__12;
        v___f_495_ = leanh::lean_alloc_closure(
            l_Lake_Package_leanLibs___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_495_, 0, v___x_494_);
        leanh::lean_closure_set(v___f_495_, 1, v_self_487_);
        v___x_496_ = lean_nat_dec_le(v___x_491_, v___x_491_);
        if v___x_496_ == 0 {
            if v___x_493_ == 0 {
                leanh::lean_dec_ref(v___f_495_);
                leanh::lean_dec_ref(v_targetDecls_488_);
                return v___x_490_;
            } else {
                let mut v___x_497_: usize = 0;
                let mut v___x_498_: usize = 0;
                let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_497_ = 0usize;
                v___x_498_ = lean_usize_of_nat(v___x_491_);
                v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_500_ = 0usize;
            v___x_501_ = lean_usize_of_nat(v___x_491_);
            v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_name_503_: *mut leanh::LeanObject,
    mut v_self_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_510_: u8 = 0;
    let mut v_name_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_505_ = l_Lake_Package_findTargetDecl_x3f(v_name_503_, v_self_504_);
                if leanh::lean_obj_tag(v___x_505_) == 0 {
                    leanh::lean_dec_ref(v_self_504_);
                    v___x_506_ = leanh::lean_box(0);
                    return v___x_506_;
                } else {
                    v_val_507_ = leanh::lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_521_ = (!leanh::lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_509_ = v___x_505_;
                        v_isShared_510_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_507_);
                        leanh::lean_dec(v___x_505_);
                        v___x_509_ = leanh::lean_box(0);
                        v_isShared_510_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_511_ = leanh::lean_ctor_get(v_val_507_, 1);
                leanh::lean_inc(v_name_511_);
                v_kind_512_ = leanh::lean_ctor_get(v_val_507_, 2);
                leanh::lean_inc(v_kind_512_);
                v_config_513_ = leanh::lean_ctor_get(v_val_507_, 3);
                leanh::lean_inc(v_config_513_);
                leanh::lean_dec(v_val_507_);
                v___x_514_ = l_Lake_Package_leanLibs___closed__12;
                v___x_515_ = lean_name_eq(v_kind_512_, v___x_514_);
                leanh::lean_dec(v_kind_512_);
                if v___x_515_ == 0 {
                    leanh::lean_dec(v_config_513_);
                    leanh::lean_dec(v_name_511_);
                    leanh::lean_del_object(v___x_509_);
                    leanh::lean_dec_ref(v_self_504_);
                    v___x_516_ = leanh::lean_box(0);
                    return v___x_516_;
                } else {
                    v___x_517_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_517_, 0, v_self_504_);
                    leanh::lean_ctor_set(v___x_517_, 1, v_name_511_);
                    leanh::lean_ctor_set(v___x_517_, 2, v_config_513_);
                    if v_isShared_510_ == 0 {
                        leanh::lean_ctor_set(v___x_509_, 0, v___x_517_);
                        v___x_519_ = v___x_509_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
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
    mut v_name_522_: *mut leanh::LeanObject,
    mut v_self_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lake_Package_findLeanLib_x3f(v_name_522_, v_self_523_);
    leanh::lean_dec(v_name_522_);
    return v_res_524_;
}
pub unsafe fn l_Lake_LeanLib_config(
    mut v_self_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_526_ = leanh::lean_ctor_get(v_self_525_, 2);
    leanh::lean_inc(v_config_526_);
    return v_config_526_;
}
pub unsafe fn l_Lake_LeanLib_config___boxed(
    mut v_self_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Lake_LeanLib_config(v_self_527_);
    leanh::lean_dec_ref(v_self_527_);
    return v_res_528_;
}
pub unsafe fn l_Lake_LeanLib_srcDir(
    mut v_self_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_530_ = leanh::lean_ctor_get(v_self_529_, 0);
    leanh::lean_inc_ref(v_pkg_530_);
    v_config_531_ = leanh::lean_ctor_get(v_pkg_530_, 6);
    leanh::lean_inc_ref(v_config_531_);
    v_config_532_ = leanh::lean_ctor_get(v_self_529_, 2);
    leanh::lean_inc(v_config_532_);
    leanh::lean_dec_ref(v_self_529_);
    v_dir_533_ = leanh::lean_ctor_get(v_pkg_530_, 4);
    leanh::lean_inc_ref(v_dir_533_);
    leanh::lean_dec_ref(v_pkg_530_);
    v_srcDir_534_ = leanh::lean_ctor_get(v_config_531_, 4);
    leanh::lean_inc_ref(v_srcDir_534_);
    leanh::lean_dec_ref(v_config_531_);
    v_srcDir_535_ = leanh::lean_ctor_get(v_config_532_, 1);
    leanh::lean_inc_ref(v_srcDir_535_);
    leanh::lean_dec(v_config_532_);
    v___x_536_ = l_System_FilePath_normalize(v_srcDir_534_);
    v___x_537_ = l_Lake_joinRelative(v_dir_533_, v___x_536_);
    v___x_538_ = l_System_FilePath_normalize(v_srcDir_535_);
    v___x_539_ = l_Lake_joinRelative(v___x_537_, v___x_538_);
    return v___x_539_;
}
pub unsafe fn l_Lake_LeanLib_rootDir(
    mut v_self_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_541_ = leanh::lean_ctor_get(v_self_540_, 0);
    leanh::lean_inc_ref(v_pkg_541_);
    v_config_542_ = leanh::lean_ctor_get(v_pkg_541_, 6);
    leanh::lean_inc_ref(v_config_542_);
    v_config_543_ = leanh::lean_ctor_get(v_self_540_, 2);
    leanh::lean_inc(v_config_543_);
    leanh::lean_dec_ref(v_self_540_);
    v_dir_544_ = leanh::lean_ctor_get(v_pkg_541_, 4);
    leanh::lean_inc_ref(v_dir_544_);
    leanh::lean_dec_ref(v_pkg_541_);
    v_srcDir_545_ = leanh::lean_ctor_get(v_config_542_, 4);
    leanh::lean_inc_ref(v_srcDir_545_);
    leanh::lean_dec_ref(v_config_542_);
    v_srcDir_546_ = leanh::lean_ctor_get(v_config_543_, 1);
    leanh::lean_inc_ref(v_srcDir_546_);
    leanh::lean_dec(v_config_543_);
    v___x_547_ = l_System_FilePath_normalize(v_srcDir_545_);
    v___x_548_ = l_Lake_joinRelative(v_dir_544_, v___x_547_);
    v___x_549_ = l_System_FilePath_normalize(v_srcDir_546_);
    v___x_550_ = l_Lake_joinRelative(v___x_548_, v___x_549_);
    return v___x_550_;
}
pub unsafe fn l_Lake_LeanLib_roots(
    mut v_self_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_552_ = leanh::lean_ctor_get(v_self_551_, 2);
    v_roots_553_ = leanh::lean_ctor_get(v_config_552_, 2);
    leanh::lean_inc_ref(v_roots_553_);
    return v_roots_553_;
}
pub unsafe fn l_Lake_LeanLib_roots___boxed(
    mut v_self_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lake_LeanLib_roots(v_self_554_);
    leanh::lean_dec_ref(v_self_554_);
    return v_res_555_;
}
pub unsafe fn l_Lake_LeanLib_isLocalModule(
    mut v_mod_556_: *mut leanh::LeanObject,
    mut v_self_557_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_config_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    v_config_558_ = leanh::lean_ctor_get(v_self_557_, 2);
    v___x_559_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_556_, v_config_558_);
    return v___x_559_;
}
pub unsafe fn l_Lake_LeanLib_isLocalModule___boxed(
    mut v_mod_560_: *mut leanh::LeanObject,
    mut v_self_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: u8 = 0;
    let mut v_r_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lake_LeanLib_isLocalModule(v_mod_560_, v_self_561_);
    leanh::lean_dec_ref(v_self_561_);
    leanh::lean_dec(v_mod_560_);
    v_r_563_ = leanh::lean_box((v_res_562_) as usize);
    return v_r_563_;
}
pub unsafe fn l_Lake_LeanLib_isBuildableModule(
    mut v_mod_564_: *mut leanh::LeanObject,
    mut v_self_565_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_config_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    v_config_566_ = leanh::lean_ctor_get(v_self_565_, 2);
    v___x_567_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_564_, v_config_566_);
    return v___x_567_;
}
pub unsafe fn l_Lake_LeanLib_isBuildableModule___boxed(
    mut v_mod_568_: *mut leanh::LeanObject,
    mut v_self_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ = l_Lake_LeanLib_isBuildableModule(v_mod_568_, v_self_569_);
    leanh::lean_dec_ref(v_self_569_);
    leanh::lean_dec(v_mod_568_);
    v_r_571_ = leanh::lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_Lake_LeanLib_libPrefixOnWindows(
    mut v_self_572_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_config_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_574_: u8 = 0;
    v_config_573_ = leanh::lean_ctor_get(v_self_572_, 2);
    v_libPrefixOnWindows_574_ = leanh::lean_ctor_get_uint8(
        v_config_573_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
    );
    if v_libPrefixOnWindows_574_ == 0 {
        let mut v_pkg_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_libPrefixOnWindows_577_: u8 = 0;
        v_pkg_575_ = leanh::lean_ctor_get(v_self_572_, 0);
        v_config_576_ = leanh::lean_ctor_get(v_pkg_575_, 6);
        v_libPrefixOnWindows_577_ = leanh::lean_ctor_get_uint8(
            v_config_576_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 4) as u32,
        );
        return v_libPrefixOnWindows_577_;
    } else {
        return v_libPrefixOnWindows_574_;
    }
}
pub unsafe fn l_Lake_LeanLib_libPrefixOnWindows___boxed(
    mut v_self_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_579_: u8 = 0;
    let mut v_r_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_578_);
    leanh::lean_dec_ref(v_self_578_);
    v_r_580_ = leanh::lean_box((v_res_579_) as usize);
    return v_r_580_;
}
pub unsafe fn l_Lake_LeanLib_libName(
    mut v_self_582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_592_: u8 = 0;
    let mut v___y_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_596_: u8 = 0;
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_588_ = leanh::lean_ctor_get(v_self_582_, 2);
                leanh::lean_inc(v_config_588_);
                v_pkg_589_ = leanh::lean_ctor_get(v_self_582_, 0);
                leanh::lean_inc_ref(v_pkg_589_);
                v_name_590_ = leanh::lean_ctor_get(v_self_582_, 1);
                leanh::lean_inc(v_name_590_);
                leanh::lean_dec_ref(v_self_582_);
                v_libName_591_ = leanh::lean_ctor_get(v_config_588_, 4);
                leanh::lean_inc_ref(v_libName_591_);
                v_libPrefixOnWindows_592_ = leanh::lean_ctor_get_uint8(
                    v_config_588_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                );
                leanh::lean_dec(v_config_588_);
                v___x_597_ = lean_string_utf8_byte_size(v_libName_591_);
                v___x_598_ = leanh::lean_unsigned_to_nat(0);
                v___x_599_ = lean_nat_dec_eq(v___x_597_, v___x_598_);
                if v___x_599_ == 0 {
                    leanh::lean_dec(v_name_590_);
                    v___y_594_ = v_libName_591_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_libName_591_);
                    leanh::lean_inc_ref(v_pkg_589_);
                    v___x_600_ = l_Lake_Package_id_x3f(v_pkg_589_);
                    v___x_601_ = l_Lean_mkModuleInitializationStem(v_name_590_, v___x_600_);
                    leanh::lean_dec(v___x_600_);
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
                    leanh::lean_dec_ref(v___y_584_);
                    return v___x_587_;
                }
            }
            2 => {
                if v_libPrefixOnWindows_592_ == 0 {
                    v_config_595_ = leanh::lean_ctor_get(v_pkg_589_, 6);
                    leanh::lean_inc_ref(v_config_595_);
                    leanh::lean_dec_ref(v_pkg_589_);
                    v_libPrefixOnWindows_596_ = leanh::lean_ctor_get_uint8(
                        v_config_595_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 4) as u32,
                    );
                    leanh::lean_dec_ref(v_config_595_);
                    if v_libPrefixOnWindows_596_ == 0 {
                        return v___y_594_;
                    } else {
                        v___y_584_ = v___y_594_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_pkg_589_);
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
    mut v_self_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = l_Lake_LeanLib_libName(v_self_602_);
    v___x_604_ = 0;
    v___x_605_ = l_Lake_nameToStaticLib(v___x_603_, v___x_604_);
    return v___x_605_;
}
pub unsafe fn l_Lake_LeanLib_staticLibFile(
    mut v_self_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_607_ = leanh::lean_ctor_get(v_self_606_, 0);
    v_config_608_ = leanh::lean_ctor_get(v_pkg_607_, 6);
    v_dir_609_ = leanh::lean_ctor_get(v_pkg_607_, 4);
    v_buildDir_610_ = leanh::lean_ctor_get(v_config_608_, 5);
    v_nativeLibDir_611_ = leanh::lean_ctor_get(v_config_608_, 7);
    leanh::lean_inc_ref(v_buildDir_610_);
    v___x_612_ = l_System_FilePath_normalize(v_buildDir_610_);
    leanh::lean_inc_ref(v_dir_609_);
    v___x_613_ = l_Lake_joinRelative(v_dir_609_, v___x_612_);
    leanh::lean_inc_ref(v_nativeLibDir_611_);
    v___x_614_ = l_System_FilePath_normalize(v_nativeLibDir_611_);
    v___x_615_ = l_Lake_joinRelative(v___x_613_, v___x_614_);
    v___x_616_ = l_Lake_LeanLib_libName(v_self_606_);
    v___x_617_ = 0;
    v___x_618_ = l_Lake_nameToStaticLib(v___x_616_, v___x_617_);
    v___x_619_ = l_Lake_joinRelative(v___x_615_, v___x_618_);
    return v___x_619_;
}
pub unsafe fn l_Lake_LeanLib_staticExportLibFile(
    mut v_self_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_622_ = leanh::lean_ctor_get(v_self_621_, 0);
    v_config_623_ = leanh::lean_ctor_get(v_pkg_622_, 6);
    v_dir_624_ = leanh::lean_ctor_get(v_pkg_622_, 4);
    v_buildDir_625_ = leanh::lean_ctor_get(v_config_623_, 5);
    v_nativeLibDir_626_ = leanh::lean_ctor_get(v_config_623_, 7);
    leanh::lean_inc_ref(v_buildDir_625_);
    v___x_627_ = l_System_FilePath_normalize(v_buildDir_625_);
    leanh::lean_inc_ref(v_dir_624_);
    v___x_628_ = l_Lake_joinRelative(v_dir_624_, v___x_627_);
    leanh::lean_inc_ref(v_nativeLibDir_626_);
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
    mut v_self_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lake_LeanLib_libName(v_self_637_);
    v___x_639_ = 0;
    v___x_640_ = l_Lake_nameToSharedLib(v___x_638_, v___x_639_);
    leanh::lean_dec_ref(v___x_638_);
    return v___x_640_;
}
pub unsafe fn l_Lake_LeanLib_sharedLibFile(
    mut v_self_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_642_ = leanh::lean_ctor_get(v_self_641_, 0);
    v_config_643_ = leanh::lean_ctor_get(v_pkg_642_, 6);
    v_dir_644_ = leanh::lean_ctor_get(v_pkg_642_, 4);
    v_buildDir_645_ = leanh::lean_ctor_get(v_config_643_, 5);
    v_nativeLibDir_646_ = leanh::lean_ctor_get(v_config_643_, 7);
    leanh::lean_inc_ref(v_buildDir_645_);
    v___x_647_ = l_System_FilePath_normalize(v_buildDir_645_);
    leanh::lean_inc_ref(v_dir_644_);
    v___x_648_ = l_Lake_joinRelative(v_dir_644_, v___x_647_);
    leanh::lean_inc_ref(v_nativeLibDir_646_);
    v___x_649_ = l_System_FilePath_normalize(v_nativeLibDir_646_);
    v___x_650_ = l_Lake_joinRelative(v___x_648_, v___x_649_);
    v___x_651_ = l_Lake_LeanLib_libName(v_self_641_);
    v___x_652_ = 0;
    v___x_653_ = l_Lake_nameToSharedLib(v___x_651_, v___x_652_);
    leanh::lean_dec_ref(v___x_651_);
    v___x_654_ = l_Lake_joinRelative(v___x_650_, v___x_653_);
    return v___x_654_;
}
pub unsafe fn l_Lake_LeanLib_isPlugin(mut v_self_655_: *mut leanh::LeanObject) -> u8 {
    let mut v_config_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u8 = 0;
    v_config_656_ = leanh::lean_ctor_get(v_self_655_, 2);
    v_pkg_657_ = leanh::lean_ctor_get(v_self_655_, 0);
    leanh::lean_inc_ref(v_pkg_657_);
    v_roots_658_ = leanh::lean_ctor_get(v_config_656_, 2);
    leanh::lean_inc_ref(v_roots_658_);
    v___x_659_ = lean_array_get_size(v_roots_658_);
    v___x_660_ = leanh::lean_unsigned_to_nat(1);
    v___x_661_ = lean_nat_dec_eq(v___x_659_, v___x_660_);
    if v___x_661_ == 0 {
        leanh::lean_dec_ref(v_roots_658_);
        leanh::lean_dec_ref(v_pkg_657_);
        leanh::lean_dec_ref(v_self_655_);
        return v___x_661_;
    } else {
        let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_667_: u8 = 0;
        v___x_662_ = l_Lake_LeanLib_libName(v_self_655_);
        v___x_663_ = leanh::lean_unsigned_to_nat(0);
        v___x_664_ = lean_array_fget(v_roots_658_, v___x_663_);
        leanh::lean_dec_ref(v_roots_658_);
        v___x_665_ = l_Lake_Package_id_x3f(v_pkg_657_);
        v___x_666_ = l_Lean_mkModuleInitializationStem(v___x_664_, v___x_665_);
        leanh::lean_dec(v___x_665_);
        v___x_667_ = lean_string_dec_eq(v___x_662_, v___x_666_);
        leanh::lean_dec_ref(v___x_666_);
        leanh::lean_dec_ref(v___x_662_);
        return v___x_667_;
    }
}
pub unsafe fn l_Lake_LeanLib_isPlugin___boxed(
    mut v_self_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_669_: u8 = 0;
    let mut v_r_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lake_LeanLib_isPlugin(v_self_668_);
    v_r_670_ = leanh::lean_box((v_res_669_) as usize);
    return v_r_670_;
}
pub unsafe fn l_Lake_LeanLib_extraDepTargets(
    mut v_self_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_672_ = leanh::lean_ctor_get(v_self_671_, 2);
    v_extraDepTargets_673_ = leanh::lean_ctor_get(v_config_672_, 6);
    leanh::lean_inc_ref(v_extraDepTargets_673_);
    return v_extraDepTargets_673_;
}
pub unsafe fn l_Lake_LeanLib_extraDepTargets___boxed(
    mut v_self_674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_675_ = l_Lake_LeanLib_extraDepTargets(v_self_674_);
    leanh::lean_dec_ref(v_self_674_);
    return v_res_675_;
}
pub unsafe fn l_Lake_LeanLib_precompileModules(
    mut v_self_676_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_pkg_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_679_: u8 = 0;
    v_pkg_677_ = leanh::lean_ctor_get(v_self_676_, 0);
    v_config_678_ = leanh::lean_ctor_get(v_pkg_677_, 6);
    v_precompileModules_679_ = leanh::lean_ctor_get_uint8(
        v_config_678_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 1) as u32,
    );
    if v_precompileModules_679_ == 0 {
        let mut v_config_680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_precompileModules_681_: u8 = 0;
        v_config_680_ = leanh::lean_ctor_get(v_self_676_, 2);
        v_precompileModules_681_ = leanh::lean_ctor_get_uint8(
            v_config_680_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 9 + 1) as u32,
        );
        return v_precompileModules_681_;
    } else {
        return v_precompileModules_679_;
    }
}
pub unsafe fn l_Lake_LeanLib_precompileModules___boxed(
    mut v_self_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_683_: u8 = 0;
    let mut v_r_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lake_LeanLib_precompileModules(v_self_682_);
    leanh::lean_dec_ref(v_self_682_);
    v_r_684_ = leanh::lean_box((v_res_683_) as usize);
    return v_r_684_;
}
pub unsafe fn l_Lake_LeanLib_platformIndependent(
    mut v_self_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_686_ = leanh::lean_ctor_get(v_self_685_, 2);
    v_toLeanConfig_687_ = leanh::lean_ctor_get(v_config_686_, 0);
    v_platformIndependent_688_ = leanh::lean_ctor_get(v_toLeanConfig_687_, 10);
    if leanh::lean_obj_tag(v_platformIndependent_688_) == 0 {
        let mut v_pkg_689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_690_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toLeanConfig_691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_platformIndependent_692_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pkg_689_ = leanh::lean_ctor_get(v_self_685_, 0);
        v_config_690_ = leanh::lean_ctor_get(v_pkg_689_, 6);
        v_toLeanConfig_691_ = leanh::lean_ctor_get(v_config_690_, 1);
        v_platformIndependent_692_ = leanh::lean_ctor_get(v_toLeanConfig_691_, 10);
        leanh::lean_inc(v_platformIndependent_692_);
        return v_platformIndependent_692_;
    } else {
        leanh::lean_inc_ref(v_platformIndependent_688_);
        return v_platformIndependent_688_;
    }
}
pub unsafe fn l_Lake_LeanLib_platformIndependent___boxed(
    mut v_self_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lake_LeanLib_platformIndependent(v_self_693_);
    leanh::lean_dec_ref(v_self_693_);
    return v_res_694_;
}
pub unsafe fn l_Lake_LeanLib_defaultFacets(
    mut v_self_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultFacets_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_696_ = leanh::lean_ctor_get(v_self_695_, 2);
    v_defaultFacets_697_ = leanh::lean_ctor_get(v_config_696_, 7);
    leanh::lean_inc_ref(v_defaultFacets_697_);
    return v_defaultFacets_697_;
}
pub unsafe fn l_Lake_LeanLib_defaultFacets___boxed(
    mut v_self_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Lake_LeanLib_defaultFacets(v_self_698_);
    leanh::lean_dec_ref(v_self_698_);
    return v_res_699_;
}
pub unsafe fn l_Lake_LeanLib_nativeFacets(
    mut v_self_700_: *mut leanh::LeanObject,
    mut v_shouldExport_701_: u8,
) -> *mut leanh::LeanObject {
    let mut v_config_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_702_ = leanh::lean_ctor_get(v_self_700_, 2);
    leanh::lean_inc(v_config_702_);
    leanh::lean_dec_ref(v_self_700_);
    v_nativeFacets_703_ = leanh::lean_ctor_get(v_config_702_, 8);
    leanh::lean_inc_ref(v_nativeFacets_703_);
    leanh::lean_dec(v_config_702_);
    v___x_704_ = leanh::lean_box((v_shouldExport_701_) as usize);
    v___x_705_ = leanh::lean_apply_1(v_nativeFacets_703_, v___x_704_);
    return v___x_705_;
}
pub unsafe fn l_Lake_LeanLib_nativeFacets___boxed(
    mut v_self_706_: *mut leanh::LeanObject,
    mut v_shouldExport_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shouldExport_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_708_ = (leanh::lean_unbox(v_shouldExport_707_) as u8);
    v_res_709_ = l_Lake_LeanLib_nativeFacets(v_self_706_, v_shouldExport_boxed_708_);
    return v_res_709_;
}
pub unsafe fn l_Lake_LeanLib_buildType(mut v_self_710_: *mut leanh::LeanObject) -> u8 {
    let mut v_pkg_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_716_: u8 = 0;
    let mut v_buildType_717_: u8 = 0;
    let mut v___x_718_: u8 = 0;
    v_pkg_711_ = leanh::lean_ctor_get(v_self_710_, 0);
    v_config_712_ = leanh::lean_ctor_get(v_pkg_711_, 6);
    v_toLeanConfig_713_ = leanh::lean_ctor_get(v_config_712_, 1);
    v_config_714_ = leanh::lean_ctor_get(v_self_710_, 2);
    v_toLeanConfig_715_ = leanh::lean_ctor_get(v_config_714_, 0);
    v_buildType_716_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_713_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    v_buildType_717_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_715_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    v___x_718_ = l_Lake_instOrdBuildType_ord(v_buildType_716_, v_buildType_717_);
    if v___x_718_ == 2 {
        return v_buildType_717_;
    } else {
        return v_buildType_716_;
    }
}
pub unsafe fn l_Lake_LeanLib_buildType___boxed(
    mut v_self_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: u8 = 0;
    let mut v_r_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Lake_LeanLib_buildType(v_self_719_);
    leanh::lean_dec_ref(v_self_719_);
    v_r_721_ = leanh::lean_box((v_res_720_) as usize);
    return v_r_721_;
}
pub unsafe fn l_Lake_LeanLib_serverOptions(
    mut v_self_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_728_: u8 = 0;
    let mut v_leanOptions_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_731_: u8 = 0;
    let mut v_leanOptions_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_736_: u8 = 0;
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_723_ = leanh::lean_ctor_get(v_self_722_, 0);
                v_config_724_ = leanh::lean_ctor_get(v_pkg_723_, 6);
                v_toLeanConfig_725_ = leanh::lean_ctor_get(v_config_724_, 1);
                v_config_726_ = leanh::lean_ctor_get(v_self_722_, 2);
                v_toLeanConfig_727_ = leanh::lean_ctor_get(v_config_726_, 0);
                v_buildType_728_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_725_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_729_ = leanh::lean_ctor_get(v_toLeanConfig_725_, 0);
                v_moreServerOptions_730_ = leanh::lean_ctor_get(v_toLeanConfig_725_, 4);
                v_buildType_731_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_727_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_732_ = leanh::lean_ctor_get(v_toLeanConfig_727_, 0);
                v_moreServerOptions_733_ = leanh::lean_ctor_get(v_toLeanConfig_727_, 4);
                v___x_734_ = leanh::lean_box(1);
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
    mut v_self_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lake_LeanLib_serverOptions(v_self_745_);
    leanh::lean_dec_ref(v_self_745_);
    return v_res_746_;
}
pub unsafe fn l_Lake_LeanLib_backend(mut v_self_747_: *mut leanh::LeanObject) -> u8 {
    let mut v_config_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_753_: u8 = 0;
    let mut v_backend_754_: u8 = 0;
    let mut v___x_755_: u8 = 0;
    v_config_748_ = leanh::lean_ctor_get(v_self_747_, 2);
    v_toLeanConfig_749_ = leanh::lean_ctor_get(v_config_748_, 0);
    v_pkg_750_ = leanh::lean_ctor_get(v_self_747_, 0);
    v_config_751_ = leanh::lean_ctor_get(v_pkg_750_, 6);
    v_toLeanConfig_752_ = leanh::lean_ctor_get(v_config_751_, 1);
    v_backend_753_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_749_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    v_backend_754_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_752_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    v___x_755_ = l_Lake_Backend_orPreferLeft(v_backend_753_, v_backend_754_);
    return v___x_755_;
}
pub unsafe fn l_Lake_LeanLib_backend___boxed(
    mut v_self_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_757_: u8 = 0;
    let mut v_r_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lake_LeanLib_backend(v_self_756_);
    leanh::lean_dec_ref(v_self_756_);
    v_r_758_ = leanh::lean_box((v_res_757_) as usize);
    return v_r_758_;
}
pub unsafe fn l_Lake_LeanLib_allowImportAll(mut v_self_759_: *mut leanh::LeanObject) -> u8 {
    let mut v_config_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_761_: u8 = 0;
    v_config_760_ = leanh::lean_ctor_get(v_self_759_, 2);
    v_allowImportAll_761_ = leanh::lean_ctor_get_uint8(
        v_config_760_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 9 + 2) as u32,
    );
    if v_allowImportAll_761_ == 0 {
        let mut v_pkg_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_allowImportAll_764_: u8 = 0;
        v_pkg_762_ = leanh::lean_ctor_get(v_self_759_, 0);
        v_config_763_ = leanh::lean_ctor_get(v_pkg_762_, 6);
        v_allowImportAll_764_ = leanh::lean_ctor_get_uint8(
            v_config_763_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 5) as u32,
        );
        return v_allowImportAll_764_;
    } else {
        return v_allowImportAll_761_;
    }
}
pub unsafe fn l_Lake_LeanLib_allowImportAll___boxed(
    mut v_self_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_766_: u8 = 0;
    let mut v_r_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Lake_LeanLib_allowImportAll(v_self_765_);
    leanh::lean_dec_ref(v_self_765_);
    v_r_767_ = leanh::lean_box((v_res_766_) as usize);
    return v_r_767_;
}
pub unsafe fn l_Lake_LeanLib_dynlibs(
    mut v_self_768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_769_ = leanh::lean_ctor_get(v_self_768_, 0);
    v_config_770_ = leanh::lean_ctor_get(v_pkg_769_, 6);
    v_toLeanConfig_771_ = leanh::lean_ctor_get(v_config_770_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_771_);
    v_config_772_ = leanh::lean_ctor_get(v_self_768_, 2);
    leanh::lean_inc(v_config_772_);
    leanh::lean_dec_ref(v_self_768_);
    v_toLeanConfig_773_ = leanh::lean_ctor_get(v_config_772_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_773_);
    leanh::lean_dec(v_config_772_);
    v_dynlibs_774_ = leanh::lean_ctor_get(v_toLeanConfig_771_, 11);
    leanh::lean_inc_ref(v_dynlibs_774_);
    leanh::lean_dec_ref(v_toLeanConfig_771_);
    v_dynlibs_775_ = leanh::lean_ctor_get(v_toLeanConfig_773_, 11);
    leanh::lean_inc_ref(v_dynlibs_775_);
    leanh::lean_dec_ref(v_toLeanConfig_773_);
    v___x_776_ = l_Array_append___redArg(v_dynlibs_774_, v_dynlibs_775_);
    leanh::lean_dec_ref(v_dynlibs_775_);
    return v___x_776_;
}
pub unsafe fn l_Lake_LeanLib_plugins(
    mut v_self_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_778_ = leanh::lean_ctor_get(v_self_777_, 0);
    v_config_779_ = leanh::lean_ctor_get(v_pkg_778_, 6);
    v_toLeanConfig_780_ = leanh::lean_ctor_get(v_config_779_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_780_);
    v_config_781_ = leanh::lean_ctor_get(v_self_777_, 2);
    leanh::lean_inc(v_config_781_);
    leanh::lean_dec_ref(v_self_777_);
    v_toLeanConfig_782_ = leanh::lean_ctor_get(v_config_781_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_782_);
    leanh::lean_dec(v_config_781_);
    v_plugins_783_ = leanh::lean_ctor_get(v_toLeanConfig_780_, 12);
    leanh::lean_inc_ref(v_plugins_783_);
    leanh::lean_dec_ref(v_toLeanConfig_780_);
    v_plugins_784_ = leanh::lean_ctor_get(v_toLeanConfig_782_, 12);
    leanh::lean_inc_ref(v_plugins_784_);
    leanh::lean_dec_ref(v_toLeanConfig_782_);
    v___x_785_ = l_Array_append___redArg(v_plugins_783_, v_plugins_784_);
    leanh::lean_dec_ref(v_plugins_784_);
    return v___x_785_;
}
pub unsafe fn l_Lake_LeanLib_leanOptions(
    mut v_self_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_792_: u8 = 0;
    let mut v_leanOptions_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_794_: u8 = 0;
    let mut v_leanOptions_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: u8 = 0;
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_787_ = leanh::lean_ctor_get(v_self_786_, 0);
                v_config_788_ = leanh::lean_ctor_get(v_pkg_787_, 6);
                v_toLeanConfig_789_ = leanh::lean_ctor_get(v_config_788_, 1);
                v_config_790_ = leanh::lean_ctor_get(v_self_786_, 2);
                v_toLeanConfig_791_ = leanh::lean_ctor_get(v_config_790_, 0);
                v_buildType_792_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_789_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_793_ = leanh::lean_ctor_get(v_toLeanConfig_789_, 0);
                v_buildType_794_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_791_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_795_ = leanh::lean_ctor_get(v_toLeanConfig_791_, 0);
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
    mut v_self_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_LeanLib_leanOptions(v_self_803_);
    leanh::lean_dec_ref(v_self_803_);
    return v_res_804_;
}
pub unsafe fn l_Lake_LeanLib_leanArgs(
    mut v_self_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_811_: u8 = 0;
    let mut v_moreLeanArgs_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_813_: u8 = 0;
    let mut v_moreLeanArgs_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_816_: u8 = 0;
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_806_ = leanh::lean_ctor_get(v_self_805_, 0);
                v_config_807_ = leanh::lean_ctor_get(v_pkg_806_, 6);
                v_toLeanConfig_808_ = leanh::lean_ctor_get(v_config_807_, 1);
                v_config_809_ = leanh::lean_ctor_get(v_self_805_, 2);
                v_toLeanConfig_810_ = leanh::lean_ctor_get(v_config_809_, 0);
                v_buildType_811_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_808_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_812_ = leanh::lean_ctor_get(v_toLeanConfig_808_, 1);
                v_buildType_813_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_810_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_814_ = leanh::lean_ctor_get(v_toLeanConfig_810_, 1);
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
pub unsafe fn l_Lake_LeanLib_leanArgs___boxed(
    mut v_self_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lake_LeanLib_leanArgs(v_self_821_);
    leanh::lean_dec_ref(v_self_821_);
    return v_res_822_;
}
pub unsafe fn l_Lake_LeanLib_weakLeanArgs(
    mut v_self_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_824_ = leanh::lean_ctor_get(v_self_823_, 0);
    v_config_825_ = leanh::lean_ctor_get(v_pkg_824_, 6);
    v_toLeanConfig_826_ = leanh::lean_ctor_get(v_config_825_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_826_);
    v_config_827_ = leanh::lean_ctor_get(v_self_823_, 2);
    leanh::lean_inc(v_config_827_);
    leanh::lean_dec_ref(v_self_823_);
    v_toLeanConfig_828_ = leanh::lean_ctor_get(v_config_827_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_828_);
    leanh::lean_dec(v_config_827_);
    v_weakLeanArgs_829_ = leanh::lean_ctor_get(v_toLeanConfig_826_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_829_);
    leanh::lean_dec_ref(v_toLeanConfig_826_);
    v_weakLeanArgs_830_ = leanh::lean_ctor_get(v_toLeanConfig_828_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_830_);
    leanh::lean_dec_ref(v_toLeanConfig_828_);
    v___x_831_ = l_Array_append___redArg(v_weakLeanArgs_829_, v_weakLeanArgs_830_);
    leanh::lean_dec_ref(v_weakLeanArgs_830_);
    return v___x_831_;
}
pub unsafe fn l_Lake_LeanLib_leancArgs(
    mut v_self_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_838_: u8 = 0;
    let mut v_moreLeancArgs_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_840_: u8 = 0;
    let mut v_moreLeancArgs_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_843_: u8 = 0;
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_833_ = leanh::lean_ctor_get(v_self_832_, 0);
                v_config_834_ = leanh::lean_ctor_get(v_pkg_833_, 6);
                v_toLeanConfig_835_ = leanh::lean_ctor_get(v_config_834_, 1);
                v_config_836_ = leanh::lean_ctor_get(v_self_832_, 2);
                v_toLeanConfig_837_ = leanh::lean_ctor_get(v_config_836_, 0);
                v_buildType_838_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_835_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_839_ = leanh::lean_ctor_get(v_toLeanConfig_835_, 3);
                v_buildType_840_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_837_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_841_ = leanh::lean_ctor_get(v_toLeanConfig_837_, 3);
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
    mut v_self_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Lake_LeanLib_leancArgs(v_self_848_);
    leanh::lean_dec_ref(v_self_848_);
    return v_res_849_;
}
pub unsafe fn l_Lake_LeanLib_weakLeancArgs(
    mut v_self_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_851_ = leanh::lean_ctor_get(v_self_850_, 0);
    v_config_852_ = leanh::lean_ctor_get(v_pkg_851_, 6);
    v_toLeanConfig_853_ = leanh::lean_ctor_get(v_config_852_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_853_);
    v_config_854_ = leanh::lean_ctor_get(v_self_850_, 2);
    leanh::lean_inc(v_config_854_);
    leanh::lean_dec_ref(v_self_850_);
    v_toLeanConfig_855_ = leanh::lean_ctor_get(v_config_854_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_855_);
    leanh::lean_dec(v_config_854_);
    v_weakLeancArgs_856_ = leanh::lean_ctor_get(v_toLeanConfig_853_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_856_);
    leanh::lean_dec_ref(v_toLeanConfig_853_);
    v_weakLeancArgs_857_ = leanh::lean_ctor_get(v_toLeanConfig_855_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_857_);
    leanh::lean_dec_ref(v_toLeanConfig_855_);
    v___x_858_ = l_Array_append___redArg(v_weakLeancArgs_856_, v_weakLeancArgs_857_);
    leanh::lean_dec_ref(v_weakLeancArgs_857_);
    return v___x_858_;
}
pub unsafe fn l_Lake_LeanLib_moreLinkObjs(
    mut v_self_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_860_ = leanh::lean_ctor_get(v_self_859_, 0);
    v_config_861_ = leanh::lean_ctor_get(v_pkg_860_, 6);
    v_toLeanConfig_862_ = leanh::lean_ctor_get(v_config_861_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_862_);
    v_config_863_ = leanh::lean_ctor_get(v_self_859_, 2);
    leanh::lean_inc(v_config_863_);
    leanh::lean_dec_ref(v_self_859_);
    v_toLeanConfig_864_ = leanh::lean_ctor_get(v_config_863_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_864_);
    leanh::lean_dec(v_config_863_);
    v_moreLinkObjs_865_ = leanh::lean_ctor_get(v_toLeanConfig_862_, 6);
    leanh::lean_inc_ref(v_moreLinkObjs_865_);
    leanh::lean_dec_ref(v_toLeanConfig_862_);
    v_moreLinkObjs_866_ = leanh::lean_ctor_get(v_toLeanConfig_864_, 6);
    leanh::lean_inc_ref(v_moreLinkObjs_866_);
    leanh::lean_dec_ref(v_toLeanConfig_864_);
    v___x_867_ = l_Array_append___redArg(v_moreLinkObjs_865_, v_moreLinkObjs_866_);
    leanh::lean_dec_ref(v_moreLinkObjs_866_);
    return v___x_867_;
}
pub unsafe fn l_Lake_LeanLib_moreLinkLibs(
    mut v_self_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_869_ = leanh::lean_ctor_get(v_self_868_, 0);
    v_config_870_ = leanh::lean_ctor_get(v_pkg_869_, 6);
    v_toLeanConfig_871_ = leanh::lean_ctor_get(v_config_870_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_871_);
    v_config_872_ = leanh::lean_ctor_get(v_self_868_, 2);
    leanh::lean_inc(v_config_872_);
    leanh::lean_dec_ref(v_self_868_);
    v_toLeanConfig_873_ = leanh::lean_ctor_get(v_config_872_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_873_);
    leanh::lean_dec(v_config_872_);
    v_moreLinkLibs_874_ = leanh::lean_ctor_get(v_toLeanConfig_871_, 7);
    leanh::lean_inc_ref(v_moreLinkLibs_874_);
    leanh::lean_dec_ref(v_toLeanConfig_871_);
    v_moreLinkLibs_875_ = leanh::lean_ctor_get(v_toLeanConfig_873_, 7);
    leanh::lean_inc_ref(v_moreLinkLibs_875_);
    leanh::lean_dec_ref(v_toLeanConfig_873_);
    v___x_876_ = l_Array_append___redArg(v_moreLinkLibs_874_, v_moreLinkLibs_875_);
    leanh::lean_dec_ref(v_moreLinkLibs_875_);
    return v___x_876_;
}
pub unsafe fn l_Lake_LeanLib_linkArgs(
    mut v_self_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_878_ = leanh::lean_ctor_get(v_self_877_, 0);
    v_config_879_ = leanh::lean_ctor_get(v_pkg_878_, 6);
    v_toLeanConfig_880_ = leanh::lean_ctor_get(v_config_879_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_880_);
    v_config_881_ = leanh::lean_ctor_get(v_self_877_, 2);
    leanh::lean_inc(v_config_881_);
    leanh::lean_dec_ref(v_self_877_);
    v_toLeanConfig_882_ = leanh::lean_ctor_get(v_config_881_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_882_);
    leanh::lean_dec(v_config_881_);
    v_moreLinkArgs_883_ = leanh::lean_ctor_get(v_toLeanConfig_880_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_883_);
    leanh::lean_dec_ref(v_toLeanConfig_880_);
    v_moreLinkArgs_884_ = leanh::lean_ctor_get(v_toLeanConfig_882_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_884_);
    leanh::lean_dec_ref(v_toLeanConfig_882_);
    v___x_885_ = l_Array_append___redArg(v_moreLinkArgs_883_, v_moreLinkArgs_884_);
    leanh::lean_dec_ref(v_moreLinkArgs_884_);
    return v___x_885_;
}
pub unsafe fn l_Lake_LeanLib_weakLinkArgs(
    mut v_self_886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_887_ = leanh::lean_ctor_get(v_self_886_, 0);
    v_config_888_ = leanh::lean_ctor_get(v_pkg_887_, 6);
    v_toLeanConfig_889_ = leanh::lean_ctor_get(v_config_888_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_889_);
    v_config_890_ = leanh::lean_ctor_get(v_self_886_, 2);
    leanh::lean_inc(v_config_890_);
    leanh::lean_dec_ref(v_self_886_);
    v_toLeanConfig_891_ = leanh::lean_ctor_get(v_config_890_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_891_);
    leanh::lean_dec(v_config_890_);
    v_weakLinkArgs_892_ = leanh::lean_ctor_get(v_toLeanConfig_889_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_892_);
    leanh::lean_dec_ref(v_toLeanConfig_889_);
    v_weakLinkArgs_893_ = leanh::lean_ctor_get(v_toLeanConfig_891_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_893_);
    leanh::lean_dec_ref(v_toLeanConfig_891_);
    v___x_894_ = l_Array_append___redArg(v_weakLinkArgs_892_, v_weakLinkArgs_893_);
    leanh::lean_dec_ref(v_weakLinkArgs_893_);
    return v___x_894_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanLib(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanLib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanLib(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Lake_Util_NativeLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_LeanLib(builtin);
}