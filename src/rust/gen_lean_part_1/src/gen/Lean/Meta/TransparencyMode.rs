// Lean compiler output
// Module: Lean.Meta.TransparencyMode
// Imports: Init.Data.UInt.Basic Init.MetaTypes
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
pub static l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_TransparencyMode_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_TransparencyMode_instHashable__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_TransparencyMode_instHashable__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_TransparencyMode_hash(mut v_x_39_: u8) -> u64 {
    match v_x_39_ {
        0 => {
            let mut v___x_40_: u64 = 0;
            v___x_40_ = 7u64;
            return v___x_40_;
        }
        1 => {
            let mut v___x_41_: u64 = 0;
            v___x_41_ = 11u64;
            return v___x_41_;
        }
        2 => {
            let mut v___x_42_: u64 = 0;
            v___x_42_ = 13u64;
            return v___x_42_;
        }
        3 => {
            let mut v___x_43_: u64 = 0;
            v___x_43_ = 17u64;
            return v___x_43_;
        }
        _ => {
            let mut v___x_44_: u64 = 0;
            v___x_44_ = 19u64;
            return v___x_44_;
        }
    }
}
pub unsafe fn l_Lean_Meta_TransparencyMode_hash___boxed(
    mut v_x_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_64__boxed_46_: u8 = 0;
    let mut v_res_47_: u64 = 0;
    let mut v_r_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_64__boxed_46_ = (leanh::lean_unbox(v_x_45_) as u8);
    v_res_47_ = l_Lean_Meta_TransparencyMode_hash(v_x_64__boxed_46_);
    v_r_48_ = leanh::lean_box_uint64(v_res_47_);
    return v_r_48_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_lt(mut v_x_51_: u8, mut v_x_52_: u8) -> u8 {
    match v_x_52_ {
        4 => {
            let mut v___x_53_: u8 = 0;
            v___x_53_ = 0;
            return v___x_53_;
        }
        2 => match v_x_51_ {
            4 => {
                let mut v___x_54_: u8 = 0;
                v___x_54_ = 1;
                return v___x_54_;
            }
            2 => {
                let mut v___x_55_: u8 = 0;
                v___x_55_ = 0;
                return v___x_55_;
            }
            3 => {
                let mut v___x_56_: u8 = 0;
                v___x_56_ = 0;
                return v___x_56_;
            }
            _ => {
                let mut v___x_57_: u8 = 0;
                v___x_57_ = 0;
                return v___x_57_;
            }
        },
        3 => match v_x_51_ {
            4 => {
                let mut v___x_58_: u8 = 0;
                v___x_58_ = 1;
                return v___x_58_;
            }
            2 => {
                let mut v___x_59_: u8 = 0;
                v___x_59_ = 1;
                return v___x_59_;
            }
            3 => {
                let mut v___x_60_: u8 = 0;
                v___x_60_ = 0;
                return v___x_60_;
            }
            _ => {
                let mut v___x_61_: u8 = 0;
                v___x_61_ = 0;
                return v___x_61_;
            }
        },
        0 => match v_x_51_ {
            4 => {
                let mut v___x_62_: u8 = 0;
                v___x_62_ = 1;
                return v___x_62_;
            }
            2 => {
                let mut v___x_63_: u8 = 0;
                v___x_63_ = 1;
                return v___x_63_;
            }
            3 => {
                let mut v___x_64_: u8 = 0;
                v___x_64_ = 1;
                return v___x_64_;
            }
            1 => {
                let mut v___x_65_: u8 = 0;
                v___x_65_ = 1;
                return v___x_65_;
            }
            _ => {
                let mut v___x_66_: u8 = 0;
                v___x_66_ = 0;
                return v___x_66_;
            }
        },
        _ => match v_x_51_ {
            4 => {
                let mut v___x_67_: u8 = 0;
                v___x_67_ = 1;
                return v___x_67_;
            }
            2 => {
                let mut v___x_68_: u8 = 0;
                v___x_68_ = 1;
                return v___x_68_;
            }
            3 => {
                let mut v___x_69_: u8 = 0;
                v___x_69_ = 1;
                return v___x_69_;
            }
            _ => {
                let mut v___x_70_: u8 = 0;
                v___x_70_ = 0;
                return v___x_70_;
            }
        },
    }
}
pub unsafe fn l_Lean_Meta_TransparencyMode_lt___boxed(
    mut v_x_71_: *mut leanh::LeanObject,
    mut v_x_72_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_104__boxed_73_: u8 = 0;
    let mut v_x_105__boxed_74_: u8 = 0;
    let mut v_res_75_: u8 = 0;
    let mut v_r_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_104__boxed_73_ = (leanh::lean_unbox(v_x_71_) as u8);
    v_x_105__boxed_74_ = (leanh::lean_unbox(v_x_72_) as u8);
    v_res_75_ = l_Lean_Meta_TransparencyMode_lt(v_x_104__boxed_73_, v_x_105__boxed_74_);
    v_r_76_ = leanh::lean_box((v_res_75_) as usize);
    return v_r_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_TransparencyMode(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_MetaTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_TransparencyMode(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_TransparencyMode(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_TransparencyMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_TransparencyMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_TransparencyMode(builtin);
}