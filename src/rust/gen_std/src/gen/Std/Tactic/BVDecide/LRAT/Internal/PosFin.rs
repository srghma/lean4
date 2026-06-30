// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.PosFin
// Imports: Init.Data.Hashable
use crate::ffi::lean_nat_dec_eq;
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt64_ofNat___boxed;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0_value:
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
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0_value:
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
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0_value:
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
    m_fun: l_Nat_reprFast as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1___redArg(
    mut v_a_51_: *mut leanh::LeanObject,
    mut v_b_52_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_53_: u8 = 0;
    v___x_53_ = lean_nat_dec_eq(v_a_51_, v_b_52_);
    return v___x_53_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1___redArg___boxed(
    mut v_a_54_: *mut leanh::LeanObject,
    mut v_b_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_56_: u8 = 0;
    let mut v_r_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1___redArg(
        v_a_54_, v_b_55_,
    );
    leanh::lean_dec(v_b_55_);
    leanh::lean_dec(v_a_54_);
    v_r_57_ = leanh::lean_box((v_res_56_) as usize);
    return v_r_57_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1(
    mut v_n_58_: *mut leanh::LeanObject,
    mut v_a_59_: *mut leanh::LeanObject,
    mut v_b_60_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_61_: u8 = 0;
    v___x_61_ = lean_nat_dec_eq(v_a_59_, v_b_60_);
    return v___x_61_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1___boxed(
    mut v_n_62_: *mut leanh::LeanObject,
    mut v_a_63_: *mut leanh::LeanObject,
    mut v_b_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_65_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___aux__1(
        v_n_62_, v_a_63_, v_b_64_,
    );
    leanh::lean_dec(v_b_64_);
    leanh::lean_dec(v_a_63_);
    leanh::lean_dec(v_n_62_);
    v_r_66_ = leanh::lean_box((v_res_65_) as usize);
    return v_r_66_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg(
    mut v_a_67_: *mut leanh::LeanObject,
    mut v_b_68_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_69_: u8 = 0;
    v___x_69_ = lean_nat_dec_eq(v_a_67_, v_b_68_);
    return v___x_69_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg___boxed(
    mut v_a_70_: *mut leanh::LeanObject,
    mut v_b_71_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_72_: u8 = 0;
    let mut v_r_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg(v_a_70_, v_b_71_);
    leanh::lean_dec(v_b_71_);
    leanh::lean_dec(v_a_70_);
    v_r_73_ = leanh::lean_box((v_res_72_) as usize);
    return v_r_73_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin(
    mut v_n_74_: *mut leanh::LeanObject,
    mut v_a_75_: *mut leanh::LeanObject,
    mut v_b_76_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_77_: u8 = 0;
    v___x_77_ = lean_nat_dec_eq(v_a_75_, v_b_76_);
    return v___x_77_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(
    mut v_n_78_: *mut leanh::LeanObject,
    mut v_a_79_: *mut leanh::LeanObject,
    mut v_b_80_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_81_: u8 = 0;
    let mut v_r_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_81_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin(v_n_78_, v_a_79_, v_b_80_);
    leanh::lean_dec(v_b_80_);
    leanh::lean_dec(v_a_79_);
    leanh::lean_dec(v_n_78_);
    v_r_82_ = leanh::lean_box((v_res_81_) as usize);
    return v_r_82_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0(
    mut v_p_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_p_83_);
    return v_p_83_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0___boxed(
    mut v_p_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_85_ = l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0(v_p_84_);
    leanh::lean_dec(v_p_84_);
    return v_res_85_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat(
    mut v_n_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_88_ = l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0;
    return v___f_88_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___boxed(
    mut v_n_89_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_90_ = l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat(v_n_89_);
    leanh::lean_dec(v_n_89_);
    return v_res_90_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin(
    mut v_n_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_93_ = l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0;
    return v___f_93_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___boxed(
    mut v_n_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_95_ = l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin(v_n_94_);
    leanh::lean_dec(v_n_94_);
    return v_res_95_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin(
    mut v_n_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_98_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0;
    return v___f_98_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___boxed(
    mut v_n_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin(v_n_99_);
    leanh::lean_dec(v_n_99_);
    return v_res_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
}