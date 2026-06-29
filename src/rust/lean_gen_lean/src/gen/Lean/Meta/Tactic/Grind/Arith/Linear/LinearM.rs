// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types, l_Lean_Meta_Grind_Arith_Linear_linearExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 115, 116, 114, 117, 99, 116,
        117, 114, 101, 32, 105, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 0,
    m_objs: [],
};
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value:
    crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value:
    crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 109, 109, 117,
        116, 97, 116, 105, 118, 101, 32, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(
    mut v_a_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_818_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_817_, v_a_814_, v_a_815_);
    return v___x_818_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_819_, v_a_820_);
    crate::leanh::lean_dec_ref(v_a_820_);
    crate::leanh::lean_dec(v_a_819_);
    return v_res_822_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27(
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
    mut v_a_830_: *mut crate::leanh::LeanObject,
    mut v_a_831_: *mut crate::leanh::LeanObject,
    mut v_a_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_823_, v_a_831_);
    return v___x_834_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(
    mut v_a_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(
        v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_,
        v_a_844_,
    );
    crate::leanh::lean_dec(v_a_844_);
    crate::leanh::lean_dec_ref(v_a_843_);
    crate::leanh::lean_dec(v_a_842_);
    crate::leanh::lean_dec_ref(v_a_841_);
    crate::leanh::lean_dec(v_a_840_);
    crate::leanh::lean_dec_ref(v_a_839_);
    crate::leanh::lean_dec(v_a_838_);
    crate::leanh::lean_dec_ref(v_a_837_);
    crate::leanh::lean_dec(v_a_836_);
    crate::leanh::lean_dec(v_a_835_);
    return v_res_846_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(
    mut v_f_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_851_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_850_, v_f_847_, v_a_848_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(
    mut v_f_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_852_, v_a_853_);
    crate::leanh::lean_dec(v_a_853_);
    return v_res_855_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27(
    mut v_f_856_: *mut crate::leanh::LeanObject,
    mut v_a_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
    mut v_a_863_: *mut crate::leanh::LeanObject,
    mut v_a_864_: *mut crate::leanh::LeanObject,
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_868_, v_f_856_, v_a_857_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(
    mut v_f_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_a_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_a_879_: *mut crate::leanh::LeanObject,
    mut v_a_880_: *mut crate::leanh::LeanObject,
    mut v_a_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_882_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(
        v_f_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_,
        v_a_879_, v_a_880_,
    );
    crate::leanh::lean_dec(v_a_880_);
    crate::leanh::lean_dec_ref(v_a_879_);
    crate::leanh::lean_dec(v_a_878_);
    crate::leanh::lean_dec_ref(v_a_877_);
    crate::leanh::lean_dec(v_a_876_);
    crate::leanh::lean_dec_ref(v_a_875_);
    crate::leanh::lean_dec(v_a_874_);
    crate::leanh::lean_dec_ref(v_a_873_);
    crate::leanh::lean_dec(v_a_872_);
    crate::leanh::lean_dec(v_a_871_);
    return v_res_882_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(
    mut v_inst_883_: *mut crate::leanh::LeanObject,
    mut v_inst_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = crate::leanh::lean_apply_2(v_inst_883_, crate::leanh::lean_box(0), v_inst_884_);
    return v___x_885_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(
    mut v_m_886_: *mut crate::leanh::LeanObject,
    mut v_n_887_: *mut crate::leanh::LeanObject,
    mut v_inst_888_: *mut crate::leanh::LeanObject,
    mut v_inst_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = crate::leanh::lean_apply_2(v_inst_888_, crate::leanh::lean_box(0), v_inst_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(
    mut v_structId_891_: *mut crate::leanh::LeanObject,
    mut v_x_892_: *mut crate::leanh::LeanObject,
    mut v_a_893_: *mut crate::leanh::LeanObject,
    mut v_a_894_: *mut crate::leanh::LeanObject,
    mut v_a_895_: *mut crate::leanh::LeanObject,
    mut v_a_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_a_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_902_);
    crate::leanh::lean_inc_ref(v_a_901_);
    crate::leanh::lean_inc(v_a_900_);
    crate::leanh::lean_inc_ref(v_a_899_);
    crate::leanh::lean_inc(v_a_898_);
    crate::leanh::lean_inc_ref(v_a_897_);
    crate::leanh::lean_inc(v_a_896_);
    crate::leanh::lean_inc_ref(v_a_895_);
    crate::leanh::lean_inc(v_a_894_);
    crate::leanh::lean_inc(v_a_893_);
    v___x_904_ = crate::leanh::lean_apply_12(
        v_x_892_,
        v_structId_891_,
        v_a_893_,
        v_a_894_,
        v_a_895_,
        v_a_896_,
        v_a_897_,
        v_a_898_,
        v_a_899_,
        v_a_900_,
        v_a_901_,
        v_a_902_,
        crate::leanh::lean_box(0),
    );
    return v___x_904_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(
    mut v_structId_905_: *mut crate::leanh::LeanObject,
    mut v_x_906_: *mut crate::leanh::LeanObject,
    mut v_a_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
    mut v_a_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
    mut v_a_912_: *mut crate::leanh::LeanObject,
    mut v_a_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
    mut v_a_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(
        v_structId_905_,
        v_x_906_,
        v_a_907_,
        v_a_908_,
        v_a_909_,
        v_a_910_,
        v_a_911_,
        v_a_912_,
        v_a_913_,
        v_a_914_,
        v_a_915_,
        v_a_916_,
    );
    crate::leanh::lean_dec(v_a_916_);
    crate::leanh::lean_dec_ref(v_a_915_);
    crate::leanh::lean_dec(v_a_914_);
    crate::leanh::lean_dec_ref(v_a_913_);
    crate::leanh::lean_dec(v_a_912_);
    crate::leanh::lean_dec_ref(v_a_911_);
    crate::leanh::lean_dec(v_a_910_);
    crate::leanh::lean_dec_ref(v_a_909_);
    crate::leanh::lean_dec(v_a_908_);
    crate::leanh::lean_dec(v_a_907_);
    return v_res_918_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run(
    mut v_00_u03b1_919_: *mut crate::leanh::LeanObject,
    mut v_structId_920_: *mut crate::leanh::LeanObject,
    mut v_x_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
    mut v_a_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_931_);
    crate::leanh::lean_inc_ref(v_a_930_);
    crate::leanh::lean_inc(v_a_929_);
    crate::leanh::lean_inc_ref(v_a_928_);
    crate::leanh::lean_inc(v_a_927_);
    crate::leanh::lean_inc_ref(v_a_926_);
    crate::leanh::lean_inc(v_a_925_);
    crate::leanh::lean_inc_ref(v_a_924_);
    crate::leanh::lean_inc(v_a_923_);
    crate::leanh::lean_inc(v_a_922_);
    v___x_933_ = crate::leanh::lean_apply_12(
        v_x_921_,
        v_structId_920_,
        v_a_922_,
        v_a_923_,
        v_a_924_,
        v_a_925_,
        v_a_926_,
        v_a_927_,
        v_a_928_,
        v_a_929_,
        v_a_930_,
        v_a_931_,
        crate::leanh::lean_box(0),
    );
    return v___x_933_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(
    mut v_00_u03b1_934_: *mut crate::leanh::LeanObject,
    mut v_structId_935_: *mut crate::leanh::LeanObject,
    mut v_x_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
    mut v_a_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
    mut v_a_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run(
        v_00_u03b1_934_,
        v_structId_935_,
        v_x_936_,
        v_a_937_,
        v_a_938_,
        v_a_939_,
        v_a_940_,
        v_a_941_,
        v_a_942_,
        v_a_943_,
        v_a_944_,
        v_a_945_,
        v_a_946_,
    );
    crate::leanh::lean_dec(v_a_946_);
    crate::leanh::lean_dec_ref(v_a_945_);
    crate::leanh::lean_dec(v_a_944_);
    crate::leanh::lean_dec_ref(v_a_943_);
    crate::leanh::lean_dec(v_a_942_);
    crate::leanh::lean_dec_ref(v_a_941_);
    crate::leanh::lean_dec(v_a_940_);
    crate::leanh::lean_dec_ref(v_a_939_);
    crate::leanh::lean_dec(v_a_938_);
    crate::leanh::lean_dec(v_a_937_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(
    mut v_a_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_949_);
    v___x_951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_951_, 0, v_a_949_);
    return v___x_951_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_952_);
    crate::leanh::lean_dec(v_a_952_);
    return v_res_954_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId(
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
    mut v_a_961_: *mut crate::leanh::LeanObject,
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
    mut v_a_964_: *mut crate::leanh::LeanObject,
    mut v_a_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_955_);
    v___x_967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_967_, 0, v_a_955_);
    return v___x_967_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
    mut v_a_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(
        v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_,
        v_a_977_, v_a_978_,
    );
    crate::leanh::lean_dec(v_a_978_);
    crate::leanh::lean_dec_ref(v_a_977_);
    crate::leanh::lean_dec(v_a_976_);
    crate::leanh::lean_dec_ref(v_a_975_);
    crate::leanh::lean_dec(v_a_974_);
    crate::leanh::lean_dec_ref(v_a_973_);
    crate::leanh::lean_dec(v_a_972_);
    crate::leanh::lean_dec_ref(v_a_971_);
    crate::leanh::lean_dec(v_a_970_);
    crate::leanh::lean_dec(v_a_969_);
    crate::leanh::lean_dec(v_a_968_);
    return v_res_980_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(
    mut v_msgData_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_st_ref_get(v___y_985_);
    v_env_988_ = crate::leanh::lean_ctor_get(v___x_987_, 0);
    crate::leanh::lean_inc_ref(v_env_988_);
    crate::leanh::lean_dec(v___x_987_);
    v___x_989_ = lean_st_ref_get(v___y_983_);
    v_mctx_990_ = crate::leanh::lean_ctor_get(v___x_989_, 0);
    crate::leanh::lean_inc_ref(v_mctx_990_);
    crate::leanh::lean_dec(v___x_989_);
    v_lctx_991_ = crate::leanh::lean_ctor_get(v___y_982_, 2);
    v_options_992_ = crate::leanh::lean_ctor_get(v___y_984_, 2);
    crate::leanh::lean_inc_ref(v_options_992_);
    crate::leanh::lean_inc_ref(v_lctx_991_);
    v___x_993_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_993_, 0, v_env_988_);
    crate::leanh::lean_ctor_set(v___x_993_, 1, v_mctx_990_);
    crate::leanh::lean_ctor_set(v___x_993_, 2, v_lctx_991_);
    crate::leanh::lean_ctor_set(v___x_993_, 3, v_options_992_);
    v___x_994_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_994_, 0, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_994_, 1, v_msgData_981_);
    v___x_995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_994_);
    return v___x_995_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
    crate::leanh::lean_dec(v___y_1000_);
    crate::leanh::lean_dec_ref(v___y_999_);
    crate::leanh::lean_dec(v___y_998_);
    crate::leanh::lean_dec_ref(v___y_997_);
    return v_res_1002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
    mut v_msg_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1009_ = crate::leanh::lean_ctor_get(v___y_1006_, 5);
                v___x_1010_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
                v_a_1011_ = crate::leanh::lean_ctor_get(v___x_1010_, 0);
                v_isSharedCheck_1019_ = (!crate::leanh::lean_is_exclusive(v___x_1010_)) as u8;
                if v_isSharedCheck_1019_ == 0 {
                    v___x_1013_ = v___x_1010_;
                    v_isShared_1014_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1011_);
                    crate::leanh::lean_dec(v___x_1010_);
                    v___x_1013_ = crate::leanh::lean_box(0);
                    v_isShared_1014_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1009_);
                v___x_1015_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1015_, 0, v_ref_1009_);
                crate::leanh::lean_ctor_set(v___x_1015_, 1, v_a_1011_);
                if v_isShared_1014_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1013_, 1);
                    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1015_);
                    v___x_1017_ = v___x_1013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(
    mut v_msg_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
            v_msg_1020_,
            v___y_1021_,
            v___y_1022_,
            v___y_1023_,
            v___y_1024_,
        );
    crate::leanh::lean_dec(v___y_1024_);
    crate::leanh::lean_dec_ref(v___y_1023_);
    crate::leanh::lean_dec(v___y_1022_);
    crate::leanh::lean_dec_ref(v___y_1021_);
    return v_res_1026_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0;
    v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
    return v___x_1029_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
    mut v_a_1030_: *mut crate::leanh::LeanObject,
    mut v_a_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1046_: u8 = 0;
    let mut v_structs_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1042_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_1031_, v_a_1039_);
                if crate::leanh::lean_obj_tag(v___x_1042_) == 0 {
                    v_a_1043_ = crate::leanh::lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1056_ = (!crate::leanh::lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1045_ = v___x_1042_;
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1043_);
                        crate::leanh::lean_dec(v___x_1042_);
                        v___x_1045_ = crate::leanh::lean_box(0);
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = crate::leanh::lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1064_ = (!crate::leanh::lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1042_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1057_);
                        crate::leanh::lean_dec(v___x_1042_);
                        v___x_1059_ = crate::leanh::lean_box(0);
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_1047_ = crate::leanh::lean_ctor_get(v_a_1043_, 0);
                crate::leanh::lean_inc_ref(v_structs_1047_);
                crate::leanh::lean_dec(v_a_1043_);
                v___x_1048_ = lean_array_get_size(v_structs_1047_);
                v___x_1049_ = lean_nat_dec_lt(v_a_1030_, v___x_1048_);
                if v___x_1049_ == 0 {
                    crate::leanh::lean_dec_ref(v_structs_1047_);
                    crate::leanh::lean_del_object(v___x_1045_);
                    v___x_1050_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1,
                    );
                    v___x_1051_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_1050_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
                    return v___x_1051_;
                } else {
                    v___x_1052_ = lean_array_fget(v_structs_1047_, v_a_1030_);
                    crate::leanh::lean_dec_ref(v_structs_1047_);
                    if v_isShared_1046_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1045_, 0, v___x_1052_);
                        v___x_1054_ = v___x_1045_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
                        v___x_1054_ = v_reuseFailAlloc_1055_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1054_;
            }
            3 => {
                if v_isShared_1060_ == 0 {
                    v___x_1062_ = v___x_1059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
        v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_,
        v_a_1073_, v_a_1074_, v_a_1075_,
    );
    crate::leanh::lean_dec(v_a_1075_);
    crate::leanh::lean_dec_ref(v_a_1074_);
    crate::leanh::lean_dec(v_a_1073_);
    crate::leanh::lean_dec_ref(v_a_1072_);
    crate::leanh::lean_dec(v_a_1071_);
    crate::leanh::lean_dec_ref(v_a_1070_);
    crate::leanh::lean_dec(v_a_1069_);
    crate::leanh::lean_dec_ref(v_a_1068_);
    crate::leanh::lean_dec(v_a_1067_);
    crate::leanh::lean_dec(v_a_1066_);
    crate::leanh::lean_dec(v_a_1065_);
    return v_res_1077_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(
    mut v_00_u03b1_1078_: *mut crate::leanh::LeanObject,
    mut v_msg_1079_: *mut crate::leanh::LeanObject,
    mut v___y_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
            v_msg_1079_,
            v___y_1087_,
            v___y_1088_,
            v___y_1089_,
            v___y_1090_,
        );
    return v___x_1092_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(
    mut v_00_u03b1_1093_: *mut crate::leanh::LeanObject,
    mut v_msg_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(
        v_00_u03b1_1093_,
        v_msg_1094_,
        v___y_1095_,
        v___y_1096_,
        v___y_1097_,
        v___y_1098_,
        v___y_1099_,
        v___y_1100_,
        v___y_1101_,
        v___y_1102_,
        v___y_1103_,
        v___y_1104_,
        v___y_1105_,
    );
    crate::leanh::lean_dec(v___y_1105_);
    crate::leanh::lean_dec_ref(v___y_1104_);
    crate::leanh::lean_dec(v___y_1103_);
    crate::leanh::lean_dec_ref(v___y_1102_);
    crate::leanh::lean_dec(v___y_1101_);
    crate::leanh::lean_dec_ref(v___y_1100_);
    crate::leanh::lean_dec(v___y_1099_);
    crate::leanh::lean_dec_ref(v___y_1098_);
    crate::leanh::lean_dec(v___y_1097_);
    crate::leanh::lean_dec(v___y_1096_);
    crate::leanh::lean_dec(v___y_1095_);
    return v_res_1107_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(
    mut v_ringId_x3f_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1131_: u8 = 0;
    let mut v_toRing_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_ringId_x3f_1109_) == 1 {
                    v_val_1121_ = crate::leanh::lean_ctor_get(v_ringId_x3f_1109_, 0);
                    v_isSharedCheck_1148_ =
                        (!crate::leanh::lean_is_exclusive(v_ringId_x3f_1109_)) as u8;
                    if v_isSharedCheck_1148_ == 0 {
                        v___x_1123_ = v_ringId_x3f_1109_;
                        v_isShared_1124_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1121_);
                        crate::leanh::lean_dec(v_ringId_x3f_1109_);
                        v___x_1123_ = crate::leanh::lean_box(0);
                        v_isShared_1124_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ringId_x3f_1109_);
                    v___x_1149_ = crate::leanh::lean_box(0);
                    v___x_1150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1149_);
                    return v___x_1150_;
                }
            }
            1 => {
                v___x_1125_ = 0;
                v___x_1126_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1126_, 0, v_val_1121_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1126_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1125_,
                );
                v___x_1127_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___x_1126_,
                    v_a_1110_,
                    v_a_1111_,
                    v_a_1112_,
                    v_a_1113_,
                    v_a_1114_,
                    v_a_1115_,
                    v_a_1116_,
                    v_a_1117_,
                    v_a_1118_,
                    v_a_1119_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1126_, 1);
                if crate::leanh::lean_obj_tag(v___x_1127_) == 0 {
                    v_a_1128_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1139_ = (!crate::leanh::lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1139_ == 0 {
                        v___x_1130_ = v___x_1127_;
                        v_isShared_1131_ = v_isSharedCheck_1139_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1128_);
                        crate::leanh::lean_dec(v___x_1127_);
                        v___x_1130_ = crate::leanh::lean_box(0);
                        v_isShared_1131_ = v_isSharedCheck_1139_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1123_);
                    v_a_1140_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1147_ = (!crate::leanh::lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1142_ = v___x_1127_;
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1140_);
                        crate::leanh::lean_dec(v___x_1127_);
                        v___x_1142_ = crate::leanh::lean_box(0);
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_toRing_1132_ = crate::leanh::lean_ctor_get(v_a_1128_, 0);
                crate::leanh::lean_inc_ref(v_toRing_1132_);
                crate::leanh::lean_dec(v_a_1128_);
                if v_isShared_1124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1123_, 0, v_toRing_1132_);
                    v___x_1134_ = v___x_1123_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_toRing_1132_);
                    v___x_1134_ = v_reuseFailAlloc_1138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1131_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1130_, 0, v___x_1134_);
                    v___x_1136_ = v___x_1130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1136_;
            }
            5 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(
    mut v_ringId_x3f_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(
        v_ringId_x3f_1151_,
        v_a_1152_,
        v_a_1153_,
        v_a_1154_,
        v_a_1155_,
        v_a_1156_,
        v_a_1157_,
        v_a_1158_,
        v_a_1159_,
        v_a_1160_,
        v_a_1161_,
    );
    crate::leanh::lean_dec(v_a_1161_);
    crate::leanh::lean_dec_ref(v_a_1160_);
    crate::leanh::lean_dec(v_a_1159_);
    crate::leanh::lean_dec_ref(v_a_1158_);
    crate::leanh::lean_dec(v_a_1157_);
    crate::leanh::lean_dec_ref(v_a_1156_);
    crate::leanh::lean_dec(v_a_1155_);
    crate::leanh::lean_dec_ref(v_a_1154_);
    crate::leanh::lean_dec(v_a_1153_);
    crate::leanh::lean_dec(v_a_1152_);
    return v_res_1163_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0;
    v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1,
    );
    v___x_1173_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
            v___x_1172_,
            v_a_1167_,
            v_a_1168_,
            v_a_1169_,
            v_a_1170_,
        );
    return v___x_1173_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_a_1175_: *mut crate::leanh::LeanObject,
    mut v_a_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_a_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
        v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_,
    );
    crate::leanh::lean_dec(v_a_1177_);
    crate::leanh::lean_dec_ref(v_a_1176_);
    crate::leanh::lean_dec(v_a_1175_);
    crate::leanh::lean_dec_ref(v_a_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing(
    mut v_00_u03b1_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
        v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_,
    );
    return v___x_1193_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(
    mut v_00_u03b1_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
    mut v_a_1204_: *mut crate::leanh::LeanObject,
    mut v_a_1205_: *mut crate::leanh::LeanObject,
    mut v_a_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(
        v_00_u03b1_1194_,
        v_a_1195_,
        v_a_1196_,
        v_a_1197_,
        v_a_1198_,
        v_a_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
        v_a_1203_,
        v_a_1204_,
        v_a_1205_,
    );
    crate::leanh::lean_dec(v_a_1205_);
    crate::leanh::lean_dec_ref(v_a_1204_);
    crate::leanh::lean_dec(v_a_1203_);
    crate::leanh::lean_dec_ref(v_a_1202_);
    crate::leanh::lean_dec(v_a_1201_);
    crate::leanh::lean_dec_ref(v_a_1200_);
    crate::leanh::lean_dec(v_a_1199_);
    crate::leanh::lean_dec_ref(v_a_1198_);
    crate::leanh::lean_dec(v_a_1197_);
    crate::leanh::lean_dec(v_a_1196_);
    crate::leanh::lean_dec(v_a_1195_);
    return v_res_1207_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0;
    v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
    return v___x_1210_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
    mut v_a_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_a_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1,
    );
    v___x_1217_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
            v___x_1216_,
            v_a_1211_,
            v_a_1212_,
            v_a_1213_,
            v_a_1214_,
        );
    return v___x_1217_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(
    mut v_a_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
        v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_,
    );
    crate::leanh::lean_dec(v_a_1221_);
    crate::leanh::lean_dec_ref(v_a_1220_);
    crate::leanh::lean_dec(v_a_1219_);
    crate::leanh::lean_dec_ref(v_a_1218_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(
    mut v_00_u03b1_1224_: *mut crate::leanh::LeanObject,
    mut v_a_1225_: *mut crate::leanh::LeanObject,
    mut v_a_1226_: *mut crate::leanh::LeanObject,
    mut v_a_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
        v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_,
    );
    return v___x_1237_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(
    mut v_00_u03b1_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
    mut v_a_1243_: *mut crate::leanh::LeanObject,
    mut v_a_1244_: *mut crate::leanh::LeanObject,
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(
        v_00_u03b1_1238_,
        v_a_1239_,
        v_a_1240_,
        v_a_1241_,
        v_a_1242_,
        v_a_1243_,
        v_a_1244_,
        v_a_1245_,
        v_a_1246_,
        v_a_1247_,
        v_a_1248_,
        v_a_1249_,
    );
    crate::leanh::lean_dec(v_a_1249_);
    crate::leanh::lean_dec_ref(v_a_1248_);
    crate::leanh::lean_dec(v_a_1247_);
    crate::leanh::lean_dec_ref(v_a_1246_);
    crate::leanh::lean_dec(v_a_1245_);
    crate::leanh::lean_dec_ref(v_a_1244_);
    crate::leanh::lean_dec(v_a_1243_);
    crate::leanh::lean_dec_ref(v_a_1242_);
    crate::leanh::lean_dec(v_a_1241_);
    crate::leanh::lean_dec(v_a_1240_);
    crate::leanh::lean_dec(v_a_1239_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
    mut v_a_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_,
                    v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_,
                );
                if crate::leanh::lean_obj_tag(v___x_1264_) == 0 {
                    v_a_1265_ = crate::leanh::lean_ctor_get(v___x_1264_, 0);
                    crate::leanh::lean_inc(v_a_1265_);
                    crate::leanh::lean_dec_ref_known(v___x_1264_, 1);
                    v_ringId_x3f_1266_ = crate::leanh::lean_ctor_get(v_a_1265_, 1);
                    crate::leanh::lean_inc(v_ringId_x3f_1266_);
                    crate::leanh::lean_dec(v_a_1265_);
                    v___x_1267_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(
                        v_ringId_x3f_1266_,
                        v_a_1253_,
                        v_a_1254_,
                        v_a_1255_,
                        v_a_1256_,
                        v_a_1257_,
                        v_a_1258_,
                        v_a_1259_,
                        v_a_1260_,
                        v_a_1261_,
                        v_a_1262_,
                    );
                    return v___x_1267_;
                } else {
                    v_a_1268_ = crate::leanh::lean_ctor_get(v___x_1264_, 0);
                    v_isSharedCheck_1275_ = (!crate::leanh::lean_is_exclusive(v___x_1264_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1270_ = v___x_1264_;
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1268_);
                        crate::leanh::lean_dec(v___x_1264_);
                        v___x_1270_ = crate::leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1271_ == 0 {
                    v___x_1273_ = v___x_1270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(
    mut v_a_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
    mut v_a_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1288_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
        v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_,
        v_a_1284_, v_a_1285_, v_a_1286_,
    );
    crate::leanh::lean_dec(v_a_1286_);
    crate::leanh::lean_dec_ref(v_a_1285_);
    crate::leanh::lean_dec(v_a_1284_);
    crate::leanh::lean_dec_ref(v_a_1283_);
    crate::leanh::lean_dec(v_a_1282_);
    crate::leanh::lean_dec_ref(v_a_1281_);
    crate::leanh::lean_dec(v_a_1280_);
    crate::leanh::lean_dec_ref(v_a_1279_);
    crate::leanh::lean_dec(v_a_1278_);
    crate::leanh::lean_dec(v_a_1277_);
    crate::leanh::lean_dec(v_a_1276_);
    return v_res_1288_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(
    mut v_e_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_Meta_Sym_canon(
        v_e_1289_,
        v___y_1295_,
        v___y_1296_,
        v___y_1297_,
        v___y_1298_,
        v___y_1299_,
        v___y_1300_,
    );
    if crate::leanh::lean_obj_tag(v___x_1302_) == 0 {
        let mut v_a_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1303_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
        crate::leanh::lean_inc(v_a_1303_);
        crate::leanh::lean_dec_ref_known(v___x_1302_, 1);
        v___x_1304_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1303_, v___y_1296_);
        return v___x_1304_;
    } else {
        return v___x_1302_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(
    mut v_e_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1318_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(
        v_e_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
    );
    crate::leanh::lean_dec(v___y_1316_);
    crate::leanh::lean_dec_ref(v___y_1315_);
    crate::leanh::lean_dec(v___y_1314_);
    crate::leanh::lean_dec_ref(v___y_1313_);
    crate::leanh::lean_dec(v___y_1312_);
    crate::leanh::lean_dec_ref(v___y_1311_);
    crate::leanh::lean_dec(v___y_1310_);
    crate::leanh::lean_dec_ref(v___y_1309_);
    crate::leanh::lean_dec(v___y_1308_);
    crate::leanh::lean_dec(v___y_1307_);
    crate::leanh::lean_dec(v___y_1306_);
    return v_res_1318_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(
    mut v_e_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_e_1319_,
        v___y_1327_,
        v___y_1328_,
        v___y_1329_,
        v___y_1330_,
    );
    return v___x_1332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(
    mut v_e_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(
        v_e_1333_,
        v___y_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
        v___y_1338_,
        v___y_1339_,
        v___y_1340_,
        v___y_1341_,
        v___y_1342_,
        v___y_1343_,
        v___y_1344_,
    );
    crate::leanh::lean_dec(v___y_1344_);
    crate::leanh::lean_dec_ref(v___y_1343_);
    crate::leanh::lean_dec(v___y_1342_);
    crate::leanh::lean_dec_ref(v___y_1341_);
    crate::leanh::lean_dec(v___y_1340_);
    crate::leanh::lean_dec_ref(v___y_1339_);
    crate::leanh::lean_dec(v___y_1338_);
    crate::leanh::lean_dec_ref(v___y_1337_);
    crate::leanh::lean_dec(v___y_1336_);
    crate::leanh::lean_dec(v___y_1335_);
    crate::leanh::lean_dec(v___y_1334_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v_val_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut v_a_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1365_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
                    v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_,
                    v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                );
                if crate::leanh::lean_obj_tag(v___x_1365_) == 0 {
                    v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1375_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1366_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1368_ = crate::leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1376_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1383_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1383_ == 0 {
                        v___x_1378_ = v___x_1365_;
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1376_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1378_ = crate::leanh::lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1366_) == 1 {
                    v_val_1370_ = crate::leanh::lean_ctor_get(v_a_1366_, 0);
                    crate::leanh::lean_inc(v_val_1370_);
                    crate::leanh::lean_dec_ref_known(v_a_1366_, 1);
                    if v_isShared_1369_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1368_, 0, v_val_1370_);
                        v___x_1372_ = v___x_1368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_val_1370_);
                        v___x_1372_ = v_reuseFailAlloc_1373_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1368_);
                    crate::leanh::lean_dec(v_a_1366_);
                    v___x_1374_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                        v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                    );
                    return v___x_1374_;
                }
            }
            2 => {
                return v___x_1372_;
            }
            3 => {
                if v_isShared_1379_ == 0 {
                    v___x_1381_ = v___x_1378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
                    v___x_1381_ = v_reuseFailAlloc_1382_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
        v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_,
        v_a_1392_, v_a_1393_, v_a_1394_,
    );
    crate::leanh::lean_dec(v_a_1394_);
    crate::leanh::lean_dec_ref(v_a_1393_);
    crate::leanh::lean_dec(v_a_1392_);
    crate::leanh::lean_dec_ref(v_a_1391_);
    crate::leanh::lean_dec(v_a_1390_);
    crate::leanh::lean_dec_ref(v_a_1389_);
    crate::leanh::lean_dec(v_a_1388_);
    crate::leanh::lean_dec_ref(v_a_1387_);
    crate::leanh::lean_dec(v_a_1386_);
    crate::leanh::lean_dec(v_a_1385_);
    crate::leanh::lean_dec(v_a_1384_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(
    mut v_f_1397_: *mut crate::leanh::LeanObject,
    mut v_s_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_1413_: u8 = 0;
    let mut v_invSet_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_1417_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_1399_ = crate::leanh::lean_ctor_get(v_s_1398_, 0);
                v_invFn_x3f_1400_ = crate::leanh::lean_ctor_get(v_s_1398_, 1);
                v_semiringId_x3f_1401_ = crate::leanh::lean_ctor_get(v_s_1398_, 2);
                v_commSemiringInst_1402_ = crate::leanh::lean_ctor_get(v_s_1398_, 3);
                v_commRingInst_1403_ = crate::leanh::lean_ctor_get(v_s_1398_, 4);
                v_noZeroDivInst_x3f_1404_ = crate::leanh::lean_ctor_get(v_s_1398_, 5);
                v_fieldInst_x3f_1405_ = crate::leanh::lean_ctor_get(v_s_1398_, 6);
                v_powIdentityInst_x3f_1406_ = crate::leanh::lean_ctor_get(v_s_1398_, 7);
                v_denoteEntries_1407_ = crate::leanh::lean_ctor_get(v_s_1398_, 8);
                v_nextId_1408_ = crate::leanh::lean_ctor_get(v_s_1398_, 9);
                v_steps_1409_ = crate::leanh::lean_ctor_get(v_s_1398_, 10);
                v_queue_1410_ = crate::leanh::lean_ctor_get(v_s_1398_, 11);
                v_basis_1411_ = crate::leanh::lean_ctor_get(v_s_1398_, 12);
                v_diseqs_1412_ = crate::leanh::lean_ctor_get(v_s_1398_, 13);
                v_recheck_1413_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1398_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_1414_ = crate::leanh::lean_ctor_get(v_s_1398_, 14);
                v_powIdentityVarCount_1415_ = crate::leanh::lean_ctor_get(v_s_1398_, 15);
                v_numEq0_x3f_1416_ = crate::leanh::lean_ctor_get(v_s_1398_, 16);
                v_numEq0Updated_1417_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1398_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_1425_ = (!crate::leanh::lean_is_exclusive(v_s_1398_)) as u8;
                if v_isSharedCheck_1425_ == 0 {
                    v___x_1419_ = v_s_1398_;
                    v_isShared_1420_ = v_isSharedCheck_1425_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_1416_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_1415_);
                    crate::leanh::lean_inc(v_invSet_1414_);
                    crate::leanh::lean_inc(v_diseqs_1412_);
                    crate::leanh::lean_inc(v_basis_1411_);
                    crate::leanh::lean_inc(v_queue_1410_);
                    crate::leanh::lean_inc(v_steps_1409_);
                    crate::leanh::lean_inc(v_nextId_1408_);
                    crate::leanh::lean_inc(v_denoteEntries_1407_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_1406_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_1405_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_1404_);
                    crate::leanh::lean_inc(v_commRingInst_1403_);
                    crate::leanh::lean_inc(v_commSemiringInst_1402_);
                    crate::leanh::lean_inc(v_semiringId_x3f_1401_);
                    crate::leanh::lean_inc(v_invFn_x3f_1400_);
                    crate::leanh::lean_inc(v_toRing_1399_);
                    crate::leanh::lean_dec(v_s_1398_);
                    v___x_1419_ = crate::leanh::lean_box(0);
                    v_isShared_1420_ = v_isSharedCheck_1425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1421_ = crate::leanh::lean_apply_1(v_f_1397_, v_toRing_1399_);
                if v_isShared_1420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1419_, 0, v___x_1421_);
                    v___x_1423_ = v___x_1419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_invFn_x3f_1400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_semiringId_x3f_1401_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1424_,
                        3,
                        v_commSemiringInst_1402_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_commRingInst_1403_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1424_,
                        5,
                        v_noZeroDivInst_x3f_1404_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 6, v_fieldInst_x3f_1405_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1424_,
                        7,
                        v_powIdentityInst_x3f_1406_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 8, v_denoteEntries_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 9, v_nextId_1408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 10, v_steps_1409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 11, v_queue_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 12, v_basis_1411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 13, v_diseqs_1412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 14, v_invSet_1414_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1424_,
                        15,
                        v_powIdentityVarCount_1415_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 16, v_numEq0_x3f_1416_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1424_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_1413_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1424_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_1417_,
                    );
                    v___x_1423_ = v_reuseFailAlloc_1424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(
    mut v_f_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1439_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v___y_1427_,
                    v___y_1428_,
                    v___y_1429_,
                    v___y_1430_,
                    v___y_1431_,
                    v___y_1432_,
                    v___y_1433_,
                    v___y_1434_,
                    v___y_1435_,
                    v___y_1436_,
                    v___y_1437_,
                );
                if crate::leanh::lean_obj_tag(v___x_1439_) == 0 {
                    v_a_1440_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    crate::leanh::lean_inc(v_a_1440_);
                    crate::leanh::lean_dec_ref_known(v___x_1439_, 1);
                    v_ringId_x3f_1441_ = crate::leanh::lean_ctor_get(v_a_1440_, 1);
                    crate::leanh::lean_inc(v_ringId_x3f_1441_);
                    crate::leanh::lean_dec(v_a_1440_);
                    if crate::leanh::lean_obj_tag(v_ringId_x3f_1441_) == 1 {
                        v_val_1442_ = crate::leanh::lean_ctor_get(v_ringId_x3f_1441_, 0);
                        crate::leanh::lean_inc(v_val_1442_);
                        crate::leanh::lean_dec_ref_known(v_ringId_x3f_1441_, 1);
                        v___f_1443_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_1443_, 0, v_f_1426_);
                        v___x_1444_ = 0;
                        v___x_1445_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1445_, 0, v_val_1442_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1445_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1444_,
                        );
                        v___x_1446_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_1443_,
                                v___x_1445_,
                                v___y_1428_,
                            );
                        crate::leanh::lean_dec_ref_known(v___x_1445_, 1);
                        return v___x_1446_;
                    } else {
                        crate::leanh::lean_dec(v_ringId_x3f_1441_);
                        crate::leanh::lean_dec_ref(v_f_1426_);
                        v___x_1447_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                            v___y_1434_,
                            v___y_1435_,
                            v___y_1436_,
                            v___y_1437_,
                        );
                        return v___x_1447_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1426_);
                    v_a_1448_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1455_ = (!crate::leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v___x_1450_ = v___x_1439_;
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1448_);
                        crate::leanh::lean_dec(v___x_1439_);
                        v___x_1450_ = crate::leanh::lean_box(0);
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1451_ == 0 {
                    v___x_1453_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(
    mut v_f_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1469_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(
        v_f_1456_,
        v___y_1457_,
        v___y_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
        v___y_1464_,
        v___y_1465_,
        v___y_1466_,
        v___y_1467_,
    );
    crate::leanh::lean_dec(v___y_1467_);
    crate::leanh::lean_dec_ref(v___y_1466_);
    crate::leanh::lean_dec(v___y_1465_);
    crate::leanh::lean_dec_ref(v___y_1464_);
    crate::leanh::lean_dec(v___y_1463_);
    crate::leanh::lean_dec_ref(v___y_1462_);
    crate::leanh::lean_dec(v___y_1461_);
    crate::leanh::lean_dec_ref(v___y_1460_);
    crate::leanh::lean_dec(v___y_1459_);
    crate::leanh::lean_dec(v___y_1458_);
    crate::leanh::lean_dec(v___y_1457_);
    return v_res_1469_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1471_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0;
    v___x_1472_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
    crate::leanh::lean_ctor_set(v___x_1473_, 1, v___f_1471_);
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1,
    );
    return v___x_1474_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
    mut v_x_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1488_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_,
                    v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_,
                );
                if crate::leanh::lean_obj_tag(v___x_1488_) == 0 {
                    v_a_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                    crate::leanh::lean_inc(v_a_1489_);
                    crate::leanh::lean_dec_ref_known(v___x_1488_, 1);
                    v_ringId_x3f_1490_ = crate::leanh::lean_ctor_get(v_a_1489_, 1);
                    crate::leanh::lean_inc(v_ringId_x3f_1490_);
                    crate::leanh::lean_dec(v_a_1489_);
                    if crate::leanh::lean_obj_tag(v_ringId_x3f_1490_) == 1 {
                        v_val_1491_ = crate::leanh::lean_ctor_get(v_ringId_x3f_1490_, 0);
                        crate::leanh::lean_inc(v_val_1491_);
                        crate::leanh::lean_dec_ref_known(v_ringId_x3f_1490_, 1);
                        v___x_1492_ = 0;
                        v___x_1493_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1493_, 0, v_val_1491_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1493_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1492_,
                        );
                        crate::leanh::lean_inc(v_a_1486_);
                        crate::leanh::lean_inc_ref(v_a_1485_);
                        crate::leanh::lean_inc(v_a_1484_);
                        crate::leanh::lean_inc_ref(v_a_1483_);
                        crate::leanh::lean_inc(v_a_1482_);
                        crate::leanh::lean_inc_ref(v_a_1481_);
                        crate::leanh::lean_inc(v_a_1480_);
                        crate::leanh::lean_inc_ref(v_a_1479_);
                        crate::leanh::lean_inc(v_a_1478_);
                        crate::leanh::lean_inc(v_a_1477_);
                        v___x_1494_ = crate::leanh::lean_apply_12(
                            v_x_1475_,
                            v___x_1493_,
                            v_a_1477_,
                            v_a_1478_,
                            v_a_1479_,
                            v_a_1480_,
                            v_a_1481_,
                            v_a_1482_,
                            v_a_1483_,
                            v_a_1484_,
                            v_a_1485_,
                            v_a_1486_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_1494_;
                    } else {
                        crate::leanh::lean_dec(v_ringId_x3f_1490_);
                        crate::leanh::lean_dec_ref(v_x_1475_);
                        v___x_1495_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                            v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_,
                        );
                        return v___x_1495_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1475_);
                    v_a_1496_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                    v_isSharedCheck_1503_ = (!crate::leanh::lean_is_exclusive(v___x_1488_)) as u8;
                    if v_isSharedCheck_1503_ == 0 {
                        v___x_1498_ = v___x_1488_;
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1496_);
                        crate::leanh::lean_dec(v___x_1488_);
                        v___x_1498_ = crate::leanh::lean_box(0);
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1499_ == 0 {
                    v___x_1501_ = v___x_1498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(
    mut v_x_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
        v_x_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_,
        v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_,
    );
    crate::leanh::lean_dec(v_a_1515_);
    crate::leanh::lean_dec_ref(v_a_1514_);
    crate::leanh::lean_dec(v_a_1513_);
    crate::leanh::lean_dec_ref(v_a_1512_);
    crate::leanh::lean_dec(v_a_1511_);
    crate::leanh::lean_dec_ref(v_a_1510_);
    crate::leanh::lean_dec(v_a_1509_);
    crate::leanh::lean_dec_ref(v_a_1508_);
    crate::leanh::lean_dec(v_a_1507_);
    crate::leanh::lean_dec(v_a_1506_);
    crate::leanh::lean_dec(v_a_1505_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM(
    mut v_00_u03b1_1518_: *mut crate::leanh::LeanObject,
    mut v_x_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
    mut v_a_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
    mut v_a_1524_: *mut crate::leanh::LeanObject,
    mut v_a_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
        v_x_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_,
        v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_,
    );
    return v___x_1532_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(
    mut v_00_u03b1_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(
        v_00_u03b1_1533_,
        v_x_1534_,
        v_a_1535_,
        v_a_1536_,
        v_a_1537_,
        v_a_1538_,
        v_a_1539_,
        v_a_1540_,
        v_a_1541_,
        v_a_1542_,
        v_a_1543_,
        v_a_1544_,
        v_a_1545_,
    );
    crate::leanh::lean_dec(v_a_1545_);
    crate::leanh::lean_dec_ref(v_a_1544_);
    crate::leanh::lean_dec(v_a_1543_);
    crate::leanh::lean_dec_ref(v_a_1542_);
    crate::leanh::lean_dec(v_a_1541_);
    crate::leanh::lean_dec_ref(v_a_1540_);
    crate::leanh::lean_dec(v_a_1539_);
    crate::leanh::lean_dec_ref(v_a_1538_);
    crate::leanh::lean_dec(v_a_1537_);
    crate::leanh::lean_dec(v_a_1536_);
    crate::leanh::lean_dec(v_a_1535_);
    return v_res_1547_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_f_1549_: *mut crate::leanh::LeanObject,
    mut v_s_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v_v_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1551_ = crate::leanh::lean_ctor_get(v_s_1550_, 0);
                v_typeIdOf_1552_ = crate::leanh::lean_ctor_get(v_s_1550_, 1);
                v_exprToStructId_1553_ = crate::leanh::lean_ctor_get(v_s_1550_, 2);
                v_exprToStructIdEntries_1554_ = crate::leanh::lean_ctor_get(v_s_1550_, 3);
                v_forbiddenNatModules_1555_ = crate::leanh::lean_ctor_get(v_s_1550_, 4);
                v_natStructs_1556_ = crate::leanh::lean_ctor_get(v_s_1550_, 5);
                v_natTypeIdOf_1557_ = crate::leanh::lean_ctor_get(v_s_1550_, 6);
                v_exprToNatStructId_1558_ = crate::leanh::lean_ctor_get(v_s_1550_, 7);
                v___x_1559_ = lean_array_get_size(v_structs_1551_);
                v___x_1560_ = lean_nat_dec_lt(v_a_1548_, v___x_1559_);
                if v___x_1560_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1549_);
                    return v_s_1550_;
                } else {
                    crate::leanh::lean_inc_ref(v_exprToNatStructId_1558_);
                    crate::leanh::lean_inc_ref(v_natTypeIdOf_1557_);
                    crate::leanh::lean_inc_ref(v_natStructs_1556_);
                    crate::leanh::lean_inc_ref(v_forbiddenNatModules_1555_);
                    crate::leanh::lean_inc_ref(v_exprToStructIdEntries_1554_);
                    crate::leanh::lean_inc_ref(v_exprToStructId_1553_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_1552_);
                    crate::leanh::lean_inc_ref(v_structs_1551_);
                    v_isSharedCheck_1572_ = (!crate::leanh::lean_is_exclusive(v_s_1550_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v_unused_1573_ = crate::leanh::lean_ctor_get(v_s_1550_, 7);
                        crate::leanh::lean_dec(v_unused_1573_);
                        v_unused_1574_ = crate::leanh::lean_ctor_get(v_s_1550_, 6);
                        crate::leanh::lean_dec(v_unused_1574_);
                        v_unused_1575_ = crate::leanh::lean_ctor_get(v_s_1550_, 5);
                        crate::leanh::lean_dec(v_unused_1575_);
                        v_unused_1576_ = crate::leanh::lean_ctor_get(v_s_1550_, 4);
                        crate::leanh::lean_dec(v_unused_1576_);
                        v_unused_1577_ = crate::leanh::lean_ctor_get(v_s_1550_, 3);
                        crate::leanh::lean_dec(v_unused_1577_);
                        v_unused_1578_ = crate::leanh::lean_ctor_get(v_s_1550_, 2);
                        crate::leanh::lean_dec(v_unused_1578_);
                        v_unused_1579_ = crate::leanh::lean_ctor_get(v_s_1550_, 1);
                        crate::leanh::lean_dec(v_unused_1579_);
                        v_unused_1580_ = crate::leanh::lean_ctor_get(v_s_1550_, 0);
                        crate::leanh::lean_dec(v_unused_1580_);
                        v___x_1562_ = v_s_1550_;
                        v_isShared_1563_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_1550_);
                        v___x_1562_ = crate::leanh::lean_box(0);
                        v_isShared_1563_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1564_ = lean_array_fget(v_structs_1551_, v_a_1548_);
                v___x_1565_ = crate::leanh::lean_box(0);
                v_xs_x27_1566_ = lean_array_fset(v_structs_1551_, v_a_1548_, v___x_1565_);
                v___x_1567_ = crate::leanh::lean_apply_1(v_f_1549_, v_v_1564_);
                v___x_1568_ = lean_array_fset(v_xs_x27_1566_, v_a_1548_, v___x_1567_);
                if v_isShared_1563_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1568_);
                    v___x_1570_ = v___x_1562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_typeIdOf_1552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_exprToStructId_1553_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1571_,
                        3,
                        v_exprToStructIdEntries_1554_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1571_,
                        4,
                        v_forbiddenNatModules_1555_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 5, v_natStructs_1556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 6, v_natTypeIdOf_1557_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1571_,
                        7,
                        v_exprToNatStructId_1558_,
                    );
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_f_1582_: *mut crate::leanh::LeanObject,
    mut v_s_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(
        v_a_1581_, v_f_1582_, v_s_1583_,
    );
    crate::leanh::lean_dec(v_a_1581_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(
    mut v_f_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
    mut v_a_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1586_);
    v___f_1589_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1589_, 0, v_a_1586_);
    crate::leanh::lean_closure_set(v___f_1589_, 1, v_f_1585_);
    v___x_1590_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_1591_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1590_, v___f_1589_, v_a_1587_);
    return v___x_1591_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(
    mut v_f_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ =
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1592_, v_a_1593_, v_a_1594_);
    crate::leanh::lean_dec(v_a_1594_);
    crate::leanh::lean_dec(v_a_1593_);
    return v_res_1596_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct(
    mut v_f_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
    mut v_a_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
    mut v_a_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1598_);
    v___f_1610_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1610_, 0, v_a_1598_);
    crate::leanh::lean_closure_set(v___f_1610_, 1, v_f_1597_);
    v___x_1611_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_1612_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1611_, v___f_1610_, v_a_1599_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(
    mut v_f_1613_: *mut crate::leanh::LeanObject,
    mut v_a_1614_: *mut crate::leanh::LeanObject,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
    mut v_a_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(
        v_f_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_,
        v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_,
    );
    crate::leanh::lean_dec(v_a_1624_);
    crate::leanh::lean_dec_ref(v_a_1623_);
    crate::leanh::lean_dec(v_a_1622_);
    crate::leanh::lean_dec_ref(v_a_1621_);
    crate::leanh::lean_dec(v_a_1620_);
    crate::leanh::lean_dec_ref(v_a_1619_);
    crate::leanh::lean_dec(v_a_1618_);
    crate::leanh::lean_dec_ref(v_a_1617_);
    crate::leanh::lean_dec(v_a_1616_);
    crate::leanh::lean_dec(v_a_1615_);
    crate::leanh::lean_dec(v_a_1614_);
    return v_res_1626_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM =
        _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
}
