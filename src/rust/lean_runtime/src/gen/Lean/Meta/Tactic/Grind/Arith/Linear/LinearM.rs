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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
};
pub static l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value: LeanStringObject<
    45,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed as *const core::ffi::c_void,
        m_arity: 12,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value:
    LeanStringObject<57> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value:
    LeanStringObject<69> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_818_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_817_, v_a_814_, v_a_815_);
    return v___x_818_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(
    mut v_a_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_822_: *mut LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_819_, v_a_820_);
    lean_dec_ref(v_a_820_);
    lean_dec(v_a_819_);
    return v_res_822_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27(
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    v___x_834_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_823_, v_a_831_);
    return v___x_834_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(
    mut v_a_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
    mut v_a_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_846_: *mut LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(
        v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_,
        v_a_844_,
    );
    lean_dec(v_a_844_);
    lean_dec_ref(v_a_843_);
    lean_dec(v_a_842_);
    lean_dec_ref(v_a_841_);
    lean_dec(v_a_840_);
    lean_dec_ref(v_a_839_);
    lean_dec(v_a_838_);
    lean_dec_ref(v_a_837_);
    lean_dec(v_a_836_);
    lean_dec(v_a_835_);
    return v_res_846_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(
    mut v_f_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_851_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_850_, v_f_847_, v_a_848_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(
    mut v_f_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_855_: *mut LeanObject = core::ptr::null_mut();
    v_res_855_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_852_, v_a_853_);
    lean_dec(v_a_853_);
    return v_res_855_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27(
    mut v_f_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
    mut v_a_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_868_, v_f_856_, v_a_857_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(
    mut v_f_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
    mut v_a_873_: *mut LeanObject,
    mut v_a_874_: *mut LeanObject,
    mut v_a_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_882_: *mut LeanObject = core::ptr::null_mut();
    v_res_882_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(
        v_f_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_,
        v_a_879_, v_a_880_,
    );
    lean_dec(v_a_880_);
    lean_dec_ref(v_a_879_);
    lean_dec(v_a_878_);
    lean_dec_ref(v_a_877_);
    lean_dec(v_a_876_);
    lean_dec_ref(v_a_875_);
    lean_dec(v_a_874_);
    lean_dec_ref(v_a_873_);
    lean_dec(v_a_872_);
    lean_dec(v_a_871_);
    return v_res_882_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(
    mut v_inst_883_: *mut LeanObject,
    mut v_inst_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_885_ = lean_apply_2(v_inst_883_, lean_box(0), v_inst_884_);
    return v___x_885_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(
    mut v_m_886_: *mut LeanObject,
    mut v_n_887_: *mut LeanObject,
    mut v_inst_888_: *mut LeanObject,
    mut v_inst_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = lean_apply_2(v_inst_888_, lean_box(0), v_inst_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(
    mut v_structId_891_: *mut LeanObject,
    mut v_x_892_: *mut LeanObject,
    mut v_a_893_: *mut LeanObject,
    mut v_a_894_: *mut LeanObject,
    mut v_a_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_902_);
    lean_inc_ref(v_a_901_);
    lean_inc(v_a_900_);
    lean_inc_ref(v_a_899_);
    lean_inc(v_a_898_);
    lean_inc_ref(v_a_897_);
    lean_inc(v_a_896_);
    lean_inc_ref(v_a_895_);
    lean_inc(v_a_894_);
    lean_inc(v_a_893_);
    v___x_904_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_904_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(
    mut v_structId_905_: *mut LeanObject,
    mut v_x_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_a_910_: *mut LeanObject,
    mut v_a_911_: *mut LeanObject,
    mut v_a_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_918_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_916_);
    lean_dec_ref(v_a_915_);
    lean_dec(v_a_914_);
    lean_dec_ref(v_a_913_);
    lean_dec(v_a_912_);
    lean_dec_ref(v_a_911_);
    lean_dec(v_a_910_);
    lean_dec_ref(v_a_909_);
    lean_dec(v_a_908_);
    lean_dec(v_a_907_);
    return v_res_918_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run(
    mut v_00_u03b1_919_: *mut LeanObject,
    mut v_structId_920_: *mut LeanObject,
    mut v_x_921_: *mut LeanObject,
    mut v_a_922_: *mut LeanObject,
    mut v_a_923_: *mut LeanObject,
    mut v_a_924_: *mut LeanObject,
    mut v_a_925_: *mut LeanObject,
    mut v_a_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_a_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_931_);
    lean_inc_ref(v_a_930_);
    lean_inc(v_a_929_);
    lean_inc_ref(v_a_928_);
    lean_inc(v_a_927_);
    lean_inc_ref(v_a_926_);
    lean_inc(v_a_925_);
    lean_inc_ref(v_a_924_);
    lean_inc(v_a_923_);
    lean_inc(v_a_922_);
    v___x_933_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_933_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(
    mut v_00_u03b1_934_: *mut LeanObject,
    mut v_structId_935_: *mut LeanObject,
    mut v_x_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
    mut v_a_938_: *mut LeanObject,
    mut v_a_939_: *mut LeanObject,
    mut v_a_940_: *mut LeanObject,
    mut v_a_941_: *mut LeanObject,
    mut v_a_942_: *mut LeanObject,
    mut v_a_943_: *mut LeanObject,
    mut v_a_944_: *mut LeanObject,
    mut v_a_945_: *mut LeanObject,
    mut v_a_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_948_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_946_);
    lean_dec_ref(v_a_945_);
    lean_dec(v_a_944_);
    lean_dec_ref(v_a_943_);
    lean_dec(v_a_942_);
    lean_dec_ref(v_a_941_);
    lean_dec(v_a_940_);
    lean_dec_ref(v_a_939_);
    lean_dec(v_a_938_);
    lean_dec(v_a_937_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(
    mut v_a_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_949_);
    v___x_951_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_951_, 0, v_a_949_);
    return v___x_951_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_954_: *mut LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_952_);
    lean_dec(v_a_952_);
    return v_res_954_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId(
    mut v_a_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
    mut v_a_957_: *mut LeanObject,
    mut v_a_958_: *mut LeanObject,
    mut v_a_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
    mut v_a_961_: *mut LeanObject,
    mut v_a_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
    mut v_a_964_: *mut LeanObject,
    mut v_a_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_955_);
    v___x_967_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_967_, 0, v_a_955_);
    return v___x_967_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(
    mut v_a_968_: *mut LeanObject,
    mut v_a_969_: *mut LeanObject,
    mut v_a_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
    mut v_a_973_: *mut LeanObject,
    mut v_a_974_: *mut LeanObject,
    mut v_a_975_: *mut LeanObject,
    mut v_a_976_: *mut LeanObject,
    mut v_a_977_: *mut LeanObject,
    mut v_a_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_980_: *mut LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(
        v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_,
        v_a_977_, v_a_978_,
    );
    lean_dec(v_a_978_);
    lean_dec_ref(v_a_977_);
    lean_dec(v_a_976_);
    lean_dec_ref(v_a_975_);
    lean_dec(v_a_974_);
    lean_dec_ref(v_a_973_);
    lean_dec(v_a_972_);
    lean_dec_ref(v_a_971_);
    lean_dec(v_a_970_);
    lean_dec(v_a_969_);
    lean_dec(v_a_968_);
    return v_res_980_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(
    mut v_msgData_981_: *mut LeanObject,
    mut v___y_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_st_ref_get(v___y_985_);
    v_env_988_ = lean_ctor_get(v___x_987_, 0);
    lean_inc_ref(v_env_988_);
    lean_dec(v___x_987_);
    v___x_989_ = lean_st_ref_get(v___y_983_);
    v_mctx_990_ = lean_ctor_get(v___x_989_, 0);
    lean_inc_ref(v_mctx_990_);
    lean_dec(v___x_989_);
    v_lctx_991_ = lean_ctor_get(v___y_982_, 2);
    v_options_992_ = lean_ctor_get(v___y_984_, 2);
    lean_inc_ref(v_options_992_);
    lean_inc_ref(v_lctx_991_);
    v___x_993_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_993_, 0, v_env_988_);
    lean_ctor_set(v___x_993_, 1, v_mctx_990_);
    lean_ctor_set(v___x_993_, 2, v_lctx_991_);
    lean_ctor_set(v___x_993_, 3, v_options_992_);
    v___x_994_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_994_, 0, v___x_993_);
    lean_ctor_set(v___x_994_, 1, v_msgData_981_);
    v___x_995_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_995_, 0, v___x_994_);
    return v___x_995_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1002_: *mut LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
    lean_dec(v___y_1000_);
    lean_dec_ref(v___y_999_);
    lean_dec(v___y_998_);
    lean_dec_ref(v___y_997_);
    return v_res_1002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
    mut v_msg_1003_: *mut LeanObject,
    mut v___y_1004_: *mut LeanObject,
    mut v___y_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1009_ = lean_ctor_get(v___y_1006_, 5);
                v___x_1010_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
                v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
                v_isSharedCheck_1019_ = (!lean_is_exclusive(v___x_1010_)) as u8;
                if v_isSharedCheck_1019_ == 0 {
                    v___x_1013_ = v___x_1010_;
                    v_isShared_1014_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1011_);
                    lean_dec(v___x_1010_);
                    v___x_1013_ = lean_box(0);
                    v_isShared_1014_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1009_);
                v___x_1015_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1015_, 0, v_ref_1009_);
                lean_ctor_set(v___x_1015_, 1, v_a_1011_);
                if v_isShared_1014_ == 0 {
                    lean_ctor_set_tag(v___x_1013_, 1);
                    lean_ctor_set(v___x_1013_, 0, v___x_1015_);
                    v___x_1017_ = v___x_1013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
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
    mut v_msg_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
    mut v___y_1022_: *mut LeanObject,
    mut v___y_1023_: *mut LeanObject,
    mut v___y_1024_: *mut LeanObject,
    mut v___y_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1026_: *mut LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(
            v_msg_1020_,
            v___y_1021_,
            v___y_1022_,
            v___y_1023_,
            v___y_1024_,
        );
    lean_dec(v___y_1024_);
    lean_dec_ref(v___y_1023_);
    lean_dec(v___y_1022_);
    lean_dec_ref(v___y_1021_);
    return v_res_1026_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1() -> *mut LeanObject
{
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1028_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0;
    v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
    return v___x_1029_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
    mut v_a_1030_: *mut LeanObject,
    mut v_a_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1046_: u8 = 0;
    let mut v_structs_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1042_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_1031_, v_a_1039_);
                if lean_obj_tag(v___x_1042_) == 0 {
                    v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1056_ = (!lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1045_ = v___x_1042_;
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1043_);
                        lean_dec(v___x_1042_);
                        v___x_1045_ = lean_box(0);
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1064_ = (!lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1042_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1057_);
                        lean_dec(v___x_1042_);
                        v___x_1059_ = lean_box(0);
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_1047_ = lean_ctor_get(v_a_1043_, 0);
                lean_inc_ref(v_structs_1047_);
                lean_dec(v_a_1043_);
                v___x_1048_ = lean_array_get_size(v_structs_1047_);
                v___x_1049_ = lean_nat_dec_lt(v_a_1030_, v___x_1048_);
                if v___x_1049_ == 0 {
                    lean_dec_ref(v_structs_1047_);
                    lean_del_object(v___x_1045_);
                    v___x_1050_ = lean_obj_once(
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
                    lean_dec_ref(v_structs_1047_);
                    if v_isShared_1046_ == 0 {
                        lean_ctor_set(v___x_1045_, 0, v___x_1052_);
                        v___x_1054_ = v___x_1045_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
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
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
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
    mut v_a_1065_: *mut LeanObject,
    mut v_a_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
        v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_,
        v_a_1073_, v_a_1074_, v_a_1075_,
    );
    lean_dec(v_a_1075_);
    lean_dec_ref(v_a_1074_);
    lean_dec(v_a_1073_);
    lean_dec_ref(v_a_1072_);
    lean_dec(v_a_1071_);
    lean_dec_ref(v_a_1070_);
    lean_dec(v_a_1069_);
    lean_dec_ref(v_a_1068_);
    lean_dec(v_a_1067_);
    lean_dec(v_a_1066_);
    lean_dec(v_a_1065_);
    return v_res_1077_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(
    mut v_00_u03b1_1078_: *mut LeanObject,
    mut v_msg_1079_: *mut LeanObject,
    mut v___y_1080_: *mut LeanObject,
    mut v___y_1081_: *mut LeanObject,
    mut v___y_1082_: *mut LeanObject,
    mut v___y_1083_: *mut LeanObject,
    mut v___y_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
    mut v___y_1087_: *mut LeanObject,
    mut v___y_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1093_: *mut LeanObject,
    mut v_msg_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
    mut v___y_1097_: *mut LeanObject,
    mut v___y_1098_: *mut LeanObject,
    mut v___y_1099_: *mut LeanObject,
    mut v___y_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
    mut v___y_1104_: *mut LeanObject,
    mut v___y_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1107_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1105_);
    lean_dec_ref(v___y_1104_);
    lean_dec(v___y_1103_);
    lean_dec_ref(v___y_1102_);
    lean_dec(v___y_1101_);
    lean_dec_ref(v___y_1100_);
    lean_dec(v___y_1099_);
    lean_dec_ref(v___y_1098_);
    lean_dec(v___y_1097_);
    lean_dec(v___y_1096_);
    lean_dec(v___y_1095_);
    return v_res_1107_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(
    mut v_ringId_x3f_1109_: *mut LeanObject,
    mut v_a_1110_: *mut LeanObject,
    mut v_a_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
    mut v_a_1113_: *mut LeanObject,
    mut v_a_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1131_: u8 = 0;
    let mut v_toRing_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut v_a_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ringId_x3f_1109_) == 1 {
                    v_val_1121_ = lean_ctor_get(v_ringId_x3f_1109_, 0);
                    v_isSharedCheck_1148_ = (!lean_is_exclusive(v_ringId_x3f_1109_)) as u8;
                    if v_isSharedCheck_1148_ == 0 {
                        v___x_1123_ = v_ringId_x3f_1109_;
                        v_isShared_1124_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1121_);
                        lean_dec(v_ringId_x3f_1109_);
                        v___x_1123_ = lean_box(0);
                        v_isShared_1124_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ringId_x3f_1109_);
                    v___x_1149_ = lean_box(0);
                    v___x_1150_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1150_, 0, v___x_1149_);
                    return v___x_1150_;
                }
            }
            1 => {
                v___x_1125_ = 0;
                v___x_1126_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1126_, 0, v_val_1121_);
                lean_ctor_set_uint8(
                    v___x_1126_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                lean_dec_ref_known(v___x_1126_, 1);
                if lean_obj_tag(v___x_1127_) == 0 {
                    v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1139_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1139_ == 0 {
                        v___x_1130_ = v___x_1127_;
                        v_isShared_1131_ = v_isSharedCheck_1139_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1128_);
                        lean_dec(v___x_1127_);
                        v___x_1130_ = lean_box(0);
                        v_isShared_1131_ = v_isSharedCheck_1139_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1123_);
                    v_a_1140_ = lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1147_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1142_ = v___x_1127_;
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1140_);
                        lean_dec(v___x_1127_);
                        v___x_1142_ = lean_box(0);
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_toRing_1132_ = lean_ctor_get(v_a_1128_, 0);
                lean_inc_ref(v_toRing_1132_);
                lean_dec(v_a_1128_);
                if v_isShared_1124_ == 0 {
                    lean_ctor_set(v___x_1123_, 0, v_toRing_1132_);
                    v___x_1134_ = v___x_1123_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_toRing_1132_);
                    v___x_1134_ = v_reuseFailAlloc_1138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1131_ == 0 {
                    lean_ctor_set(v___x_1130_, 0, v___x_1134_);
                    v___x_1136_ = v___x_1130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
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
                    v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
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
    mut v_ringId_x3f_1151_: *mut LeanObject,
    mut v_a_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
    mut v_a_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1163_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1161_);
    lean_dec_ref(v_a_1160_);
    lean_dec(v_a_1159_);
    lean_dec_ref(v_a_1158_);
    lean_dec(v_a_1157_);
    lean_dec_ref(v_a_1156_);
    lean_dec(v_a_1155_);
    lean_dec_ref(v_a_1154_);
    lean_dec(v_a_1153_);
    lean_dec(v_a_1152_);
    return v_res_1163_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0;
    v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
    mut v_a_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = lean_obj_once(
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
    mut v_a_1174_: *mut LeanObject,
    mut v_a_1175_: *mut LeanObject,
    mut v_a_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
        v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_,
    );
    lean_dec(v_a_1177_);
    lean_dec_ref(v_a_1176_);
    lean_dec(v_a_1175_);
    lean_dec_ref(v_a_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing(
    mut v_00_u03b1_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
        v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_,
    );
    return v___x_1193_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(
    mut v_00_u03b1_1194_: *mut LeanObject,
    mut v_a_1195_: *mut LeanObject,
    mut v_a_1196_: *mut LeanObject,
    mut v_a_1197_: *mut LeanObject,
    mut v_a_1198_: *mut LeanObject,
    mut v_a_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
    mut v_a_1203_: *mut LeanObject,
    mut v_a_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1207_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1205_);
    lean_dec_ref(v_a_1204_);
    lean_dec(v_a_1203_);
    lean_dec_ref(v_a_1202_);
    lean_dec(v_a_1201_);
    lean_dec_ref(v_a_1200_);
    lean_dec(v_a_1199_);
    lean_dec_ref(v_a_1198_);
    lean_dec(v_a_1197_);
    lean_dec(v_a_1196_);
    lean_dec(v_a_1195_);
    return v_res_1207_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0;
    v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
    return v___x_1210_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
    mut v_a_1211_: *mut LeanObject,
    mut v_a_1212_: *mut LeanObject,
    mut v_a_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = lean_obj_once(
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
    mut v_a_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
    mut v_a_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
    mut v_a_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1223_: *mut LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
        v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_,
    );
    lean_dec(v_a_1221_);
    lean_dec_ref(v_a_1220_);
    lean_dec(v_a_1219_);
    lean_dec_ref(v_a_1218_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(
    mut v_00_u03b1_1224_: *mut LeanObject,
    mut v_a_1225_: *mut LeanObject,
    mut v_a_1226_: *mut LeanObject,
    mut v_a_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_a_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
    mut v_a_1233_: *mut LeanObject,
    mut v_a_1234_: *mut LeanObject,
    mut v_a_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
        v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_,
    );
    return v___x_1237_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(
    mut v_00_u03b1_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
    mut v_a_1242_: *mut LeanObject,
    mut v_a_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
    mut v_a_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1249_);
    lean_dec_ref(v_a_1248_);
    lean_dec(v_a_1247_);
    lean_dec_ref(v_a_1246_);
    lean_dec(v_a_1245_);
    lean_dec_ref(v_a_1244_);
    lean_dec(v_a_1243_);
    lean_dec_ref(v_a_1242_);
    lean_dec(v_a_1241_);
    lean_dec(v_a_1240_);
    lean_dec(v_a_1239_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
    mut v_a_1252_: *mut LeanObject,
    mut v_a_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_,
                    v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_,
                );
                if lean_obj_tag(v___x_1264_) == 0 {
                    v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
                    lean_inc(v_a_1265_);
                    lean_dec_ref_known(v___x_1264_, 1);
                    v_ringId_x3f_1266_ = lean_ctor_get(v_a_1265_, 1);
                    lean_inc(v_ringId_x3f_1266_);
                    lean_dec(v_a_1265_);
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
                    v_a_1268_ = lean_ctor_get(v___x_1264_, 0);
                    v_isSharedCheck_1275_ = (!lean_is_exclusive(v___x_1264_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1270_ = v___x_1264_;
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1268_);
                        lean_dec(v___x_1264_);
                        v___x_1270_ = lean_box(0);
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
                    v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
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
    mut v_a_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
    mut v_a_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
    mut v_a_1284_: *mut LeanObject,
    mut v_a_1285_: *mut LeanObject,
    mut v_a_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1288_: *mut LeanObject = core::ptr::null_mut();
    v_res_1288_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
        v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_,
        v_a_1284_, v_a_1285_, v_a_1286_,
    );
    lean_dec(v_a_1286_);
    lean_dec_ref(v_a_1285_);
    lean_dec(v_a_1284_);
    lean_dec_ref(v_a_1283_);
    lean_dec(v_a_1282_);
    lean_dec_ref(v_a_1281_);
    lean_dec(v_a_1280_);
    lean_dec_ref(v_a_1279_);
    lean_dec(v_a_1278_);
    lean_dec(v_a_1277_);
    lean_dec(v_a_1276_);
    return v_res_1288_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(
    mut v_e_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_Meta_Sym_canon(
        v_e_1289_,
        v___y_1295_,
        v___y_1296_,
        v___y_1297_,
        v___y_1298_,
        v___y_1299_,
        v___y_1300_,
    );
    if lean_obj_tag(v___x_1302_) == 0 {
        let mut v_a_1303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
        v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
        lean_inc(v_a_1303_);
        lean_dec_ref_known(v___x_1302_, 1);
        v___x_1304_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1303_, v___y_1296_);
        return v___x_1304_;
    } else {
        return v___x_1302_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(
    mut v_e_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1318_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1316_);
    lean_dec_ref(v___y_1315_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    lean_dec(v___y_1312_);
    lean_dec_ref(v___y_1311_);
    lean_dec(v___y_1310_);
    lean_dec_ref(v___y_1309_);
    lean_dec(v___y_1308_);
    lean_dec(v___y_1307_);
    lean_dec(v___y_1306_);
    return v_res_1318_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(
    mut v_e_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1346_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1344_);
    lean_dec_ref(v___y_1343_);
    lean_dec(v___y_1342_);
    lean_dec_ref(v___y_1341_);
    lean_dec(v___y_1340_);
    lean_dec_ref(v___y_1339_);
    lean_dec(v___y_1338_);
    lean_dec_ref(v___y_1337_);
    lean_dec(v___y_1336_);
    lean_dec(v___y_1335_);
    lean_dec(v___y_1334_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
    mut v_a_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_a_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v_val_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut v_a_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1365_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(
                    v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_,
                    v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                );
                if lean_obj_tag(v___x_1365_) == 0 {
                    v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1375_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1366_);
                        lean_dec(v___x_1365_);
                        v___x_1368_ = lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1376_ = lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1383_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1383_ == 0 {
                        v___x_1378_ = v___x_1365_;
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1376_);
                        lean_dec(v___x_1365_);
                        v___x_1378_ = lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1383_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1366_) == 1 {
                    v_val_1370_ = lean_ctor_get(v_a_1366_, 0);
                    lean_inc(v_val_1370_);
                    lean_dec_ref_known(v_a_1366_, 1);
                    if v_isShared_1369_ == 0 {
                        lean_ctor_set(v___x_1368_, 0, v_val_1370_);
                        v___x_1372_ = v___x_1368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_val_1370_);
                        v___x_1372_ = v_reuseFailAlloc_1373_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1368_);
                    lean_dec(v_a_1366_);
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
                    v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
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
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
        v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_,
        v_a_1392_, v_a_1393_, v_a_1394_,
    );
    lean_dec(v_a_1394_);
    lean_dec_ref(v_a_1393_);
    lean_dec(v_a_1392_);
    lean_dec_ref(v_a_1391_);
    lean_dec(v_a_1390_);
    lean_dec_ref(v_a_1389_);
    lean_dec(v_a_1388_);
    lean_dec_ref(v_a_1387_);
    lean_dec(v_a_1386_);
    lean_dec(v_a_1385_);
    lean_dec(v_a_1384_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(
    mut v_f_1397_: *mut LeanObject,
    mut v_s_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_1413_: u8 = 0;
    let mut v_invSet_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_1417_: u8 = 0;
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_1399_ = lean_ctor_get(v_s_1398_, 0);
                v_invFn_x3f_1400_ = lean_ctor_get(v_s_1398_, 1);
                v_semiringId_x3f_1401_ = lean_ctor_get(v_s_1398_, 2);
                v_commSemiringInst_1402_ = lean_ctor_get(v_s_1398_, 3);
                v_commRingInst_1403_ = lean_ctor_get(v_s_1398_, 4);
                v_noZeroDivInst_x3f_1404_ = lean_ctor_get(v_s_1398_, 5);
                v_fieldInst_x3f_1405_ = lean_ctor_get(v_s_1398_, 6);
                v_powIdentityInst_x3f_1406_ = lean_ctor_get(v_s_1398_, 7);
                v_denoteEntries_1407_ = lean_ctor_get(v_s_1398_, 8);
                v_nextId_1408_ = lean_ctor_get(v_s_1398_, 9);
                v_steps_1409_ = lean_ctor_get(v_s_1398_, 10);
                v_queue_1410_ = lean_ctor_get(v_s_1398_, 11);
                v_basis_1411_ = lean_ctor_get(v_s_1398_, 12);
                v_diseqs_1412_ = lean_ctor_get(v_s_1398_, 13);
                v_recheck_1413_ = lean_ctor_get_uint8(
                    v_s_1398_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_1414_ = lean_ctor_get(v_s_1398_, 14);
                v_powIdentityVarCount_1415_ = lean_ctor_get(v_s_1398_, 15);
                v_numEq0_x3f_1416_ = lean_ctor_get(v_s_1398_, 16);
                v_numEq0Updated_1417_ = lean_ctor_get_uint8(
                    v_s_1398_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_1425_ = (!lean_is_exclusive(v_s_1398_)) as u8;
                if v_isSharedCheck_1425_ == 0 {
                    v___x_1419_ = v_s_1398_;
                    v_isShared_1420_ = v_isSharedCheck_1425_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_1416_);
                    lean_inc(v_powIdentityVarCount_1415_);
                    lean_inc(v_invSet_1414_);
                    lean_inc(v_diseqs_1412_);
                    lean_inc(v_basis_1411_);
                    lean_inc(v_queue_1410_);
                    lean_inc(v_steps_1409_);
                    lean_inc(v_nextId_1408_);
                    lean_inc(v_denoteEntries_1407_);
                    lean_inc(v_powIdentityInst_x3f_1406_);
                    lean_inc(v_fieldInst_x3f_1405_);
                    lean_inc(v_noZeroDivInst_x3f_1404_);
                    lean_inc(v_commRingInst_1403_);
                    lean_inc(v_commSemiringInst_1402_);
                    lean_inc(v_semiringId_x3f_1401_);
                    lean_inc(v_invFn_x3f_1400_);
                    lean_inc(v_toRing_1399_);
                    lean_dec(v_s_1398_);
                    v___x_1419_ = lean_box(0);
                    v_isShared_1420_ = v_isSharedCheck_1425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1421_ = lean_apply_1(v_f_1397_, v_toRing_1399_);
                if v_isShared_1420_ == 0 {
                    lean_ctor_set(v___x_1419_, 0, v___x_1421_);
                    v___x_1423_ = v___x_1419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_invFn_x3f_1400_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_semiringId_x3f_1401_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_commSemiringInst_1402_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_commRingInst_1403_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 5, v_noZeroDivInst_x3f_1404_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 6, v_fieldInst_x3f_1405_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 7, v_powIdentityInst_x3f_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 8, v_denoteEntries_1407_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 9, v_nextId_1408_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 10, v_steps_1409_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 11, v_queue_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 12, v_basis_1411_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 13, v_diseqs_1412_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 14, v_invSet_1414_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 15, v_powIdentityVarCount_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 16, v_numEq0_x3f_1416_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1424_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_1413_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1424_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v_f_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
    mut v___y_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1439_) == 0 {
                    v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
                    lean_inc(v_a_1440_);
                    lean_dec_ref_known(v___x_1439_, 1);
                    v_ringId_x3f_1441_ = lean_ctor_get(v_a_1440_, 1);
                    lean_inc(v_ringId_x3f_1441_);
                    lean_dec(v_a_1440_);
                    if lean_obj_tag(v_ringId_x3f_1441_) == 1 {
                        v_val_1442_ = lean_ctor_get(v_ringId_x3f_1441_, 0);
                        lean_inc(v_val_1442_);
                        lean_dec_ref_known(v_ringId_x3f_1441_, 1);
                        v___f_1443_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_1443_, 0, v_f_1426_);
                        v___x_1444_ = 0;
                        v___x_1445_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1445_, 0, v_val_1442_);
                        lean_ctor_set_uint8(
                            v___x_1445_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1444_,
                        );
                        v___x_1446_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_1443_,
                                v___x_1445_,
                                v___y_1428_,
                            );
                        lean_dec_ref_known(v___x_1445_, 1);
                        return v___x_1446_;
                    } else {
                        lean_dec(v_ringId_x3f_1441_);
                        lean_dec_ref(v_f_1426_);
                        v___x_1447_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                            v___y_1434_,
                            v___y_1435_,
                            v___y_1436_,
                            v___y_1437_,
                        );
                        return v___x_1447_;
                    }
                } else {
                    lean_dec_ref(v_f_1426_);
                    v_a_1448_ = lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1455_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v___x_1450_ = v___x_1439_;
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1448_);
                        lean_dec(v___x_1439_);
                        v___x_1450_ = lean_box(0);
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
                    v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
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
    mut v_f_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1469_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1467_);
    lean_dec_ref(v___y_1466_);
    lean_dec(v___y_1465_);
    lean_dec_ref(v___y_1464_);
    lean_dec(v___y_1463_);
    lean_dec_ref(v___y_1462_);
    lean_dec(v___y_1461_);
    lean_dec_ref(v___y_1460_);
    lean_dec(v___y_1459_);
    lean_dec(v___y_1458_);
    lean_dec(v___y_1457_);
    return v_res_1469_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1()
-> *mut LeanObject {
    let mut v___f_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    v___f_1471_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0;
    v___x_1472_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1473_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1473_, 0, v___x_1472_);
    lean_ctor_set(v___x_1473_, 1, v___f_1471_);
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM() -> *mut LeanObject {
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v___x_1474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1,
    );
    return v___x_1474_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
    mut v_x_1475_: *mut LeanObject,
    mut v_a_1476_: *mut LeanObject,
    mut v_a_1477_: *mut LeanObject,
    mut v_a_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
    mut v_a_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
    mut v_a_1482_: *mut LeanObject,
    mut v_a_1483_: *mut LeanObject,
    mut v_a_1484_: *mut LeanObject,
    mut v_a_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1488_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_,
                    v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_,
                );
                if lean_obj_tag(v___x_1488_) == 0 {
                    v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
                    lean_inc(v_a_1489_);
                    lean_dec_ref_known(v___x_1488_, 1);
                    v_ringId_x3f_1490_ = lean_ctor_get(v_a_1489_, 1);
                    lean_inc(v_ringId_x3f_1490_);
                    lean_dec(v_a_1489_);
                    if lean_obj_tag(v_ringId_x3f_1490_) == 1 {
                        v_val_1491_ = lean_ctor_get(v_ringId_x3f_1490_, 0);
                        lean_inc(v_val_1491_);
                        lean_dec_ref_known(v_ringId_x3f_1490_, 1);
                        v___x_1492_ = 0;
                        v___x_1493_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1493_, 0, v_val_1491_);
                        lean_ctor_set_uint8(
                            v___x_1493_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1492_,
                        );
                        lean_inc(v_a_1486_);
                        lean_inc_ref(v_a_1485_);
                        lean_inc(v_a_1484_);
                        lean_inc_ref(v_a_1483_);
                        lean_inc(v_a_1482_);
                        lean_inc_ref(v_a_1481_);
                        lean_inc(v_a_1480_);
                        lean_inc_ref(v_a_1479_);
                        lean_inc(v_a_1478_);
                        lean_inc(v_a_1477_);
                        v___x_1494_ = lean_apply_12(
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
                            lean_box(0),
                        );
                        return v___x_1494_;
                    } else {
                        lean_dec(v_ringId_x3f_1490_);
                        lean_dec_ref(v_x_1475_);
                        v___x_1495_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                            v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_,
                        );
                        return v___x_1495_;
                    }
                } else {
                    lean_dec_ref(v_x_1475_);
                    v_a_1496_ = lean_ctor_get(v___x_1488_, 0);
                    v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1488_)) as u8;
                    if v_isSharedCheck_1503_ == 0 {
                        v___x_1498_ = v___x_1488_;
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1496_);
                        lean_dec(v___x_1488_);
                        v___x_1498_ = lean_box(0);
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
                    v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
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
    mut v_x_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
    mut v_a_1510_: *mut LeanObject,
    mut v_a_1511_: *mut LeanObject,
    mut v_a_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
    mut v_a_1515_: *mut LeanObject,
    mut v_a_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1517_: *mut LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
        v_x_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_,
        v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_,
    );
    lean_dec(v_a_1515_);
    lean_dec_ref(v_a_1514_);
    lean_dec(v_a_1513_);
    lean_dec_ref(v_a_1512_);
    lean_dec(v_a_1511_);
    lean_dec_ref(v_a_1510_);
    lean_dec(v_a_1509_);
    lean_dec_ref(v_a_1508_);
    lean_dec(v_a_1507_);
    lean_dec(v_a_1506_);
    lean_dec(v_a_1505_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM(
    mut v_00_u03b1_1518_: *mut LeanObject,
    mut v_x_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_a_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
        v_x_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_,
        v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_,
    );
    return v___x_1532_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(
    mut v_00_u03b1_1533_: *mut LeanObject,
    mut v_x_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
    mut v_a_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_a_1541_: *mut LeanObject,
    mut v_a_1542_: *mut LeanObject,
    mut v_a_1543_: *mut LeanObject,
    mut v_a_1544_: *mut LeanObject,
    mut v_a_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1547_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1545_);
    lean_dec_ref(v_a_1544_);
    lean_dec(v_a_1543_);
    lean_dec_ref(v_a_1542_);
    lean_dec(v_a_1541_);
    lean_dec_ref(v_a_1540_);
    lean_dec(v_a_1539_);
    lean_dec_ref(v_a_1538_);
    lean_dec(v_a_1537_);
    lean_dec(v_a_1536_);
    lean_dec(v_a_1535_);
    return v_res_1547_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(
    mut v_a_1548_: *mut LeanObject,
    mut v_f_1549_: *mut LeanObject,
    mut v_s_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v_v_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1551_ = lean_ctor_get(v_s_1550_, 0);
                v_typeIdOf_1552_ = lean_ctor_get(v_s_1550_, 1);
                v_exprToStructId_1553_ = lean_ctor_get(v_s_1550_, 2);
                v_exprToStructIdEntries_1554_ = lean_ctor_get(v_s_1550_, 3);
                v_forbiddenNatModules_1555_ = lean_ctor_get(v_s_1550_, 4);
                v_natStructs_1556_ = lean_ctor_get(v_s_1550_, 5);
                v_natTypeIdOf_1557_ = lean_ctor_get(v_s_1550_, 6);
                v_exprToNatStructId_1558_ = lean_ctor_get(v_s_1550_, 7);
                v___x_1559_ = lean_array_get_size(v_structs_1551_);
                v___x_1560_ = lean_nat_dec_lt(v_a_1548_, v___x_1559_);
                if v___x_1560_ == 0 {
                    lean_dec_ref(v_f_1549_);
                    return v_s_1550_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_1558_);
                    lean_inc_ref(v_natTypeIdOf_1557_);
                    lean_inc_ref(v_natStructs_1556_);
                    lean_inc_ref(v_forbiddenNatModules_1555_);
                    lean_inc_ref(v_exprToStructIdEntries_1554_);
                    lean_inc_ref(v_exprToStructId_1553_);
                    lean_inc_ref(v_typeIdOf_1552_);
                    lean_inc_ref(v_structs_1551_);
                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v_s_1550_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v_unused_1573_ = lean_ctor_get(v_s_1550_, 7);
                        lean_dec(v_unused_1573_);
                        v_unused_1574_ = lean_ctor_get(v_s_1550_, 6);
                        lean_dec(v_unused_1574_);
                        v_unused_1575_ = lean_ctor_get(v_s_1550_, 5);
                        lean_dec(v_unused_1575_);
                        v_unused_1576_ = lean_ctor_get(v_s_1550_, 4);
                        lean_dec(v_unused_1576_);
                        v_unused_1577_ = lean_ctor_get(v_s_1550_, 3);
                        lean_dec(v_unused_1577_);
                        v_unused_1578_ = lean_ctor_get(v_s_1550_, 2);
                        lean_dec(v_unused_1578_);
                        v_unused_1579_ = lean_ctor_get(v_s_1550_, 1);
                        lean_dec(v_unused_1579_);
                        v_unused_1580_ = lean_ctor_get(v_s_1550_, 0);
                        lean_dec(v_unused_1580_);
                        v___x_1562_ = v_s_1550_;
                        v_isShared_1563_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_1550_);
                        v___x_1562_ = lean_box(0);
                        v_isShared_1563_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1564_ = lean_array_fget(v_structs_1551_, v_a_1548_);
                v___x_1565_ = lean_box(0);
                v_xs_x27_1566_ = lean_array_fset(v_structs_1551_, v_a_1548_, v___x_1565_);
                v___x_1567_ = lean_apply_1(v_f_1549_, v_v_1564_);
                v___x_1568_ = lean_array_fset(v_xs_x27_1566_, v_a_1548_, v___x_1567_);
                if v_isShared_1563_ == 0 {
                    lean_ctor_set(v___x_1562_, 0, v___x_1568_);
                    v___x_1570_ = v___x_1562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_typeIdOf_1552_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_exprToStructId_1553_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_exprToStructIdEntries_1554_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_forbiddenNatModules_1555_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 5, v_natStructs_1556_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 6, v_natTypeIdOf_1557_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 7, v_exprToNatStructId_1558_);
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
    mut v_a_1581_: *mut LeanObject,
    mut v_f_1582_: *mut LeanObject,
    mut v_s_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1584_: *mut LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(
        v_a_1581_, v_f_1582_, v_s_1583_,
    );
    lean_dec(v_a_1581_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(
    mut v_f_1585_: *mut LeanObject,
    mut v_a_1586_: *mut LeanObject,
    mut v_a_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1586_);
    v___f_1589_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1589_, 0, v_a_1586_);
    lean_closure_set(v___f_1589_, 1, v_f_1585_);
    v___x_1590_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_1591_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1590_, v___f_1589_, v_a_1587_);
    return v___x_1591_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(
    mut v_f_1592_: *mut LeanObject,
    mut v_a_1593_: *mut LeanObject,
    mut v_a_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1596_: *mut LeanObject = core::ptr::null_mut();
    v_res_1596_ =
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1592_, v_a_1593_, v_a_1594_);
    lean_dec(v_a_1594_);
    lean_dec(v_a_1593_);
    return v_res_1596_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct(
    mut v_f_1597_: *mut LeanObject,
    mut v_a_1598_: *mut LeanObject,
    mut v_a_1599_: *mut LeanObject,
    mut v_a_1600_: *mut LeanObject,
    mut v_a_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1598_);
    v___f_1610_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1610_, 0, v_a_1598_);
    lean_closure_set(v___f_1610_, 1, v_f_1597_);
    v___x_1611_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_1612_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1611_, v___f_1610_, v_a_1599_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(
    mut v_f_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
    mut v_a_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
    mut v_a_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(
        v_f_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_,
        v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_,
    );
    lean_dec(v_a_1624_);
    lean_dec_ref(v_a_1623_);
    lean_dec(v_a_1622_);
    lean_dec_ref(v_a_1621_);
    lean_dec(v_a_1620_);
    lean_dec_ref(v_a_1619_);
    lean_dec(v_a_1618_);
    lean_dec_ref(v_a_1617_);
    lean_dec(v_a_1616_);
    lean_dec(v_a_1615_);
    lean_dec(v_a_1614_);
    return v_res_1626_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM =
        _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
}
