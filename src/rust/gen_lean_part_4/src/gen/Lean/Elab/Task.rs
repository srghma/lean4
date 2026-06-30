// Lean compiler output
// Module: Lean.Elab.Task
// Imports: Lean.Elab.Tactic.Basic
use crate::ffi::{
    lean_io_as_task, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_task_map,
};
use crate::r#gen::Init::System::CancelToken::{
    l_IO_CancelToken_new, l_IO_CancelToken_onSet, l_IO_CancelToken_set___boxed,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_wrapAsync___redArg;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_TermElabM_run___boxed;
pub static l_Lean_Core_CoreM_asTask___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Core_CoreM_asTask___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_CoreM_asTask___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_MetaM_asTask___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_MetaM_asTask___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_MetaM_asTask___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__0(
    mut v_t_738_: *mut leanh::LeanObject,
    mut v_x_739_: *mut leanh::LeanObject,
    mut v___y_740_: *mut leanh::LeanObject,
    mut v___y_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_747_: u8 = 0;
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_a_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_741_);
                leanh::lean_inc_ref(v___y_740_);
                v___x_743_ = leanh::lean_apply_3(
                    v_t_738_,
                    v___y_740_,
                    v___y_741_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_743_) == 0 {
                    v_a_744_ = leanh::lean_ctor_get(v___x_743_, 0);
                    v_isSharedCheck_753_ = (!leanh::lean_is_exclusive(v___x_743_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_746_ = v___x_743_;
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_744_);
                        leanh::lean_dec(v___x_743_);
                        v___x_746_ = leanh::lean_box(0);
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_754_ = leanh::lean_ctor_get(v___x_743_, 0);
                    v_isSharedCheck_761_ = (!leanh::lean_is_exclusive(v___x_743_)) as u8;
                    if v_isSharedCheck_761_ == 0 {
                        v___x_756_ = v___x_743_;
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_754_);
                        leanh::lean_dec(v___x_743_);
                        v___x_756_ = leanh::lean_box(0);
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_748_ = lean_st_ref_get(v___y_741_);
                v___x_749_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_749_, 0, v_a_744_);
                leanh::lean_ctor_set(v___x_749_, 1, v___x_748_);
                if v_isShared_747_ == 0 {
                    leanh::lean_ctor_set(v___x_746_, 0, v___x_749_);
                    v___x_751_ = v___x_746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
                    v___x_751_ = v_reuseFailAlloc_752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_751_;
            }
            3 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed(
    mut v_t_762_: *mut leanh::LeanObject,
    mut v_x_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
    mut v___y_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ =
        l_Lean_Core_CoreM_asTask___redArg___lam__0(v_t_762_, v_x_763_, v___y_764_, v___y_765_);
    leanh::lean_dec(v___y_765_);
    leanh::lean_dec_ref(v___y_764_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__1(
    mut v_a_768_: *mut leanh::LeanObject,
    mut v___x_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_a_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_783_: u8 = 0;
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_771_ =
                    leanh::lean_apply_2(v_a_768_, v___x_769_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_771_) == 0 {
                    v_a_772_ = leanh::lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_779_ = (!leanh::lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_779_ == 0 {
                        v___x_774_ = v___x_771_;
                        v_isShared_775_ = v_isSharedCheck_779_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_772_);
                        leanh::lean_dec(v___x_771_);
                        v___x_774_ = leanh::lean_box(0);
                        v_isShared_775_ = v_isSharedCheck_779_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_780_ = leanh::lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_787_ = (!leanh::lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_787_ == 0 {
                        v___x_782_ = v___x_771_;
                        v_isShared_783_ = v_isSharedCheck_787_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_780_);
                        leanh::lean_dec(v___x_771_);
                        v___x_782_ = leanh::lean_box(0);
                        v_isShared_783_ = v_isSharedCheck_787_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_774_, 1);
                    v___x_777_ = v___x_774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
                    v___x_777_ = v_reuseFailAlloc_778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_777_;
            }
            3 => {
                if v_isShared_783_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_782_, 0);
                    v___x_785_ = v___x_782_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
                    v___x_785_ = v_reuseFailAlloc_786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed(
    mut v_a_788_: *mut leanh::LeanObject,
    mut v___x_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_Core_CoreM_asTask___redArg___lam__1(v_a_788_, v___x_789_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__2(
    mut v_result_792_: *mut leanh::LeanObject,
    mut v___y_793_: *mut leanh::LeanObject,
    mut v___y_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v_a_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_807_: u8 = 0;
    let mut v_fst_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_result_792_) == 0 {
                    v_a_796_ = leanh::lean_ctor_get(v_result_792_, 0);
                    v_isSharedCheck_803_ = (!leanh::lean_is_exclusive(v_result_792_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v_result_792_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_796_);
                        leanh::lean_dec(v_result_792_);
                        v___x_798_ = leanh::lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_804_ = leanh::lean_ctor_get(v_result_792_, 0);
                    v_isSharedCheck_814_ = (!leanh::lean_is_exclusive(v_result_792_)) as u8;
                    if v_isSharedCheck_814_ == 0 {
                        v___x_806_ = v_result_792_;
                        v_isShared_807_ = v_isSharedCheck_814_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_804_);
                        leanh::lean_dec(v_result_792_);
                        v___x_806_ = leanh::lean_box(0);
                        v_isShared_807_ = v_isSharedCheck_814_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_799_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_798_, 1);
                    v___x_801_ = v___x_798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_801_;
            }
            3 => {
                v_fst_808_ = leanh::lean_ctor_get(v_a_804_, 0);
                leanh::lean_inc(v_fst_808_);
                v_snd_809_ = leanh::lean_ctor_get(v_a_804_, 1);
                leanh::lean_inc(v_snd_809_);
                leanh::lean_dec(v_a_804_);
                v___x_810_ = lean_st_ref_set(v___y_794_, v_snd_809_);
                if v_isShared_807_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_806_, 0);
                    leanh::lean_ctor_set(v___x_806_, 0, v_fst_808_);
                    v___x_812_ = v___x_806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_808_);
                    v___x_812_ = v_reuseFailAlloc_813_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed(
    mut v_result_815_: *mut leanh::LeanObject,
    mut v___y_816_: *mut leanh::LeanObject,
    mut v___y_817_: *mut leanh::LeanObject,
    mut v___y_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_Core_CoreM_asTask___redArg___lam__2(v_result_815_, v___y_816_, v___y_817_);
    leanh::lean_dec(v___y_817_);
    leanh::lean_dec_ref(v___y_816_);
    return v_res_819_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg(
    mut v_t_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u8 = 0;
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_850_: u8 = 0;
    let mut v_a_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_854_: u8 = 0;
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_825_ = l_IO_CancelToken_new();
                v___f_826_ = leanh::lean_alloc_closure(
                    l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_826_, 0, v_t_821_);
                leanh::lean_inc_ref(v___x_825_);
                v___x_827_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_827_, 0, v___x_825_);
                v___x_828_ =
                    l_Lean_Core_wrapAsync___redArg(v___f_826_, v___x_827_, v_a_822_, v_a_823_);
                if leanh::lean_obj_tag(v___x_828_) == 0 {
                    v_a_829_ = leanh::lean_ctor_get(v___x_828_, 0);
                    v_isSharedCheck_850_ = (!leanh::lean_is_exclusive(v___x_828_)) as u8;
                    if v_isSharedCheck_850_ == 0 {
                        v___x_831_ = v___x_828_;
                        v_isShared_832_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_829_);
                        leanh::lean_dec(v___x_828_);
                        v___x_831_ = leanh::lean_box(0);
                        v_isShared_832_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_825_);
                    v_a_851_ = leanh::lean_ctor_get(v___x_828_, 0);
                    v_isSharedCheck_858_ = (!leanh::lean_is_exclusive(v___x_828_)) as u8;
                    if v_isSharedCheck_858_ == 0 {
                        v___x_853_ = v___x_828_;
                        v_isShared_854_ = v_isSharedCheck_858_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_851_);
                        leanh::lean_dec(v___x_828_);
                        v___x_853_ = leanh::lean_box(0);
                        v_isShared_854_ = v_isSharedCheck_858_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_833_ = leanh::lean_box(0);
                v___f_834_ = leanh::lean_alloc_closure(
                    l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_834_, 0, v_a_829_);
                leanh::lean_closure_set(v___f_834_, 1, v___x_833_);
                v___x_835_ = leanh::lean_unsigned_to_nat(0);
                v___x_836_ = lean_io_as_task(v___f_834_, v___x_835_);
                v_cancelTk_x3f_837_ = leanh::lean_ctor_get(v_a_822_, 12);
                v___f_838_ = l_Lean_Core_CoreM_asTask___redArg___closed__0;
                if leanh::lean_obj_tag(v_cancelTk_x3f_837_) == 1 {
                    v_val_847_ = leanh::lean_ctor_get(v_cancelTk_x3f_837_, 0);
                    leanh::lean_inc_ref(v___x_825_);
                    v___x_848_ = leanh::lean_alloc_closure(
                        l_IO_CancelToken_set___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___x_848_, 0, v___x_825_);
                    v___x_849_ = l_IO_CancelToken_onSet(v_val_847_, v___x_848_);
                    state = 2;
                    continue;
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_840_ = leanh::lean_alloc_closure(
                    l_IO_CancelToken_set___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___x_840_, 0, v___x_825_);
                v___x_841_ = 1;
                v___x_842_ = lean_task_map(v___f_838_, v___x_836_, v___x_835_, v___x_841_);
                v___x_843_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_843_, 0, v___x_840_);
                leanh::lean_ctor_set(v___x_843_, 1, v___x_842_);
                if v_isShared_832_ == 0 {
                    leanh::lean_ctor_set(v___x_831_, 0, v___x_843_);
                    v___x_845_ = v___x_831_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
                    v___x_845_ = v_reuseFailAlloc_846_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_845_;
            }
            4 => {
                if v_isShared_854_ == 0 {
                    v___x_856_ = v___x_853_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_857_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
                    v___x_856_ = v_reuseFailAlloc_857_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_asTask___redArg___boxed(
    mut v_t_859_: *mut leanh::LeanObject,
    mut v_a_860_: *mut leanh::LeanObject,
    mut v_a_861_: *mut leanh::LeanObject,
    mut v_a_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l_Lean_Core_CoreM_asTask___redArg(v_t_859_, v_a_860_, v_a_861_);
    leanh::lean_dec(v_a_861_);
    leanh::lean_dec_ref(v_a_860_);
    return v_res_863_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask(
    mut v_00_u03b1_864_: *mut leanh::LeanObject,
    mut v_t_865_: *mut leanh::LeanObject,
    mut v_a_866_: *mut leanh::LeanObject,
    mut v_a_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Core_CoreM_asTask___redArg(v_t_865_, v_a_866_, v_a_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask___boxed(
    mut v_00_u03b1_870_: *mut leanh::LeanObject,
    mut v_t_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
    mut v_a_873_: *mut leanh::LeanObject,
    mut v_a_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_Core_CoreM_asTask(v_00_u03b1_870_, v_t_871_, v_a_872_, v_a_873_);
    leanh::lean_dec(v_a_873_);
    leanh::lean_dec_ref(v_a_872_);
    return v_res_875_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask_x27___redArg(
    mut v_t_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_884_: u8 = 0;
    let mut v_snd_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_889_: u8 = 0;
    let mut v_a_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_880_ = l_Lean_Core_CoreM_asTask___redArg(v_t_876_, v_a_877_, v_a_878_);
                if leanh::lean_obj_tag(v___x_880_) == 0 {
                    v_a_881_ = leanh::lean_ctor_get(v___x_880_, 0);
                    v_isSharedCheck_889_ = (!leanh::lean_is_exclusive(v___x_880_)) as u8;
                    if v_isSharedCheck_889_ == 0 {
                        v___x_883_ = v___x_880_;
                        v_isShared_884_ = v_isSharedCheck_889_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_881_);
                        leanh::lean_dec(v___x_880_);
                        v___x_883_ = leanh::lean_box(0);
                        v_isShared_884_ = v_isSharedCheck_889_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_890_ = leanh::lean_ctor_get(v___x_880_, 0);
                    v_isSharedCheck_897_ = (!leanh::lean_is_exclusive(v___x_880_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_892_ = v___x_880_;
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_890_);
                        leanh::lean_dec(v___x_880_);
                        v___x_892_ = leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_885_ = leanh::lean_ctor_get(v_a_881_, 1);
                leanh::lean_inc(v_snd_885_);
                leanh::lean_dec(v_a_881_);
                if v_isShared_884_ == 0 {
                    leanh::lean_ctor_set(v___x_883_, 0, v_snd_885_);
                    v___x_887_ = v___x_883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_888_, 0, v_snd_885_);
                    v___x_887_ = v_reuseFailAlloc_888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_887_;
            }
            3 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_asTask_x27___redArg___boxed(
    mut v_t_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_902_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_898_, v_a_899_, v_a_900_);
    leanh::lean_dec(v_a_900_);
    leanh::lean_dec_ref(v_a_899_);
    return v_res_902_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask_x27(
    mut v_00_u03b1_903_: *mut leanh::LeanObject,
    mut v_t_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_908_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_904_, v_a_905_, v_a_906_);
    return v___x_908_;
}
pub unsafe fn l_Lean_Core_CoreM_asTask_x27___boxed(
    mut v_00_u03b1_909_: *mut leanh::LeanObject,
    mut v_t_910_: *mut leanh::LeanObject,
    mut v_a_911_: *mut leanh::LeanObject,
    mut v_a_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_914_ = l_Lean_Core_CoreM_asTask_x27(v_00_u03b1_909_, v_t_910_, v_a_911_, v_a_912_);
    leanh::lean_dec(v_a_912_);
    leanh::lean_dec_ref(v_a_911_);
    return v_res_914_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg___lam__0(
    mut v_val_915_: *mut leanh::LeanObject,
    mut v_t_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_926_: u8 = 0;
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut v_a_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_921_ = lean_st_mk_ref(v_val_915_);
                leanh::lean_inc(v___x_921_);
                leanh::lean_inc_ref(v_a_917_);
                v___x_922_ = leanh::lean_apply_5(
                    v_t_916_,
                    v_a_917_,
                    v___x_921_,
                    v___y_918_,
                    v___y_919_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_922_) == 0 {
                    v_a_923_ = leanh::lean_ctor_get(v___x_922_, 0);
                    v_isSharedCheck_932_ = (!leanh::lean_is_exclusive(v___x_922_)) as u8;
                    if v_isSharedCheck_932_ == 0 {
                        v___x_925_ = v___x_922_;
                        v_isShared_926_ = v_isSharedCheck_932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_923_);
                        leanh::lean_dec(v___x_922_);
                        v___x_925_ = leanh::lean_box(0);
                        v_isShared_926_ = v_isSharedCheck_932_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_921_);
                    v_a_933_ = leanh::lean_ctor_get(v___x_922_, 0);
                    v_isSharedCheck_940_ = (!leanh::lean_is_exclusive(v___x_922_)) as u8;
                    if v_isSharedCheck_940_ == 0 {
                        v___x_935_ = v___x_922_;
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_933_);
                        leanh::lean_dec(v___x_922_);
                        v___x_935_ = leanh::lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_927_ = lean_st_ref_get(v___x_921_);
                leanh::lean_dec(v___x_921_);
                v___x_928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_928_, 0, v_a_923_);
                leanh::lean_ctor_set(v___x_928_, 1, v___x_927_);
                if v_isShared_926_ == 0 {
                    leanh::lean_ctor_set(v___x_925_, 0, v___x_928_);
                    v___x_930_ = v___x_925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_930_;
            }
            3 => {
                if v_isShared_936_ == 0 {
                    v___x_938_ = v___x_935_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
                    v___x_938_ = v_reuseFailAlloc_939_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed(
    mut v_val_941_: *mut leanh::LeanObject,
    mut v_t_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v___y_944_: *mut leanh::LeanObject,
    mut v___y_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Lean_Meta_MetaM_asTask___redArg___lam__0(
        v_val_941_, v_t_942_, v_a_943_, v___y_944_, v___y_945_,
    );
    leanh::lean_dec_ref(v_a_943_);
    return v_res_947_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg___lam__1(
    mut v_c_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v_fst_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_952_);
                leanh::lean_inc_ref(v___y_951_);
                v___x_954_ = leanh::lean_apply_3(
                    v_c_948_,
                    v___y_951_,
                    v___y_952_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_954_) == 0 {
                    v_a_955_ = leanh::lean_ctor_get(v___x_954_, 0);
                    v_isSharedCheck_965_ = (!leanh::lean_is_exclusive(v___x_954_)) as u8;
                    if v_isSharedCheck_965_ == 0 {
                        v___x_957_ = v___x_954_;
                        v_isShared_958_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_955_);
                        leanh::lean_dec(v___x_954_);
                        v___x_957_ = leanh::lean_box(0);
                        v_isShared_958_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_966_ = leanh::lean_ctor_get(v___x_954_, 0);
                    v_isSharedCheck_973_ = (!leanh::lean_is_exclusive(v___x_954_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_954_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_966_);
                        leanh::lean_dec(v___x_954_);
                        v___x_968_ = leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_959_ = leanh::lean_ctor_get(v_a_955_, 0);
                leanh::lean_inc(v_fst_959_);
                v_snd_960_ = leanh::lean_ctor_get(v_a_955_, 1);
                leanh::lean_inc(v_snd_960_);
                leanh::lean_dec(v_a_955_);
                v___x_961_ = lean_st_ref_set(v___y_950_, v_snd_960_);
                if v_isShared_958_ == 0 {
                    leanh::lean_ctor_set(v___x_957_, 0, v_fst_959_);
                    v___x_963_ = v___x_957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fst_959_);
                    v___x_963_ = v_reuseFailAlloc_964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_963_;
            }
            3 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed(
    mut v_c_974_: *mut leanh::LeanObject,
    mut v___y_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lean_Meta_MetaM_asTask___redArg___lam__1(
        v_c_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_,
    );
    leanh::lean_dec(v___y_978_);
    leanh::lean_dec_ref(v___y_977_);
    leanh::lean_dec(v___y_976_);
    leanh::lean_dec_ref(v___y_975_);
    return v_res_980_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg(
    mut v_t_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
    mut v_a_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
    mut v_a_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v_fst_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v___f_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_a_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_988_ = lean_st_ref_get(v_a_984_);
                leanh::lean_inc_ref(v_a_983_);
                v___f_989_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_989_, 0, v___x_988_);
                leanh::lean_closure_set(v___f_989_, 1, v_t_982_);
                leanh::lean_closure_set(v___f_989_, 2, v_a_983_);
                v___x_990_ = l_Lean_Core_CoreM_asTask___redArg(v___f_989_, v_a_985_, v_a_986_);
                if leanh::lean_obj_tag(v___x_990_) == 0 {
                    v_a_991_ = leanh::lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_1011_ = (!leanh::lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_1011_ == 0 {
                        v___x_993_ = v___x_990_;
                        v_isShared_994_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_991_);
                        leanh::lean_dec(v___x_990_);
                        v___x_993_ = leanh::lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1012_ = leanh::lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_1019_ = (!leanh::lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_1019_ == 0 {
                        v___x_1014_ = v___x_990_;
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1012_);
                        leanh::lean_dec(v___x_990_);
                        v___x_1014_ = leanh::lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_995_ = leanh::lean_ctor_get(v_a_991_, 0);
                v_snd_996_ = leanh::lean_ctor_get(v_a_991_, 1);
                v_isSharedCheck_1010_ = (!leanh::lean_is_exclusive(v_a_991_)) as u8;
                if v_isSharedCheck_1010_ == 0 {
                    v___x_998_ = v_a_991_;
                    v_isShared_999_ = v_isSharedCheck_1010_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_996_);
                    leanh::lean_inc(v_fst_995_);
                    leanh::lean_dec(v_a_991_);
                    v___x_998_ = leanh::lean_box(0);
                    v_isShared_999_ = v_isSharedCheck_1010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1000_ = l_Lean_Meta_MetaM_asTask___redArg___closed__0;
                v___x_1001_ = leanh::lean_unsigned_to_nat(0);
                v___x_1002_ = 1;
                v___x_1003_ = lean_task_map(v___f_1000_, v_snd_996_, v___x_1001_, v___x_1002_);
                if v_isShared_999_ == 0 {
                    leanh::lean_ctor_set(v___x_998_, 1, v___x_1003_);
                    v___x_1005_ = v___x_998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1009_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_fst_995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1003_);
                    v___x_1005_ = v_reuseFailAlloc_1009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_994_ == 0 {
                    leanh::lean_ctor_set(v___x_993_, 0, v___x_1005_);
                    v___x_1007_ = v___x_993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
                    v___x_1007_ = v_reuseFailAlloc_1008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1007_;
            }
            5 => {
                if v_isShared_1015_ == 0 {
                    v___x_1017_ = v___x_1014_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___redArg___boxed(
    mut v_t_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Lean_Meta_MetaM_asTask___redArg(v_t_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
    leanh::lean_dec(v_a_1024_);
    leanh::lean_dec_ref(v_a_1023_);
    leanh::lean_dec(v_a_1022_);
    leanh::lean_dec_ref(v_a_1021_);
    return v_res_1026_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask(
    mut v_00_u03b1_1027_: *mut leanh::LeanObject,
    mut v_t_1028_: *mut leanh::LeanObject,
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_a_1031_: *mut leanh::LeanObject,
    mut v_a_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ =
        l_Lean_Meta_MetaM_asTask___redArg(v_t_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
    return v___x_1034_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask___boxed(
    mut v_00_u03b1_1035_: *mut leanh::LeanObject,
    mut v_t_1036_: *mut leanh::LeanObject,
    mut v_a_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lean_Meta_MetaM_asTask(
        v_00_u03b1_1035_,
        v_t_1036_,
        v_a_1037_,
        v_a_1038_,
        v_a_1039_,
        v_a_1040_,
    );
    leanh::lean_dec(v_a_1040_);
    leanh::lean_dec_ref(v_a_1039_);
    leanh::lean_dec(v_a_1038_);
    leanh::lean_dec_ref(v_a_1037_);
    return v_res_1042_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask_x27___redArg(
    mut v_t_1043_: *mut leanh::LeanObject,
    mut v_a_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v_snd_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_a_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1049_ = l_Lean_Meta_MetaM_asTask___redArg(
                    v_t_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_,
                );
                if leanh::lean_obj_tag(v___x_1049_) == 0 {
                    v_a_1050_ = leanh::lean_ctor_get(v___x_1049_, 0);
                    v_isSharedCheck_1058_ = (!leanh::lean_is_exclusive(v___x_1049_)) as u8;
                    if v_isSharedCheck_1058_ == 0 {
                        v___x_1052_ = v___x_1049_;
                        v_isShared_1053_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1050_);
                        leanh::lean_dec(v___x_1049_);
                        v___x_1052_ = leanh::lean_box(0);
                        v_isShared_1053_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1059_ = leanh::lean_ctor_get(v___x_1049_, 0);
                    v_isSharedCheck_1066_ = (!leanh::lean_is_exclusive(v___x_1049_)) as u8;
                    if v_isSharedCheck_1066_ == 0 {
                        v___x_1061_ = v___x_1049_;
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1059_);
                        leanh::lean_dec(v___x_1049_);
                        v___x_1061_ = leanh::lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1054_ = leanh::lean_ctor_get(v_a_1050_, 1);
                leanh::lean_inc(v_snd_1054_);
                leanh::lean_dec(v_a_1050_);
                if v_isShared_1053_ == 0 {
                    leanh::lean_ctor_set(v___x_1052_, 0, v_snd_1054_);
                    v___x_1056_ = v___x_1052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_snd_1054_);
                    v___x_1056_ = v_reuseFailAlloc_1057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1056_;
            }
            3 => {
                if v_isShared_1062_ == 0 {
                    v___x_1064_ = v___x_1061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
                    v___x_1064_ = v_reuseFailAlloc_1065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_asTask_x27___redArg___boxed(
    mut v_t_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Lean_Meta_MetaM_asTask_x27___redArg(
        v_t_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_,
    );
    leanh::lean_dec(v_a_1071_);
    leanh::lean_dec_ref(v_a_1070_);
    leanh::lean_dec(v_a_1069_);
    leanh::lean_dec_ref(v_a_1068_);
    return v_res_1073_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask_x27(
    mut v_00_u03b1_1074_: *mut leanh::LeanObject,
    mut v_t_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
    mut v_a_1077_: *mut leanh::LeanObject,
    mut v_a_1078_: *mut leanh::LeanObject,
    mut v_a_1079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_Meta_MetaM_asTask_x27___redArg(
        v_t_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_,
    );
    return v___x_1081_;
}
pub unsafe fn l_Lean_Meta_MetaM_asTask_x27___boxed(
    mut v_00_u03b1_1082_: *mut leanh::LeanObject,
    mut v_t_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_a_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Lean_Meta_MetaM_asTask_x27(
        v_00_u03b1_1082_,
        v_t_1083_,
        v_a_1084_,
        v_a_1085_,
        v_a_1086_,
        v_a_1087_,
    );
    leanh::lean_dec(v_a_1087_);
    leanh::lean_dec_ref(v_a_1086_);
    leanh::lean_dec(v_a_1085_);
    leanh::lean_dec_ref(v_a_1084_);
    return v_res_1089_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(
    mut v_c_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
    mut v___y_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v_fst_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_a_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1096_);
                leanh::lean_inc_ref(v___y_1095_);
                leanh::lean_inc(v___y_1094_);
                leanh::lean_inc_ref(v___y_1093_);
                v___x_1098_ = leanh::lean_apply_5(
                    v_c_1090_,
                    v___y_1093_,
                    v___y_1094_,
                    v___y_1095_,
                    v___y_1096_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1098_) == 0 {
                    v_a_1099_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1109_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1101_ = v___x_1098_;
                        v_isShared_1102_ = v_isSharedCheck_1109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1099_);
                        leanh::lean_dec(v___x_1098_);
                        v___x_1101_ = leanh::lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1109_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1110_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1117_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1117_ == 0 {
                        v___x_1112_ = v___x_1098_;
                        v_isShared_1113_ = v_isSharedCheck_1117_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1110_);
                        leanh::lean_dec(v___x_1098_);
                        v___x_1112_ = leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1117_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1103_ = leanh::lean_ctor_get(v_a_1099_, 0);
                leanh::lean_inc(v_fst_1103_);
                v_snd_1104_ = leanh::lean_ctor_get(v_a_1099_, 1);
                leanh::lean_inc(v_snd_1104_);
                leanh::lean_dec(v_a_1099_);
                v___x_1105_ = lean_st_ref_set(v___y_1092_, v_snd_1104_);
                if v_isShared_1102_ == 0 {
                    leanh::lean_ctor_set(v___x_1101_, 0, v_fst_1103_);
                    v___x_1107_ = v___x_1101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1103_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1107_;
            }
            3 => {
                if v_isShared_1113_ == 0 {
                    v___x_1115_ = v___x_1112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
                    v___x_1115_ = v_reuseFailAlloc_1116_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed(
    mut v_c_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(
        v_c_1118_,
        v___y_1119_,
        v___y_1120_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
    );
    leanh::lean_dec(v___y_1124_);
    leanh::lean_dec_ref(v___y_1123_);
    leanh::lean_dec(v___y_1122_);
    leanh::lean_dec_ref(v___y_1121_);
    leanh::lean_dec(v___y_1120_);
    leanh::lean_dec_ref(v___y_1119_);
    return v_res_1126_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask___redArg(
    mut v_t_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
    mut v_a_1130_: *mut leanh::LeanObject,
    mut v_a_1131_: *mut leanh::LeanObject,
    mut v_a_1132_: *mut leanh::LeanObject,
    mut v_a_1133_: *mut leanh::LeanObject,
    mut v_a_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1142_: u8 = 0;
    let mut v_fst_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___f_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_a_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_st_ref_get(v_a_1130_);
                leanh::lean_inc_ref(v_a_1129_);
                v___x_1137_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_TermElabM_run___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                leanh::lean_closure_set(v___x_1137_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1137_, 1, v_t_1128_);
                leanh::lean_closure_set(v___x_1137_, 2, v_a_1129_);
                leanh::lean_closure_set(v___x_1137_, 3, v___x_1136_);
                v___x_1138_ = l_Lean_Meta_MetaM_asTask___redArg(
                    v___x_1137_,
                    v_a_1131_,
                    v_a_1132_,
                    v_a_1133_,
                    v_a_1134_,
                );
                if leanh::lean_obj_tag(v___x_1138_) == 0 {
                    v_a_1139_ = leanh::lean_ctor_get(v___x_1138_, 0);
                    v_isSharedCheck_1159_ = (!leanh::lean_is_exclusive(v___x_1138_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v___x_1141_ = v___x_1138_;
                        v_isShared_1142_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1139_);
                        leanh::lean_dec(v___x_1138_);
                        v___x_1141_ = leanh::lean_box(0);
                        v_isShared_1142_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1160_ = leanh::lean_ctor_get(v___x_1138_, 0);
                    v_isSharedCheck_1167_ = (!leanh::lean_is_exclusive(v___x_1138_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1162_ = v___x_1138_;
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1160_);
                        leanh::lean_dec(v___x_1138_);
                        v___x_1162_ = leanh::lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1143_ = leanh::lean_ctor_get(v_a_1139_, 0);
                v_snd_1144_ = leanh::lean_ctor_get(v_a_1139_, 1);
                v_isSharedCheck_1158_ = (!leanh::lean_is_exclusive(v_a_1139_)) as u8;
                if v_isSharedCheck_1158_ == 0 {
                    v___x_1146_ = v_a_1139_;
                    v_isShared_1147_ = v_isSharedCheck_1158_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1144_);
                    leanh::lean_inc(v_fst_1143_);
                    leanh::lean_dec(v_a_1139_);
                    v___x_1146_ = leanh::lean_box(0);
                    v_isShared_1147_ = v_isSharedCheck_1158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1148_ = l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0;
                v___x_1149_ = leanh::lean_unsigned_to_nat(0);
                v___x_1150_ = 1;
                v___x_1151_ = lean_task_map(v___f_1148_, v_snd_1144_, v___x_1149_, v___x_1150_);
                if v_isShared_1147_ == 0 {
                    leanh::lean_ctor_set(v___x_1146_, 1, v___x_1151_);
                    v___x_1153_ = v___x_1146_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_fst_1143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1151_);
                    v___x_1153_ = v_reuseFailAlloc_1157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1142_ == 0 {
                    leanh::lean_ctor_set(v___x_1141_, 0, v___x_1153_);
                    v___x_1155_ = v___x_1141_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
                    v___x_1155_ = v_reuseFailAlloc_1156_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1155_;
            }
            5 => {
                if v_isShared_1163_ == 0 {
                    v___x_1165_ = v___x_1162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask___redArg___boxed(
    mut v_t_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
    mut v_a_1171_: *mut leanh::LeanObject,
    mut v_a_1172_: *mut leanh::LeanObject,
    mut v_a_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
    mut v_a_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(
        v_t_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_,
    );
    leanh::lean_dec(v_a_1174_);
    leanh::lean_dec_ref(v_a_1173_);
    leanh::lean_dec(v_a_1172_);
    leanh::lean_dec_ref(v_a_1171_);
    leanh::lean_dec(v_a_1170_);
    leanh::lean_dec_ref(v_a_1169_);
    return v_res_1176_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask(
    mut v_00_u03b1_1177_: *mut leanh::LeanObject,
    mut v_t_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v_a_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
    mut v_a_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(
        v_t_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_,
    );
    return v___x_1186_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask___boxed(
    mut v_00_u03b1_1187_: *mut leanh::LeanObject,
    mut v_t_1188_: *mut leanh::LeanObject,
    mut v_a_1189_: *mut leanh::LeanObject,
    mut v_a_1190_: *mut leanh::LeanObject,
    mut v_a_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l_Lean_Elab_Term_TermElabM_asTask(
        v_00_u03b1_1187_,
        v_t_1188_,
        v_a_1189_,
        v_a_1190_,
        v_a_1191_,
        v_a_1192_,
        v_a_1193_,
        v_a_1194_,
    );
    leanh::lean_dec(v_a_1194_);
    leanh::lean_dec_ref(v_a_1193_);
    leanh::lean_dec(v_a_1192_);
    leanh::lean_dec_ref(v_a_1191_);
    leanh::lean_dec(v_a_1190_);
    leanh::lean_dec_ref(v_a_1189_);
    return v_res_1196_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(
    mut v_t_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v_snd_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_a_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1218_: u8 = 0;
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1205_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(
                    v_t_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_,
                );
                if leanh::lean_obj_tag(v___x_1205_) == 0 {
                    v_a_1206_ = leanh::lean_ctor_get(v___x_1205_, 0);
                    v_isSharedCheck_1214_ = (!leanh::lean_is_exclusive(v___x_1205_)) as u8;
                    if v_isSharedCheck_1214_ == 0 {
                        v___x_1208_ = v___x_1205_;
                        v_isShared_1209_ = v_isSharedCheck_1214_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1206_);
                        leanh::lean_dec(v___x_1205_);
                        v___x_1208_ = leanh::lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1214_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1215_ = leanh::lean_ctor_get(v___x_1205_, 0);
                    v_isSharedCheck_1222_ = (!leanh::lean_is_exclusive(v___x_1205_)) as u8;
                    if v_isSharedCheck_1222_ == 0 {
                        v___x_1217_ = v___x_1205_;
                        v_isShared_1218_ = v_isSharedCheck_1222_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1215_);
                        leanh::lean_dec(v___x_1205_);
                        v___x_1217_ = leanh::lean_box(0);
                        v_isShared_1218_ = v_isSharedCheck_1222_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1210_ = leanh::lean_ctor_get(v_a_1206_, 1);
                leanh::lean_inc(v_snd_1210_);
                leanh::lean_dec(v_a_1206_);
                if v_isShared_1209_ == 0 {
                    leanh::lean_ctor_set(v___x_1208_, 0, v_snd_1210_);
                    v___x_1212_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_snd_1210_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            3 => {
                if v_isShared_1218_ == 0 {
                    v___x_1220_ = v___x_1217_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
                    v___x_1220_ = v_reuseFailAlloc_1221_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask_x27___redArg___boxed(
    mut v_t_1223_: *mut leanh::LeanObject,
    mut v_a_1224_: *mut leanh::LeanObject,
    mut v_a_1225_: *mut leanh::LeanObject,
    mut v_a_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
    mut v_a_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(
        v_t_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_,
    );
    leanh::lean_dec(v_a_1229_);
    leanh::lean_dec_ref(v_a_1228_);
    leanh::lean_dec(v_a_1227_);
    leanh::lean_dec_ref(v_a_1226_);
    leanh::lean_dec(v_a_1225_);
    leanh::lean_dec_ref(v_a_1224_);
    return v_res_1231_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask_x27(
    mut v_00_u03b1_1232_: *mut leanh::LeanObject,
    mut v_t_1233_: *mut leanh::LeanObject,
    mut v_a_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(
        v_t_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_,
    );
    return v___x_1241_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_asTask_x27___boxed(
    mut v_00_u03b1_1242_: *mut leanh::LeanObject,
    mut v_t_1243_: *mut leanh::LeanObject,
    mut v_a_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Elab_Term_TermElabM_asTask_x27(
        v_00_u03b1_1242_,
        v_t_1243_,
        v_a_1244_,
        v_a_1245_,
        v_a_1246_,
        v_a_1247_,
        v_a_1248_,
        v_a_1249_,
    );
    leanh::lean_dec(v_a_1249_);
    leanh::lean_dec_ref(v_a_1248_);
    leanh::lean_dec(v_a_1247_);
    leanh::lean_dec_ref(v_a_1246_);
    leanh::lean_dec(v_a_1245_);
    leanh::lean_dec_ref(v_a_1244_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(
    mut v_val_1252_: *mut leanh::LeanObject,
    mut v_t_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1273_: u8 = 0;
    let mut v_a_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1262_ = lean_st_mk_ref(v_val_1252_);
                leanh::lean_inc(v___x_1262_);
                leanh::lean_inc_ref(v_a_1254_);
                v___x_1263_ = leanh::lean_apply_9(
                    v_t_1253_,
                    v_a_1254_,
                    v___x_1262_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                    v___y_1258_,
                    v___y_1259_,
                    v___y_1260_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1263_) == 0 {
                    v_a_1264_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1273_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1273_ == 0 {
                        v___x_1266_ = v___x_1263_;
                        v_isShared_1267_ = v_isSharedCheck_1273_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1264_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1266_ = leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1273_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1262_);
                    v_a_1274_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1281_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1281_ == 0 {
                        v___x_1276_ = v___x_1263_;
                        v_isShared_1277_ = v_isSharedCheck_1281_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1274_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1276_ = leanh::lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1281_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1268_ = lean_st_ref_get(v___x_1262_);
                leanh::lean_dec(v___x_1262_);
                v___x_1269_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1269_, 0, v_a_1264_);
                leanh::lean_ctor_set(v___x_1269_, 1, v___x_1268_);
                if v_isShared_1267_ == 0 {
                    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1269_);
                    v___x_1271_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
                    v___x_1271_ = v_reuseFailAlloc_1272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1271_;
            }
            3 => {
                if v_isShared_1277_ == 0 {
                    v___x_1279_ = v___x_1276_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
                    v___x_1279_ = v_reuseFailAlloc_1280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed(
    mut v_val_1282_: *mut leanh::LeanObject,
    mut v_t_1283_: *mut leanh::LeanObject,
    mut v_a_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
    mut v___y_1288_: *mut leanh::LeanObject,
    mut v___y_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(
        v_val_1282_,
        v_t_1283_,
        v_a_1284_,
        v___y_1285_,
        v___y_1286_,
        v___y_1287_,
        v___y_1288_,
        v___y_1289_,
        v___y_1290_,
    );
    leanh::lean_dec_ref(v_a_1284_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(
    mut v_c_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v_fst_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_a_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1301_);
                leanh::lean_inc_ref(v___y_1300_);
                leanh::lean_inc(v___y_1299_);
                leanh::lean_inc_ref(v___y_1298_);
                leanh::lean_inc(v___y_1297_);
                leanh::lean_inc_ref(v___y_1296_);
                v___x_1303_ = leanh::lean_apply_7(
                    v_c_1293_,
                    v___y_1296_,
                    v___y_1297_,
                    v___y_1298_,
                    v___y_1299_,
                    v___y_1300_,
                    v___y_1301_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1303_) == 0 {
                    v_a_1304_ = leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1314_ = (!leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1314_ == 0 {
                        v___x_1306_ = v___x_1303_;
                        v_isShared_1307_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1304_);
                        leanh::lean_dec(v___x_1303_);
                        v___x_1306_ = leanh::lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1315_ = leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1322_ = (!leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1322_ == 0 {
                        v___x_1317_ = v___x_1303_;
                        v_isShared_1318_ = v_isSharedCheck_1322_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1315_);
                        leanh::lean_dec(v___x_1303_);
                        v___x_1317_ = leanh::lean_box(0);
                        v_isShared_1318_ = v_isSharedCheck_1322_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1308_ = leanh::lean_ctor_get(v_a_1304_, 0);
                leanh::lean_inc(v_fst_1308_);
                v_snd_1309_ = leanh::lean_ctor_get(v_a_1304_, 1);
                leanh::lean_inc(v_snd_1309_);
                leanh::lean_dec(v_a_1304_);
                v___x_1310_ = lean_st_ref_set(v___y_1295_, v_snd_1309_);
                if v_isShared_1307_ == 0 {
                    leanh::lean_ctor_set(v___x_1306_, 0, v_fst_1308_);
                    v___x_1312_ = v___x_1306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_fst_1308_);
                    v___x_1312_ = v_reuseFailAlloc_1313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1312_;
            }
            3 => {
                if v_isShared_1318_ == 0 {
                    v___x_1320_ = v___x_1317_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
                    v___x_1320_ = v_reuseFailAlloc_1321_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed(
    mut v_c_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(
        v_c_1323_,
        v___y_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
        v___y_1329_,
        v___y_1330_,
        v___y_1331_,
    );
    leanh::lean_dec(v___y_1331_);
    leanh::lean_dec_ref(v___y_1330_);
    leanh::lean_dec(v___y_1329_);
    leanh::lean_dec_ref(v___y_1328_);
    leanh::lean_dec(v___y_1327_);
    leanh::lean_dec_ref(v___y_1326_);
    leanh::lean_dec(v___y_1325_);
    leanh::lean_dec_ref(v___y_1324_);
    return v_res_1333_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg(
    mut v_t_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v_fst_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___f_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1345_ = lean_st_ref_get(v_a_1337_);
                leanh::lean_inc_ref(v_a_1336_);
                v___f_1346_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    3,
                );
                leanh::lean_closure_set(v___f_1346_, 0, v___x_1345_);
                leanh::lean_closure_set(v___f_1346_, 1, v_t_1335_);
                leanh::lean_closure_set(v___f_1346_, 2, v_a_1336_);
                v___x_1347_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(
                    v___f_1346_,
                    v_a_1338_,
                    v_a_1339_,
                    v_a_1340_,
                    v_a_1341_,
                    v_a_1342_,
                    v_a_1343_,
                );
                if leanh::lean_obj_tag(v___x_1347_) == 0 {
                    v_a_1348_ = leanh::lean_ctor_get(v___x_1347_, 0);
                    v_isSharedCheck_1368_ = (!leanh::lean_is_exclusive(v___x_1347_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1350_ = v___x_1347_;
                        v_isShared_1351_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1348_);
                        leanh::lean_dec(v___x_1347_);
                        v___x_1350_ = leanh::lean_box(0);
                        v_isShared_1351_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1369_ = leanh::lean_ctor_get(v___x_1347_, 0);
                    v_isSharedCheck_1376_ = (!leanh::lean_is_exclusive(v___x_1347_)) as u8;
                    if v_isSharedCheck_1376_ == 0 {
                        v___x_1371_ = v___x_1347_;
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1369_);
                        leanh::lean_dec(v___x_1347_);
                        v___x_1371_ = leanh::lean_box(0);
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1352_ = leanh::lean_ctor_get(v_a_1348_, 0);
                v_snd_1353_ = leanh::lean_ctor_get(v_a_1348_, 1);
                v_isSharedCheck_1367_ = (!leanh::lean_is_exclusive(v_a_1348_)) as u8;
                if v_isSharedCheck_1367_ == 0 {
                    v___x_1355_ = v_a_1348_;
                    v_isShared_1356_ = v_isSharedCheck_1367_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1353_);
                    leanh::lean_inc(v_fst_1352_);
                    leanh::lean_dec(v_a_1348_);
                    v___x_1355_ = leanh::lean_box(0);
                    v_isShared_1356_ = v_isSharedCheck_1367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1357_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0;
                v___x_1358_ = leanh::lean_unsigned_to_nat(8);
                v___x_1359_ = 0;
                v___x_1360_ = lean_task_map(v___f_1357_, v_snd_1353_, v___x_1358_, v___x_1359_);
                if v_isShared_1356_ == 0 {
                    leanh::lean_ctor_set(v___x_1355_, 1, v___x_1360_);
                    v___x_1362_ = v___x_1355_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_fst_1352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1360_);
                    v___x_1362_ = v_reuseFailAlloc_1366_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1351_ == 0 {
                    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1362_);
                    v___x_1364_ = v___x_1350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
                    v___x_1364_ = v_reuseFailAlloc_1365_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1364_;
            }
            5 => {
                if v_isShared_1372_ == 0 {
                    v___x_1374_ = v___x_1371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___redArg___boxed(
    mut v_t_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(
        v_t_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_,
        v_a_1385_,
    );
    leanh::lean_dec(v_a_1385_);
    leanh::lean_dec_ref(v_a_1384_);
    leanh::lean_dec(v_a_1383_);
    leanh::lean_dec_ref(v_a_1382_);
    leanh::lean_dec(v_a_1381_);
    leanh::lean_dec_ref(v_a_1380_);
    leanh::lean_dec(v_a_1379_);
    leanh::lean_dec_ref(v_a_1378_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask(
    mut v_00_u03b1_1388_: *mut leanh::LeanObject,
    mut v_t_1389_: *mut leanh::LeanObject,
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
    mut v_a_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(
        v_t_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_,
        v_a_1397_,
    );
    return v___x_1399_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask___boxed(
    mut v_00_u03b1_1400_: *mut leanh::LeanObject,
    mut v_t_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
    mut v_a_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_Elab_Tactic_TacticM_asTask(
        v_00_u03b1_1400_,
        v_t_1401_,
        v_a_1402_,
        v_a_1403_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
        v_a_1407_,
        v_a_1408_,
        v_a_1409_,
    );
    leanh::lean_dec(v_a_1409_);
    leanh::lean_dec_ref(v_a_1408_);
    leanh::lean_dec(v_a_1407_);
    leanh::lean_dec_ref(v_a_1406_);
    leanh::lean_dec(v_a_1405_);
    leanh::lean_dec_ref(v_a_1404_);
    leanh::lean_dec(v_a_1403_);
    leanh::lean_dec_ref(v_a_1402_);
    return v_res_1411_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(
    mut v_t_1412_: *mut leanh::LeanObject,
    mut v_a_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v_snd_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut v_a_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1422_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(
                    v_t_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_,
                    v_a_1419_, v_a_1420_,
                );
                if leanh::lean_obj_tag(v___x_1422_) == 0 {
                    v_a_1423_ = leanh::lean_ctor_get(v___x_1422_, 0);
                    v_isSharedCheck_1431_ = (!leanh::lean_is_exclusive(v___x_1422_)) as u8;
                    if v_isSharedCheck_1431_ == 0 {
                        v___x_1425_ = v___x_1422_;
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1423_);
                        leanh::lean_dec(v___x_1422_);
                        v___x_1425_ = leanh::lean_box(0);
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1432_ = leanh::lean_ctor_get(v___x_1422_, 0);
                    v_isSharedCheck_1439_ = (!leanh::lean_is_exclusive(v___x_1422_)) as u8;
                    if v_isSharedCheck_1439_ == 0 {
                        v___x_1434_ = v___x_1422_;
                        v_isShared_1435_ = v_isSharedCheck_1439_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1432_);
                        leanh::lean_dec(v___x_1422_);
                        v___x_1434_ = leanh::lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1439_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1427_ = leanh::lean_ctor_get(v_a_1423_, 1);
                leanh::lean_inc(v_snd_1427_);
                leanh::lean_dec(v_a_1423_);
                if v_isShared_1426_ == 0 {
                    leanh::lean_ctor_set(v___x_1425_, 0, v_snd_1427_);
                    v___x_1429_ = v___x_1425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_snd_1427_);
                    v___x_1429_ = v_reuseFailAlloc_1430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1429_;
            }
            3 => {
                if v_isShared_1435_ == 0 {
                    v___x_1437_ = v___x_1434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
                    v___x_1437_ = v_reuseFailAlloc_1438_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg___boxed(
    mut v_t_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
    mut v_a_1442_: *mut leanh::LeanObject,
    mut v_a_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
    mut v_a_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_a_1448_: *mut leanh::LeanObject,
    mut v_a_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(
        v_t_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_,
        v_a_1448_,
    );
    leanh::lean_dec(v_a_1448_);
    leanh::lean_dec_ref(v_a_1447_);
    leanh::lean_dec(v_a_1446_);
    leanh::lean_dec_ref(v_a_1445_);
    leanh::lean_dec(v_a_1444_);
    leanh::lean_dec_ref(v_a_1443_);
    leanh::lean_dec(v_a_1442_);
    leanh::lean_dec_ref(v_a_1441_);
    return v_res_1450_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask_x27(
    mut v_00_u03b1_1451_: *mut leanh::LeanObject,
    mut v_t_1452_: *mut leanh::LeanObject,
    mut v_a_1453_: *mut leanh::LeanObject,
    mut v_a_1454_: *mut leanh::LeanObject,
    mut v_a_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(
        v_t_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_,
        v_a_1460_,
    );
    return v___x_1462_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_asTask_x27___boxed(
    mut v_00_u03b1_1463_: *mut leanh::LeanObject,
    mut v_t_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
    mut v_a_1472_: *mut leanh::LeanObject,
    mut v_a_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Lean_Elab_Tactic_TacticM_asTask_x27(
        v_00_u03b1_1463_,
        v_t_1464_,
        v_a_1465_,
        v_a_1466_,
        v_a_1467_,
        v_a_1468_,
        v_a_1469_,
        v_a_1470_,
        v_a_1471_,
        v_a_1472_,
    );
    leanh::lean_dec(v_a_1472_);
    leanh::lean_dec_ref(v_a_1471_);
    leanh::lean_dec(v_a_1470_);
    leanh::lean_dec_ref(v_a_1469_);
    leanh::lean_dec(v_a_1468_);
    leanh::lean_dec_ref(v_a_1467_);
    leanh::lean_dec(v_a_1466_);
    leanh::lean_dec_ref(v_a_1465_);
    return v_res_1474_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Task(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Task(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Task(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Task(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Task(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Task(builtin);
}