// Lean compiler output
// Module: Init.Control.State
// Imports: Init.Control.Except
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
pub static l_StateT_run_x27___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateT_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateT_run_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_StateT_instMonadFunctor___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateT_instMonadFunctor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateT_instMonadFunctor___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadAttachStateTOfMonad___redArg___closed__0_value:
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
    m_fun: l_instMonadAttachStateTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadAttachStateTOfMonad___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadAttachStateTOfMonad___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_StateT_mk___redArg(
    mut v_x_763_: *mut leanh::LeanObject,
    mut v_a_764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = leanh::lean_apply_1(v_x_763_, v_a_764_);
    return v___x_765_;
}
pub unsafe fn l_StateT_mk(
    mut v_00_u03c3_766_: *mut leanh::LeanObject,
    mut v_m_767_: *mut leanh::LeanObject,
    mut v_00_u03b1_768_: *mut leanh::LeanObject,
    mut v_x_769_: *mut leanh::LeanObject,
    mut v_a_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = leanh::lean_apply_1(v_x_769_, v_a_770_);
    return v___x_771_;
}
pub unsafe fn l_StateT_run___redArg(
    mut v_x_772_: *mut leanh::LeanObject,
    mut v_s_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = leanh::lean_apply_1(v_x_772_, v_s_773_);
    return v___x_774_;
}
pub unsafe fn l_StateT_run(
    mut v_00_u03c3_775_: *mut leanh::LeanObject,
    mut v_m_776_: *mut leanh::LeanObject,
    mut v_00_u03b1_777_: *mut leanh::LeanObject,
    mut v_x_778_: *mut leanh::LeanObject,
    mut v_s_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = leanh::lean_apply_1(v_x_778_, v_s_779_);
    return v___x_780_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0(
    mut v_x_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_782_ = leanh::lean_ctor_get(v_x_781_, 0);
    leanh::lean_inc(v_fst_782_);
    return v_fst_782_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0___boxed(
    mut v_x_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_StateT_run_x27___redArg___lam__0(v_x_783_);
    leanh::lean_dec_ref(v_x_783_);
    return v_res_784_;
}
pub unsafe fn l_StateT_run_x27___redArg(
    mut v_inst_786_: *mut leanh::LeanObject,
    mut v_x_787_: *mut leanh::LeanObject,
    mut v_s_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_789_ = leanh::lean_ctor_get(v_inst_786_, 0);
    leanh::lean_inc(v_map_789_);
    leanh::lean_dec_ref(v_inst_786_);
    v___f_790_ = l_StateT_run_x27___redArg___closed__0;
    v___x_791_ = leanh::lean_apply_1(v_x_787_, v_s_788_);
    v___x_792_ = leanh::lean_apply_4(
        v_map_789_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_790_,
        v___x_791_,
    );
    return v___x_792_;
}
pub unsafe fn l_StateT_run_x27(
    mut v_00_u03c3_793_: *mut leanh::LeanObject,
    mut v_m_794_: *mut leanh::LeanObject,
    mut v_inst_795_: *mut leanh::LeanObject,
    mut v_00_u03b1_796_: *mut leanh::LeanObject,
    mut v_x_797_: *mut leanh::LeanObject,
    mut v_s_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_799_ = leanh::lean_ctor_get(v_inst_795_, 0);
    leanh::lean_inc(v_map_799_);
    leanh::lean_dec_ref(v_inst_795_);
    v___f_800_ = l_StateT_run_x27___redArg___closed__0;
    v___x_801_ = leanh::lean_apply_1(v_x_797_, v_s_798_);
    v___x_802_ = leanh::lean_apply_4(
        v_map_799_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_800_,
        v___x_801_,
    );
    return v___x_802_;
}
pub unsafe fn l_StateT_pure___redArg(
    mut v_inst_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_s_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_809_: u8 = 0;
    let mut v_toPure_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_unused_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_806_ = leanh::lean_ctor_get(v_inst_803_, 0);
                v_isSharedCheck_815_ = (!leanh::lean_is_exclusive(v_inst_803_)) as u8;
                if v_isSharedCheck_815_ == 0 {
                    v_unused_816_ = leanh::lean_ctor_get(v_inst_803_, 1);
                    leanh::lean_dec(v_unused_816_);
                    v___x_808_ = v_inst_803_;
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_806_);
                    leanh::lean_dec(v_inst_803_);
                    v___x_808_ = leanh::lean_box(0);
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_810_ = leanh::lean_ctor_get(v_toApplicative_806_, 1);
                leanh::lean_inc(v_toPure_810_);
                leanh::lean_dec_ref(v_toApplicative_806_);
                if v_isShared_809_ == 0 {
                    leanh::lean_ctor_set(v___x_808_, 1, v_s_805_);
                    leanh::lean_ctor_set(v___x_808_, 0, v_a_804_);
                    v___x_812_ = v___x_808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_814_, 1, v_s_805_);
                    v___x_812_ = v_reuseFailAlloc_814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_813_ = leanh::lean_apply_2(
                    v_toPure_810_,
                    leanh::lean_box(0),
                    v___x_812_,
                );
                return v___x_813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_pure(
    mut v_00_u03c3_817_: *mut leanh::LeanObject,
    mut v_m_818_: *mut leanh::LeanObject,
    mut v_inst_819_: *mut leanh::LeanObject,
    mut v_00_u03b1_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_s_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_unused_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_823_ = leanh::lean_ctor_get(v_inst_819_, 0);
                v_isSharedCheck_832_ = (!leanh::lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_832_ == 0 {
                    v_unused_833_ = leanh::lean_ctor_get(v_inst_819_, 1);
                    leanh::lean_dec(v_unused_833_);
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_823_);
                    leanh::lean_dec(v_inst_819_);
                    v___x_825_ = leanh::lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = leanh::lean_ctor_get(v_toApplicative_823_, 1);
                leanh::lean_inc(v_toPure_827_);
                leanh::lean_dec_ref(v_toApplicative_823_);
                if v_isShared_826_ == 0 {
                    leanh::lean_ctor_set(v___x_825_, 1, v_s_822_);
                    leanh::lean_ctor_set(v___x_825_, 0, v_a_821_);
                    v___x_829_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_831_, 1, v_s_822_);
                    v___x_829_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_830_ = leanh::lean_apply_2(
                    v_toPure_827_,
                    leanh::lean_box(0),
                    v___x_829_,
                );
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_bind___redArg___lam__0(
    mut v_f_834_: *mut leanh::LeanObject,
    mut v_____x_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_836_ = leanh::lean_ctor_get(v_____x_835_, 0);
    leanh::lean_inc(v_fst_836_);
    v_snd_837_ = leanh::lean_ctor_get(v_____x_835_, 1);
    leanh::lean_inc(v_snd_837_);
    leanh::lean_dec_ref(v_____x_835_);
    v___x_838_ = leanh::lean_apply_2(v_f_834_, v_fst_836_, v_snd_837_);
    return v___x_838_;
}
pub unsafe fn l_StateT_bind___redArg(
    mut v_inst_839_: *mut leanh::LeanObject,
    mut v_x_840_: *mut leanh::LeanObject,
    mut v_f_841_: *mut leanh::LeanObject,
    mut v_s_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_843_ = leanh::lean_ctor_get(v_inst_839_, 1);
    leanh::lean_inc(v_toBind_843_);
    leanh::lean_dec_ref(v_inst_839_);
    v___f_844_ = leanh::lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_844_, 0, v_f_841_);
    v___x_845_ = leanh::lean_apply_1(v_x_840_, v_s_842_);
    v___x_846_ = leanh::lean_apply_4(
        v_toBind_843_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_845_,
        v___f_844_,
    );
    return v___x_846_;
}
pub unsafe fn l_StateT_bind(
    mut v_00_u03c3_847_: *mut leanh::LeanObject,
    mut v_m_848_: *mut leanh::LeanObject,
    mut v_inst_849_: *mut leanh::LeanObject,
    mut v_00_u03b1_850_: *mut leanh::LeanObject,
    mut v_00_u03b2_851_: *mut leanh::LeanObject,
    mut v_x_852_: *mut leanh::LeanObject,
    mut v_f_853_: *mut leanh::LeanObject,
    mut v_s_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_855_ = leanh::lean_ctor_get(v_inst_849_, 1);
    leanh::lean_inc(v_toBind_855_);
    leanh::lean_dec_ref(v_inst_849_);
    v___f_856_ = leanh::lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_856_, 0, v_f_853_);
    v___x_857_ = leanh::lean_apply_1(v_x_852_, v_s_854_);
    v___x_858_ = leanh::lean_apply_4(
        v_toBind_855_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_857_,
        v___f_856_,
    );
    return v___x_858_;
}
pub unsafe fn l_StateT_map___redArg___lam__0(
    mut v_f_859_: *mut leanh::LeanObject,
    mut v_toPure_860_: *mut leanh::LeanObject,
    mut v_____x_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_862_ = leanh::lean_ctor_get(v_____x_861_, 0);
                v_snd_863_ = leanh::lean_ctor_get(v_____x_861_, 1);
                v_isSharedCheck_872_ = (!leanh::lean_is_exclusive(v_____x_861_)) as u8;
                if v_isSharedCheck_872_ == 0 {
                    v___x_865_ = v_____x_861_;
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_863_);
                    leanh::lean_inc(v_fst_862_);
                    leanh::lean_dec(v_____x_861_);
                    v___x_865_ = leanh::lean_box(0);
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_867_ = leanh::lean_apply_1(v_f_859_, v_fst_862_);
                if v_isShared_866_ == 0 {
                    leanh::lean_ctor_set(v___x_865_, 0, v___x_867_);
                    v___x_869_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_863_);
                    v___x_869_ = v_reuseFailAlloc_871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_870_ = leanh::lean_apply_2(
                    v_toPure_860_,
                    leanh::lean_box(0),
                    v___x_869_,
                );
                return v___x_870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_map___redArg(
    mut v_inst_873_: *mut leanh::LeanObject,
    mut v_f_874_: *mut leanh::LeanObject,
    mut v_x_875_: *mut leanh::LeanObject,
    mut v_s_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_877_ = leanh::lean_ctor_get(v_inst_873_, 0);
    leanh::lean_inc_ref(v_toApplicative_877_);
    v_toBind_878_ = leanh::lean_ctor_get(v_inst_873_, 1);
    leanh::lean_inc(v_toBind_878_);
    leanh::lean_dec_ref(v_inst_873_);
    v_toPure_879_ = leanh::lean_ctor_get(v_toApplicative_877_, 1);
    leanh::lean_inc(v_toPure_879_);
    leanh::lean_dec_ref(v_toApplicative_877_);
    v___x_880_ = leanh::lean_apply_1(v_x_875_, v_s_876_);
    v___f_881_ = leanh::lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_881_, 0, v_f_874_);
    leanh::lean_closure_set(v___f_881_, 1, v_toPure_879_);
    v___x_882_ = leanh::lean_apply_4(
        v_toBind_878_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_880_,
        v___f_881_,
    );
    return v___x_882_;
}
pub unsafe fn l_StateT_map(
    mut v_00_u03c3_883_: *mut leanh::LeanObject,
    mut v_m_884_: *mut leanh::LeanObject,
    mut v_inst_885_: *mut leanh::LeanObject,
    mut v_00_u03b1_886_: *mut leanh::LeanObject,
    mut v_00_u03b2_887_: *mut leanh::LeanObject,
    mut v_f_888_: *mut leanh::LeanObject,
    mut v_x_889_: *mut leanh::LeanObject,
    mut v_s_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_891_ = leanh::lean_ctor_get(v_inst_885_, 0);
    leanh::lean_inc_ref(v_toApplicative_891_);
    v_toBind_892_ = leanh::lean_ctor_get(v_inst_885_, 1);
    leanh::lean_inc(v_toBind_892_);
    leanh::lean_dec_ref(v_inst_885_);
    v_toPure_893_ = leanh::lean_ctor_get(v_toApplicative_891_, 1);
    leanh::lean_inc(v_toPure_893_);
    leanh::lean_dec_ref(v_toApplicative_891_);
    v___x_894_ = leanh::lean_apply_1(v_x_889_, v_s_890_);
    v___f_895_ = leanh::lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_895_, 0, v_f_888_);
    leanh::lean_closure_set(v___f_895_, 1, v_toPure_893_);
    v___x_896_ = leanh::lean_apply_4(
        v_toBind_892_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_894_,
        v___f_895_,
    );
    return v___x_896_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__0(
    mut v___y_897_: *mut leanh::LeanObject,
    mut v_toPure_898_: *mut leanh::LeanObject,
    mut v_____x_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_900_ = leanh::lean_ctor_get(v_____x_899_, 1);
                v_isSharedCheck_908_ = (!leanh::lean_is_exclusive(v_____x_899_)) as u8;
                if v_isSharedCheck_908_ == 0 {
                    v_unused_909_ = leanh::lean_ctor_get(v_____x_899_, 0);
                    leanh::lean_dec(v_unused_909_);
                    v___x_902_ = v_____x_899_;
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_900_);
                    leanh::lean_dec(v_____x_899_);
                    v___x_902_ = leanh::lean_box(0);
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_903_ == 0 {
                    leanh::lean_ctor_set(v___x_902_, 0, v___y_897_);
                    v___x_905_ = v___x_902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___y_897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_900_);
                    v___x_905_ = v_reuseFailAlloc_907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_906_ = leanh::lean_apply_2(
                    v_toPure_898_,
                    leanh::lean_box(0),
                    v___x_905_,
                );
                return v___x_906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__1(
    mut v_inst_910_: *mut leanh::LeanObject,
    mut v_00_u03b1_911_: *mut leanh::LeanObject,
    mut v_00_u03b2_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_916_ = leanh::lean_ctor_get(v_inst_910_, 0);
    leanh::lean_inc_ref(v_toApplicative_916_);
    v_toBind_917_ = leanh::lean_ctor_get(v_inst_910_, 1);
    leanh::lean_inc(v_toBind_917_);
    leanh::lean_dec_ref(v_inst_910_);
    v_toPure_918_ = leanh::lean_ctor_get(v_toApplicative_916_, 1);
    leanh::lean_inc(v_toPure_918_);
    leanh::lean_dec_ref(v_toApplicative_916_);
    v___x_919_ = leanh::lean_apply_1(v___y_914_, v___y_915_);
    v___f_920_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_920_, 0, v___y_913_);
    leanh::lean_closure_set(v___f_920_, 1, v_toPure_918_);
    v___x_921_ = leanh::lean_apply_4(
        v_toBind_917_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_919_,
        v___f_920_,
    );
    return v___x_921_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__2(
    mut v_fst_922_: *mut leanh::LeanObject,
    mut v_toPure_923_: *mut leanh::LeanObject,
    mut v_____x_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_925_ = leanh::lean_ctor_get(v_____x_924_, 0);
                v_snd_926_ = leanh::lean_ctor_get(v_____x_924_, 1);
                v_isSharedCheck_935_ = (!leanh::lean_is_exclusive(v_____x_924_)) as u8;
                if v_isSharedCheck_935_ == 0 {
                    v___x_928_ = v_____x_924_;
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_926_);
                    leanh::lean_inc(v_fst_925_);
                    leanh::lean_dec(v_____x_924_);
                    v___x_928_ = leanh::lean_box(0);
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_930_ = leanh::lean_apply_1(v_fst_922_, v_fst_925_);
                if v_isShared_929_ == 0 {
                    leanh::lean_ctor_set(v___x_928_, 0, v___x_930_);
                    v___x_932_ = v___x_928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_934_, 1, v_snd_926_);
                    v___x_932_ = v_reuseFailAlloc_934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_933_ = leanh::lean_apply_2(
                    v_toPure_923_,
                    leanh::lean_box(0),
                    v___x_932_,
                );
                return v___x_933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__3(
    mut v_toApplicative_936_: *mut leanh::LeanObject,
    mut v_x_937_: *mut leanh::LeanObject,
    mut v_toBind_938_: *mut leanh::LeanObject,
    mut v_____x_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_940_ = leanh::lean_ctor_get(v_____x_939_, 0);
    leanh::lean_inc(v_fst_940_);
    v_snd_941_ = leanh::lean_ctor_get(v_____x_939_, 1);
    leanh::lean_inc(v_snd_941_);
    leanh::lean_dec_ref(v_____x_939_);
    v_toPure_942_ = leanh::lean_ctor_get(v_toApplicative_936_, 1);
    leanh::lean_inc(v_toPure_942_);
    leanh::lean_dec_ref(v_toApplicative_936_);
    v___x_943_ = leanh::lean_box(0);
    v___x_944_ = leanh::lean_apply_2(v_x_937_, v___x_943_, v_snd_941_);
    v___f_945_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_945_, 0, v_fst_940_);
    leanh::lean_closure_set(v___f_945_, 1, v_toPure_942_);
    v___x_946_ = leanh::lean_apply_4(
        v_toBind_938_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_944_,
        v___f_945_,
    );
    return v___x_946_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__4(
    mut v_inst_947_: *mut leanh::LeanObject,
    mut v_00_u03b1_948_: *mut leanh::LeanObject,
    mut v_00_u03b2_949_: *mut leanh::LeanObject,
    mut v_f_950_: *mut leanh::LeanObject,
    mut v_x_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_953_ = leanh::lean_ctor_get(v_inst_947_, 0);
    leanh::lean_inc_ref(v_toApplicative_953_);
    v_toBind_954_ = leanh::lean_ctor_get(v_inst_947_, 1);
    leanh::lean_inc_n(v_toBind_954_, 2);
    leanh::lean_dec_ref(v_inst_947_);
    v___f_955_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_955_, 0, v_toApplicative_953_);
    leanh::lean_closure_set(v___f_955_, 1, v_x_951_);
    leanh::lean_closure_set(v___f_955_, 2, v_toBind_954_);
    v___x_956_ = leanh::lean_apply_1(v_f_950_, v___y_952_);
    v___x_957_ = leanh::lean_apply_4(
        v_toBind_954_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_956_,
        v___f_955_,
    );
    return v___x_957_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__5(
    mut v_toApplicative_958_: *mut leanh::LeanObject,
    mut v_fst_959_: *mut leanh::LeanObject,
    mut v_____x_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_toPure_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_unused_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_961_ = leanh::lean_ctor_get(v_____x_960_, 1);
                v_isSharedCheck_970_ = (!leanh::lean_is_exclusive(v_____x_960_)) as u8;
                if v_isSharedCheck_970_ == 0 {
                    v_unused_971_ = leanh::lean_ctor_get(v_____x_960_, 0);
                    leanh::lean_dec(v_unused_971_);
                    v___x_963_ = v_____x_960_;
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_961_);
                    leanh::lean_dec(v_____x_960_);
                    v___x_963_ = leanh::lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_965_ = leanh::lean_ctor_get(v_toApplicative_958_, 1);
                leanh::lean_inc(v_toPure_965_);
                leanh::lean_dec_ref(v_toApplicative_958_);
                if v_isShared_964_ == 0 {
                    leanh::lean_ctor_set(v___x_963_, 0, v_fst_959_);
                    v___x_967_ = v___x_963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_969_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_961_);
                    v___x_967_ = v_reuseFailAlloc_969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_968_ = leanh::lean_apply_2(
                    v_toPure_965_,
                    leanh::lean_box(0),
                    v___x_967_,
                );
                return v___x_968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__6(
    mut v_toApplicative_972_: *mut leanh::LeanObject,
    mut v_y_973_: *mut leanh::LeanObject,
    mut v_toBind_974_: *mut leanh::LeanObject,
    mut v_____x_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_976_ = leanh::lean_ctor_get(v_____x_975_, 0);
    leanh::lean_inc(v_fst_976_);
    v_snd_977_ = leanh::lean_ctor_get(v_____x_975_, 1);
    leanh::lean_inc(v_snd_977_);
    leanh::lean_dec_ref(v_____x_975_);
    v___f_978_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_978_, 0, v_toApplicative_972_);
    leanh::lean_closure_set(v___f_978_, 1, v_fst_976_);
    v___x_979_ = leanh::lean_box(0);
    v___x_980_ = leanh::lean_apply_2(v_y_973_, v___x_979_, v_snd_977_);
    v___x_981_ = leanh::lean_apply_4(
        v_toBind_974_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_980_,
        v___f_978_,
    );
    return v___x_981_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__7(
    mut v_inst_982_: *mut leanh::LeanObject,
    mut v_00_u03b1_983_: *mut leanh::LeanObject,
    mut v_00_u03b2_984_: *mut leanh::LeanObject,
    mut v_x_985_: *mut leanh::LeanObject,
    mut v_y_986_: *mut leanh::LeanObject,
    mut v___y_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_988_ = leanh::lean_ctor_get(v_inst_982_, 0);
    leanh::lean_inc_ref(v_toApplicative_988_);
    v_toBind_989_ = leanh::lean_ctor_get(v_inst_982_, 1);
    leanh::lean_inc_n(v_toBind_989_, 2);
    leanh::lean_dec_ref(v_inst_982_);
    v___f_990_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_990_, 0, v_toApplicative_988_);
    leanh::lean_closure_set(v___f_990_, 1, v_y_986_);
    leanh::lean_closure_set(v___f_990_, 2, v_toBind_989_);
    v___x_991_ = leanh::lean_apply_1(v_x_985_, v___y_987_);
    v___x_992_ = leanh::lean_apply_4(
        v_toBind_989_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_991_,
        v___f_990_,
    );
    return v___x_992_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__8(
    mut v_y_993_: *mut leanh::LeanObject,
    mut v_____x_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_995_ = leanh::lean_ctor_get(v_____x_994_, 1);
    leanh::lean_inc(v_snd_995_);
    leanh::lean_dec_ref(v_____x_994_);
    v___x_996_ = leanh::lean_box(0);
    v___x_997_ = leanh::lean_apply_2(v_y_993_, v___x_996_, v_snd_995_);
    return v___x_997_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__9(
    mut v_inst_998_: *mut leanh::LeanObject,
    mut v_00_u03b1_999_: *mut leanh::LeanObject,
    mut v_00_u03b2_1000_: *mut leanh::LeanObject,
    mut v_x_1001_: *mut leanh::LeanObject,
    mut v_y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1004_ = leanh::lean_ctor_get(v_inst_998_, 1);
    leanh::lean_inc(v_toBind_1004_);
    leanh::lean_dec_ref(v_inst_998_);
    v___f_1005_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1005_, 0, v_y_1002_);
    v___x_1006_ = leanh::lean_apply_1(v_x_1001_, v___y_1003_);
    v___x_1007_ = leanh::lean_apply_4(
        v_toBind_1004_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1006_,
        v___f_1005_,
    );
    return v___x_1007_;
}
pub unsafe fn l_StateT_instMonad___redArg(
    mut v_inst_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1008_, 6);
    v___f_1009_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1009_, 0, v_inst_1008_);
    v___f_1010_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1010_, 0, v_inst_1008_);
    v___f_1011_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1011_, 0, v_inst_1008_);
    v___f_1012_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1012_, 0, v_inst_1008_);
    v___x_1013_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1013_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1013_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1013_, 2, v_inst_1008_);
    v___x_1014_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1014_, 0, v___x_1013_);
    leanh::lean_ctor_set(v___x_1014_, 1, v___f_1009_);
    v___x_1015_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1015_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1015_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1015_, 2, v_inst_1008_);
    v___x_1016_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1016_, 0, v___x_1014_);
    leanh::lean_ctor_set(v___x_1016_, 1, v___x_1015_);
    leanh::lean_ctor_set(v___x_1016_, 2, v___f_1010_);
    leanh::lean_ctor_set(v___x_1016_, 3, v___f_1011_);
    leanh::lean_ctor_set(v___x_1016_, 4, v___f_1012_);
    v___x_1017_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1017_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1017_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1017_, 2, v_inst_1008_);
    v___x_1018_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1018_, 0, v___x_1016_);
    leanh::lean_ctor_set(v___x_1018_, 1, v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_StateT_instMonad(
    mut v_00_u03c3_1019_: *mut leanh::LeanObject,
    mut v_m_1020_: *mut leanh::LeanObject,
    mut v_inst_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1021_, 6);
    v___f_1022_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1022_, 0, v_inst_1021_);
    v___f_1023_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1023_, 0, v_inst_1021_);
    v___f_1024_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1024_, 0, v_inst_1021_);
    v___f_1025_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1025_, 0, v_inst_1021_);
    v___x_1026_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1026_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1026_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1026_, 2, v_inst_1021_);
    v___x_1027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    leanh::lean_ctor_set(v___x_1027_, 1, v___f_1022_);
    v___x_1028_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1028_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1028_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1028_, 2, v_inst_1021_);
    v___x_1029_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1029_, 0, v___x_1027_);
    leanh::lean_ctor_set(v___x_1029_, 1, v___x_1028_);
    leanh::lean_ctor_set(v___x_1029_, 2, v___f_1023_);
    leanh::lean_ctor_set(v___x_1029_, 3, v___f_1024_);
    leanh::lean_ctor_set(v___x_1029_, 4, v___f_1025_);
    v___x_1030_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1030_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1030_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1030_, 2, v_inst_1021_);
    v___x_1031_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    leanh::lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn l_StateT_orElse___redArg___lam__0(
    mut v_x_u2082_1032_: *mut leanh::LeanObject,
    mut v_s_1033_: *mut leanh::LeanObject,
    mut v_x_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = leanh::lean_box(0);
    v___x_1036_ = leanh::lean_apply_2(v_x_u2082_1032_, v___x_1035_, v_s_1033_);
    return v___x_1036_;
}
pub unsafe fn l_StateT_orElse___redArg(
    mut v_inst_1037_: *mut leanh::LeanObject,
    mut v_x_u2081_1038_: *mut leanh::LeanObject,
    mut v_x_u2082_1039_: *mut leanh::LeanObject,
    mut v_s_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1041_ = leanh::lean_ctor_get(v_inst_1037_, 2);
    leanh::lean_inc(v_orElse_1041_);
    leanh::lean_dec_ref(v_inst_1037_);
    leanh::lean_inc(v_s_1040_);
    v___f_1042_ = leanh::lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1042_, 0, v_x_u2082_1039_);
    leanh::lean_closure_set(v___f_1042_, 1, v_s_1040_);
    v___x_1043_ = leanh::lean_apply_1(v_x_u2081_1038_, v_s_1040_);
    v___x_1044_ = leanh::lean_apply_3(
        v_orElse_1041_,
        leanh::lean_box(0),
        v___x_1043_,
        v___f_1042_,
    );
    return v___x_1044_;
}
pub unsafe fn l_StateT_orElse(
    mut v_00_u03c3_1045_: *mut leanh::LeanObject,
    mut v_m_1046_: *mut leanh::LeanObject,
    mut v_inst_1047_: *mut leanh::LeanObject,
    mut v_00_u03b1_1048_: *mut leanh::LeanObject,
    mut v_x_u2081_1049_: *mut leanh::LeanObject,
    mut v_x_u2082_1050_: *mut leanh::LeanObject,
    mut v_s_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1052_ = leanh::lean_ctor_get(v_inst_1047_, 2);
    leanh::lean_inc(v_orElse_1052_);
    leanh::lean_dec_ref(v_inst_1047_);
    leanh::lean_inc(v_s_1051_);
    v___f_1053_ = leanh::lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1053_, 0, v_x_u2082_1050_);
    leanh::lean_closure_set(v___f_1053_, 1, v_s_1051_);
    v___x_1054_ = leanh::lean_apply_1(v_x_u2081_1049_, v_s_1051_);
    v___x_1055_ = leanh::lean_apply_3(
        v_orElse_1052_,
        leanh::lean_box(0),
        v___x_1054_,
        v___f_1053_,
    );
    return v___x_1055_;
}
pub unsafe fn l_StateT_failure___redArg(
    mut v_inst_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_1057_ = leanh::lean_ctor_get(v_inst_1056_, 1);
    leanh::lean_inc(v_failure_1057_);
    leanh::lean_dec_ref(v_inst_1056_);
    v___x_1058_ = leanh::lean_apply_1(v_failure_1057_, leanh::lean_box(0));
    return v___x_1058_;
}
pub unsafe fn l_StateT_failure(
    mut v_00_u03c3_1059_: *mut leanh::LeanObject,
    mut v_m_1060_: *mut leanh::LeanObject,
    mut v_inst_1061_: *mut leanh::LeanObject,
    mut v_00_u03b1_1062_: *mut leanh::LeanObject,
    mut v_x_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_1064_ = leanh::lean_ctor_get(v_inst_1061_, 1);
    leanh::lean_inc(v_failure_1064_);
    leanh::lean_dec_ref(v_inst_1061_);
    v___x_1065_ = leanh::lean_apply_1(v_failure_1064_, leanh::lean_box(0));
    return v___x_1065_;
}
pub unsafe fn l_StateT_failure___boxed(
    mut v_00_u03c3_1066_: *mut leanh::LeanObject,
    mut v_m_1067_: *mut leanh::LeanObject,
    mut v_inst_1068_: *mut leanh::LeanObject,
    mut v_00_u03b1_1069_: *mut leanh::LeanObject,
    mut v_x_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_StateT_failure(
        v_00_u03c3_1066_,
        v_m_1067_,
        v_inst_1068_,
        v_00_u03b1_1069_,
        v_x_1070_,
    );
    leanh::lean_dec(v_x_1070_);
    return v_res_1071_;
}
pub unsafe fn l_StateT_instAlternative___redArg(
    mut v_inst_1072_: *mut leanh::LeanObject,
    mut v_inst_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1072_, 5);
    v___f_1074_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1074_, 0, v_inst_1072_);
    v___f_1075_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1075_, 0, v_inst_1072_);
    v___f_1076_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1076_, 0, v_inst_1072_);
    v___f_1077_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1077_, 0, v_inst_1072_);
    v___x_1078_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1078_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1078_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1078_, 2, v_inst_1072_);
    v___x_1079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    leanh::lean_ctor_set(v___x_1079_, 1, v___f_1074_);
    v___x_1080_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1080_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1080_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1080_, 2, v_inst_1072_);
    v___x_1081_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1081_, 0, v___x_1079_);
    leanh::lean_ctor_set(v___x_1081_, 1, v___x_1080_);
    leanh::lean_ctor_set(v___x_1081_, 2, v___f_1075_);
    leanh::lean_ctor_set(v___x_1081_, 3, v___f_1076_);
    leanh::lean_ctor_set(v___x_1081_, 4, v___f_1077_);
    leanh::lean_inc_ref(v_inst_1073_);
    v___x_1082_ =
        leanh::lean_alloc_closure(l_StateT_failure___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_1082_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1082_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1082_, 2, v_inst_1073_);
    v___x_1083_ = leanh::lean_alloc_closure(l_StateT_orElse as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_1083_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1083_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1083_, 2, v_inst_1073_);
    v___x_1084_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1084_, 0, v___x_1081_);
    leanh::lean_ctor_set(v___x_1084_, 1, v___x_1082_);
    leanh::lean_ctor_set(v___x_1084_, 2, v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_StateT_instAlternative(
    mut v_00_u03c3_1085_: *mut leanh::LeanObject,
    mut v_m_1086_: *mut leanh::LeanObject,
    mut v_inst_1087_: *mut leanh::LeanObject,
    mut v_inst_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_StateT_instAlternative___redArg(v_inst_1087_, v_inst_1088_);
    return v___x_1089_;
}
pub unsafe fn l_StateT_get___redArg(
    mut v_inst_1090_: *mut leanh::LeanObject,
    mut v_s_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v_toPure_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_unused_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1092_ = leanh::lean_ctor_get(v_inst_1090_, 0);
                v_isSharedCheck_1101_ = (!leanh::lean_is_exclusive(v_inst_1090_)) as u8;
                if v_isSharedCheck_1101_ == 0 {
                    v_unused_1102_ = leanh::lean_ctor_get(v_inst_1090_, 1);
                    leanh::lean_dec(v_unused_1102_);
                    v___x_1094_ = v_inst_1090_;
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1092_);
                    leanh::lean_dec(v_inst_1090_);
                    v___x_1094_ = leanh::lean_box(0);
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1096_ = leanh::lean_ctor_get(v_toApplicative_1092_, 1);
                leanh::lean_inc(v_toPure_1096_);
                leanh::lean_dec_ref(v_toApplicative_1092_);
                leanh::lean_inc(v_s_1091_);
                if v_isShared_1095_ == 0 {
                    leanh::lean_ctor_set(v___x_1094_, 1, v_s_1091_);
                    leanh::lean_ctor_set(v___x_1094_, 0, v_s_1091_);
                    v___x_1098_ = v___x_1094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_s_1091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_s_1091_);
                    v___x_1098_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = leanh::lean_apply_2(
                    v_toPure_1096_,
                    leanh::lean_box(0),
                    v___x_1098_,
                );
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_get(
    mut v_00_u03c3_1103_: *mut leanh::LeanObject,
    mut v_m_1104_: *mut leanh::LeanObject,
    mut v_inst_1105_: *mut leanh::LeanObject,
    mut v_s_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v_toPure_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_unused_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1107_ = leanh::lean_ctor_get(v_inst_1105_, 0);
                v_isSharedCheck_1116_ = (!leanh::lean_is_exclusive(v_inst_1105_)) as u8;
                if v_isSharedCheck_1116_ == 0 {
                    v_unused_1117_ = leanh::lean_ctor_get(v_inst_1105_, 1);
                    leanh::lean_dec(v_unused_1117_);
                    v___x_1109_ = v_inst_1105_;
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1107_);
                    leanh::lean_dec(v_inst_1105_);
                    v___x_1109_ = leanh::lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1111_ = leanh::lean_ctor_get(v_toApplicative_1107_, 1);
                leanh::lean_inc(v_toPure_1111_);
                leanh::lean_dec_ref(v_toApplicative_1107_);
                leanh::lean_inc(v_s_1106_);
                if v_isShared_1110_ == 0 {
                    leanh::lean_ctor_set(v___x_1109_, 1, v_s_1106_);
                    leanh::lean_ctor_set(v___x_1109_, 0, v_s_1106_);
                    v___x_1113_ = v___x_1109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_s_1106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_s_1106_);
                    v___x_1113_ = v_reuseFailAlloc_1115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1114_ = leanh::lean_apply_2(
                    v_toPure_1111_,
                    leanh::lean_box(0),
                    v___x_1113_,
                );
                return v___x_1114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___redArg(
    mut v_inst_1118_: *mut leanh::LeanObject,
    mut v_s_x27_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v_toPure_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_unused_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1120_ = leanh::lean_ctor_get(v_inst_1118_, 0);
                v_isSharedCheck_1130_ = (!leanh::lean_is_exclusive(v_inst_1118_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v_unused_1131_ = leanh::lean_ctor_get(v_inst_1118_, 1);
                    leanh::lean_dec(v_unused_1131_);
                    v___x_1122_ = v_inst_1118_;
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1120_);
                    leanh::lean_dec(v_inst_1118_);
                    v___x_1122_ = leanh::lean_box(0);
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1124_ = leanh::lean_ctor_get(v_toApplicative_1120_, 1);
                leanh::lean_inc(v_toPure_1124_);
                leanh::lean_dec_ref(v_toApplicative_1120_);
                v___x_1125_ = leanh::lean_box(0);
                if v_isShared_1123_ == 0 {
                    leanh::lean_ctor_set(v___x_1122_, 1, v_s_x27_1119_);
                    leanh::lean_ctor_set(v___x_1122_, 0, v___x_1125_);
                    v___x_1127_ = v___x_1122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_s_x27_1119_);
                    v___x_1127_ = v_reuseFailAlloc_1129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1128_ = leanh::lean_apply_2(
                    v_toPure_1124_,
                    leanh::lean_box(0),
                    v___x_1127_,
                );
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set(
    mut v_00_u03c3_1132_: *mut leanh::LeanObject,
    mut v_m_1133_: *mut leanh::LeanObject,
    mut v_inst_1134_: *mut leanh::LeanObject,
    mut v_s_x27_1135_: *mut leanh::LeanObject,
    mut v_x_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v_toPure_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_unused_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1137_ = leanh::lean_ctor_get(v_inst_1134_, 0);
                v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v_inst_1134_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v_unused_1148_ = leanh::lean_ctor_get(v_inst_1134_, 1);
                    leanh::lean_dec(v_unused_1148_);
                    v___x_1139_ = v_inst_1134_;
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1137_);
                    leanh::lean_dec(v_inst_1134_);
                    v___x_1139_ = leanh::lean_box(0);
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1141_ = leanh::lean_ctor_get(v_toApplicative_1137_, 1);
                leanh::lean_inc(v_toPure_1141_);
                leanh::lean_dec_ref(v_toApplicative_1137_);
                v___x_1142_ = leanh::lean_box(0);
                if v_isShared_1140_ == 0 {
                    leanh::lean_ctor_set(v___x_1139_, 1, v_s_x27_1135_);
                    leanh::lean_ctor_set(v___x_1139_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_s_x27_1135_);
                    v___x_1144_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1145_ = leanh::lean_apply_2(
                    v_toPure_1141_,
                    leanh::lean_box(0),
                    v___x_1144_,
                );
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___boxed(
    mut v_00_u03c3_1149_: *mut leanh::LeanObject,
    mut v_m_1150_: *mut leanh::LeanObject,
    mut v_inst_1151_: *mut leanh::LeanObject,
    mut v_s_x27_1152_: *mut leanh::LeanObject,
    mut v_x_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_StateT_set(
        v_00_u03c3_1149_,
        v_m_1150_,
        v_inst_1151_,
        v_s_x27_1152_,
        v_x_1153_,
    );
    leanh::lean_dec(v_x_1153_);
    return v_res_1154_;
}
pub unsafe fn l_StateT_modifyGet___redArg(
    mut v_inst_1155_: *mut leanh::LeanObject,
    mut v_f_1156_: *mut leanh::LeanObject,
    mut v_s_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1158_ = leanh::lean_ctor_get(v_inst_1155_, 0);
    leanh::lean_inc_ref(v_toApplicative_1158_);
    leanh::lean_dec_ref(v_inst_1155_);
    v_toPure_1159_ = leanh::lean_ctor_get(v_toApplicative_1158_, 1);
    leanh::lean_inc(v_toPure_1159_);
    leanh::lean_dec_ref(v_toApplicative_1158_);
    v___x_1160_ = leanh::lean_apply_1(v_f_1156_, v_s_1157_);
    v___x_1161_ =
        leanh::lean_apply_2(v_toPure_1159_, leanh::lean_box(0), v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_StateT_modifyGet(
    mut v_00_u03c3_1162_: *mut leanh::LeanObject,
    mut v_m_1163_: *mut leanh::LeanObject,
    mut v_inst_1164_: *mut leanh::LeanObject,
    mut v_00_u03b1_1165_: *mut leanh::LeanObject,
    mut v_f_1166_: *mut leanh::LeanObject,
    mut v_s_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1168_ = leanh::lean_ctor_get(v_inst_1164_, 0);
    leanh::lean_inc_ref(v_toApplicative_1168_);
    leanh::lean_dec_ref(v_inst_1164_);
    v_toPure_1169_ = leanh::lean_ctor_get(v_toApplicative_1168_, 1);
    leanh::lean_inc(v_toPure_1169_);
    leanh::lean_dec_ref(v_toApplicative_1168_);
    v___x_1170_ = leanh::lean_apply_1(v_f_1166_, v_s_1167_);
    v___x_1171_ =
        leanh::lean_apply_2(v_toPure_1169_, leanh::lean_box(0), v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_StateT_lift___redArg___lam__0(
    mut v_s_1172_: *mut leanh::LeanObject,
    mut v_toPure_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1175_, 0, v_a_1174_);
    leanh::lean_ctor_set(v___x_1175_, 1, v_s_1172_);
    v___x_1176_ =
        leanh::lean_apply_2(v_toPure_1173_, leanh::lean_box(0), v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn l_StateT_lift___redArg(
    mut v_inst_1177_: *mut leanh::LeanObject,
    mut v_t_1178_: *mut leanh::LeanObject,
    mut v_s_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1180_ = leanh::lean_ctor_get(v_inst_1177_, 0);
    leanh::lean_inc_ref(v_toApplicative_1180_);
    v_toBind_1181_ = leanh::lean_ctor_get(v_inst_1177_, 1);
    leanh::lean_inc(v_toBind_1181_);
    leanh::lean_dec_ref(v_inst_1177_);
    v_toPure_1182_ = leanh::lean_ctor_get(v_toApplicative_1180_, 1);
    leanh::lean_inc(v_toPure_1182_);
    leanh::lean_dec_ref(v_toApplicative_1180_);
    v___f_1183_ = leanh::lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1183_, 0, v_s_1179_);
    leanh::lean_closure_set(v___f_1183_, 1, v_toPure_1182_);
    v___x_1184_ = leanh::lean_apply_4(
        v_toBind_1181_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_t_1178_,
        v___f_1183_,
    );
    return v___x_1184_;
}
pub unsafe fn l_StateT_lift(
    mut v_00_u03c3_1185_: *mut leanh::LeanObject,
    mut v_m_1186_: *mut leanh::LeanObject,
    mut v_inst_1187_: *mut leanh::LeanObject,
    mut v_00_u03b1_1188_: *mut leanh::LeanObject,
    mut v_t_1189_: *mut leanh::LeanObject,
    mut v_s_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1191_ = leanh::lean_ctor_get(v_inst_1187_, 0);
    leanh::lean_inc_ref(v_toApplicative_1191_);
    v_toBind_1192_ = leanh::lean_ctor_get(v_inst_1187_, 1);
    leanh::lean_inc(v_toBind_1192_);
    leanh::lean_dec_ref(v_inst_1187_);
    v_toPure_1193_ = leanh::lean_ctor_get(v_toApplicative_1191_, 1);
    leanh::lean_inc(v_toPure_1193_);
    leanh::lean_dec_ref(v_toApplicative_1191_);
    v___f_1194_ = leanh::lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1194_, 0, v_s_1190_);
    leanh::lean_closure_set(v___f_1194_, 1, v_toPure_1193_);
    v___x_1195_ = leanh::lean_apply_4(
        v_toBind_1192_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_t_1189_,
        v___f_1194_,
    );
    return v___x_1195_;
}
pub unsafe fn l_StateT_instMonadLift___redArg(
    mut v_inst_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1197_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1197_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1197_, 2, v_inst_1196_);
    return v___x_1197_;
}
pub unsafe fn l_StateT_instMonadLift(
    mut v_00_u03c3_1198_: *mut leanh::LeanObject,
    mut v_m_1199_: *mut leanh::LeanObject,
    mut v_inst_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1201_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1201_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1201_, 2, v_inst_1200_);
    return v___x_1201_;
}
pub unsafe fn l_StateT_instMonadFunctor___lam__0(
    mut v_00_u03b1_1202_: *mut leanh::LeanObject,
    mut v_f_1203_: *mut leanh::LeanObject,
    mut v_x_1204_: *mut leanh::LeanObject,
    mut v_s_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = leanh::lean_apply_1(v_x_1204_, v_s_1205_);
    v___x_1207_ = leanh::lean_apply_2(v_f_1203_, leanh::lean_box(0), v___x_1206_);
    return v___x_1207_;
}
pub unsafe fn l_StateT_instMonadFunctor(
    mut v_00_u03c3_1209_: *mut leanh::LeanObject,
    mut v_m_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1211_ = l_StateT_instMonadFunctor___closed__0;
    return v___f_1211_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__0(
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v_toPure_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1215_, 0, v_a_1214_);
    leanh::lean_ctor_set(v___x_1215_, 1, v___y_1212_);
    v___x_1216_ =
        leanh::lean_apply_2(v_toPure_1213_, leanh::lean_box(0), v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__1(
    mut v_inst_1217_: *mut leanh::LeanObject,
    mut v_inst_1218_: *mut leanh::LeanObject,
    mut v_00_u03b1_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1222_ = leanh::lean_ctor_get(v_inst_1218_, 0);
    leanh::lean_inc_ref(v_toApplicative_1222_);
    v_throw_1223_ = leanh::lean_ctor_get(v_inst_1217_, 0);
    leanh::lean_inc(v_throw_1223_);
    leanh::lean_dec_ref(v_inst_1217_);
    v_toBind_1224_ = leanh::lean_ctor_get(v_inst_1218_, 1);
    leanh::lean_inc(v_toBind_1224_);
    leanh::lean_dec_ref(v_inst_1218_);
    v_toPure_1225_ = leanh::lean_ctor_get(v_toApplicative_1222_, 1);
    leanh::lean_inc(v_toPure_1225_);
    leanh::lean_dec_ref(v_toApplicative_1222_);
    v___x_1226_ = leanh::lean_apply_2(v_throw_1223_, leanh::lean_box(0), v___y_1220_);
    v___f_1227_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1227_, 0, v___y_1221_);
    leanh::lean_closure_set(v___f_1227_, 1, v_toPure_1225_);
    v___x_1228_ = leanh::lean_apply_4(
        v_toBind_1224_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1226_,
        v___f_1227_,
    );
    return v___x_1228_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__2(
    mut v_c_1229_: *mut leanh::LeanObject,
    mut v_s_1230_: *mut leanh::LeanObject,
    mut v_e_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = leanh::lean_apply_2(v_c_1229_, v_e_1231_, v_s_1230_);
    return v___x_1232_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__3(
    mut v_inst_1233_: *mut leanh::LeanObject,
    mut v_00_u03b1_1234_: *mut leanh::LeanObject,
    mut v_x_1235_: *mut leanh::LeanObject,
    mut v_c_1236_: *mut leanh::LeanObject,
    mut v_s_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_1238_ = leanh::lean_ctor_get(v_inst_1233_, 1);
    leanh::lean_inc(v_tryCatch_1238_);
    leanh::lean_dec_ref(v_inst_1233_);
    leanh::lean_inc(v_s_1237_);
    v___f_1239_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1239_, 0, v_c_1236_);
    leanh::lean_closure_set(v___f_1239_, 1, v_s_1237_);
    v___x_1240_ = leanh::lean_apply_1(v_x_1235_, v_s_1237_);
    v___x_1241_ = leanh::lean_apply_3(
        v_tryCatch_1238_,
        leanh::lean_box(0),
        v___x_1240_,
        v___f_1239_,
    );
    return v___x_1241_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg(
    mut v_inst_1242_: *mut leanh::LeanObject,
    mut v_inst_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1243_);
    v___f_1244_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1244_, 0, v_inst_1243_);
    leanh::lean_closure_set(v___f_1244_, 1, v_inst_1242_);
    v___f_1245_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1245_, 0, v_inst_1243_);
    v___x_1246_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1246_, 0, v___f_1244_);
    leanh::lean_ctor_set(v___x_1246_, 1, v___f_1245_);
    return v___x_1246_;
}
pub unsafe fn l_StateT_instMonadExceptOf(
    mut v_00_u03c3_1247_: *mut leanh::LeanObject,
    mut v_m_1248_: *mut leanh::LeanObject,
    mut v_inst_1249_: *mut leanh::LeanObject,
    mut v_00_u03b5_1250_: *mut leanh::LeanObject,
    mut v_inst_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1251_);
    v___f_1252_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1252_, 0, v_inst_1251_);
    leanh::lean_closure_set(v___f_1252_, 1, v_inst_1249_);
    v___f_1253_ = leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1253_, 0, v_inst_1251_);
    v___x_1254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1254_, 0, v___f_1252_);
    leanh::lean_ctor_set(v___x_1254_, 1, v___f_1253_);
    return v___x_1254_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__0(
    mut v_toPure_1255_: *mut leanh::LeanObject,
    mut v_____do__lift_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_a_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_1256_) == 0 {
                    v_a_1257_ = leanh::lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1265_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1259_ = v_____do__lift_1256_;
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1257_);
                        leanh::lean_dec(v_____do__lift_1256_);
                        v___x_1259_ = leanh::lean_box(0);
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1266_ = leanh::lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1276_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1268_ = v_____do__lift_1256_;
                        v_isShared_1269_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1266_);
                        leanh::lean_dec(v_____do__lift_1256_);
                        v___x_1268_ = leanh::lean_box(0);
                        v_isShared_1269_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1260_ == 0 {
                    v___x_1262_ = v___x_1259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1263_ = leanh::lean_apply_2(
                    v_toPure_1255_,
                    leanh::lean_box(0),
                    v___x_1262_,
                );
                return v___x_1263_;
            }
            3 => {
                v___x_1270_ = leanh::lean_box(0);
                v___x_1271_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                leanh::lean_ctor_set(v___x_1271_, 1, v_a_1266_);
                if v_isShared_1269_ == 0 {
                    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1274_ = leanh::lean_apply_2(
                    v_toPure_1255_,
                    leanh::lean_box(0),
                    v___x_1273_,
                );
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ForM_forIn___redArg___lam__1(
    mut v_f_1277_: *mut leanh::LeanObject,
    mut v_toBind_1278_: *mut leanh::LeanObject,
    mut v___f_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
    mut v_b_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = leanh::lean_apply_2(v_f_1277_, v_a_1280_, v_b_1281_);
    v___x_1283_ = leanh::lean_apply_4(
        v_toBind_1278_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1282_,
        v___f_1279_,
    );
    return v___x_1283_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__2(
    mut v_toPure_1284_: *mut leanh::LeanObject,
    mut v_____do__lift_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1285_) == 0 {
        let mut v_a_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1286_ = leanh::lean_ctor_get(v_____do__lift_1285_, 0);
        leanh::lean_inc(v_a_1286_);
        leanh::lean_dec_ref_known(v_____do__lift_1285_, 1);
        v___x_1287_ =
            leanh::lean_apply_2(v_toPure_1284_, leanh::lean_box(0), v_a_1286_);
        return v___x_1287_;
    } else {
        let mut v_a_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1288_ = leanh::lean_ctor_get(v_____do__lift_1285_, 0);
        leanh::lean_inc(v_a_1288_);
        leanh::lean_dec_ref_known(v_____do__lift_1285_, 1);
        v_snd_1289_ = leanh::lean_ctor_get(v_a_1288_, 1);
        leanh::lean_inc(v_snd_1289_);
        leanh::lean_dec(v_a_1288_);
        v___x_1290_ =
            leanh::lean_apply_2(v_toPure_1284_, leanh::lean_box(0), v_snd_1289_);
        return v___x_1290_;
    }
}
pub unsafe fn l_ForM_forIn___redArg(
    mut v_inst_1291_: *mut leanh::LeanObject,
    mut v_inst_1292_: *mut leanh::LeanObject,
    mut v_x_1293_: *mut leanh::LeanObject,
    mut v_b_1294_: *mut leanh::LeanObject,
    mut v_f_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1296_ = leanh::lean_ctor_get(v_inst_1291_, 0);
    leanh::lean_inc_ref(v_toApplicative_1296_);
    v_toBind_1297_ = leanh::lean_ctor_get(v_inst_1291_, 1);
    leanh::lean_inc_n(v_toBind_1297_, 2);
    leanh::lean_dec_ref(v_inst_1291_);
    v_toPure_1298_ = leanh::lean_ctor_get(v_toApplicative_1296_, 1);
    leanh::lean_inc_n(v_toPure_1298_, 2);
    leanh::lean_dec_ref(v_toApplicative_1296_);
    v___f_1299_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1299_, 0, v_toPure_1298_);
    v_g_1300_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v_g_1300_, 0, v_f_1295_);
    leanh::lean_closure_set(v_g_1300_, 1, v_toBind_1297_);
    leanh::lean_closure_set(v_g_1300_, 2, v___f_1299_);
    v___f_1301_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1301_, 0, v_toPure_1298_);
    v___x_1302_ = leanh::lean_apply_3(v_inst_1292_, v_x_1293_, v_g_1300_, v_b_1294_);
    v___x_1303_ = leanh::lean_apply_4(
        v_toBind_1297_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1302_,
        v___f_1301_,
    );
    return v___x_1303_;
}
pub unsafe fn l_ForM_forIn(
    mut v_m_1304_: *mut leanh::LeanObject,
    mut v_00_u03b2_1305_: *mut leanh::LeanObject,
    mut v_00_u03c1_1306_: *mut leanh::LeanObject,
    mut v_00_u03b1_1307_: *mut leanh::LeanObject,
    mut v_inst_1308_: *mut leanh::LeanObject,
    mut v_inst_1309_: *mut leanh::LeanObject,
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v_b_1311_: *mut leanh::LeanObject,
    mut v_f_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1313_ = leanh::lean_ctor_get(v_inst_1308_, 0);
    leanh::lean_inc_ref(v_toApplicative_1313_);
    v_toBind_1314_ = leanh::lean_ctor_get(v_inst_1308_, 1);
    leanh::lean_inc_n(v_toBind_1314_, 2);
    leanh::lean_dec_ref(v_inst_1308_);
    v_toPure_1315_ = leanh::lean_ctor_get(v_toApplicative_1313_, 1);
    leanh::lean_inc_n(v_toPure_1315_, 2);
    leanh::lean_dec_ref(v_toApplicative_1313_);
    v___f_1316_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1316_, 0, v_toPure_1315_);
    v_g_1317_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v_g_1317_, 0, v_f_1312_);
    leanh::lean_closure_set(v_g_1317_, 1, v_toBind_1314_);
    leanh::lean_closure_set(v_g_1317_, 2, v___f_1316_);
    v___f_1318_ = leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1318_, 0, v_toPure_1315_);
    v___x_1319_ = leanh::lean_apply_3(v_inst_1309_, v_x_1310_, v_g_1317_, v_b_1311_);
    v___x_1320_ = leanh::lean_apply_4(
        v_toBind_1314_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1319_,
        v___f_1318_,
    );
    return v___x_1320_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad___redArg(
    mut v_inst_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1321_, 2);
    v___x_1322_ = leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1322_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1322_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1322_, 2, v_inst_1321_);
    v___x_1323_ =
        leanh::lean_alloc_closure(l_StateT_set___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_1323_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1323_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1323_, 2, v_inst_1321_);
    v___x_1324_ =
        leanh::lean_alloc_closure(l_StateT_modifyGet as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1324_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1324_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1324_, 2, v_inst_1321_);
    v___x_1325_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1325_, 0, v___x_1322_);
    leanh::lean_ctor_set(v___x_1325_, 1, v___x_1323_);
    leanh::lean_ctor_set(v___x_1325_, 2, v___x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad(
    mut v_00_u03c3_1326_: *mut leanh::LeanObject,
    mut v_m_1327_: *mut leanh::LeanObject,
    mut v_inst_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__0(
    mut v_fst_1330_: *mut leanh::LeanObject,
    mut v_00_u03b2_1331_: *mut leanh::LeanObject,
    mut v_x_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = leanh::lean_apply_1(v_x_1332_, v_fst_1330_);
    return v___x_1333_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__1(
    mut v_snd_1334_: *mut leanh::LeanObject,
    mut v_toPure_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1337_, 0, v_a_1336_);
    leanh::lean_ctor_set(v___x_1337_, 1, v_snd_1334_);
    v___x_1338_ =
        leanh::lean_apply_2(v_toPure_1335_, leanh::lean_box(0), v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__2(
    mut v_f_1339_: *mut leanh::LeanObject,
    mut v_toPure_1340_: *mut leanh::LeanObject,
    mut v_toBind_1341_: *mut leanh::LeanObject,
    mut v_____x_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1343_ = leanh::lean_ctor_get(v_____x_1342_, 0);
    leanh::lean_inc(v_fst_1343_);
    v_snd_1344_ = leanh::lean_ctor_get(v_____x_1342_, 1);
    leanh::lean_inc(v_snd_1344_);
    leanh::lean_dec_ref(v_____x_1342_);
    v___f_1345_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1345_, 0, v_fst_1343_);
    v___x_1346_ = leanh::lean_apply_1(v_f_1339_, v___f_1345_);
    v___f_1347_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1347_, 0, v_snd_1344_);
    leanh::lean_closure_set(v___f_1347_, 1, v_toPure_1340_);
    v___x_1348_ = leanh::lean_apply_4(
        v_toBind_1341_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1346_,
        v___f_1347_,
    );
    return v___x_1348_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__3(
    mut v_inst_1349_: *mut leanh::LeanObject,
    mut v_00_u03b1_1350_: *mut leanh::LeanObject,
    mut v_f_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_toPure_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1353_ = leanh::lean_ctor_get(v_inst_1349_, 0);
                v_toBind_1354_ = leanh::lean_ctor_get(v_inst_1349_, 1);
                v_isSharedCheck_1365_ = (!leanh::lean_is_exclusive(v_inst_1349_)) as u8;
                if v_isSharedCheck_1365_ == 0 {
                    v___x_1356_ = v_inst_1349_;
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1354_);
                    leanh::lean_inc(v_toApplicative_1353_);
                    leanh::lean_dec(v_inst_1349_);
                    v___x_1356_ = leanh::lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1358_ = leanh::lean_ctor_get(v_toApplicative_1353_, 1);
                leanh::lean_inc_n(v_toPure_1358_, 2);
                leanh::lean_dec_ref(v_toApplicative_1353_);
                leanh::lean_inc(v_toBind_1354_);
                v___f_1359_ = leanh::lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__2 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1359_, 0, v_f_1351_);
                leanh::lean_closure_set(v___f_1359_, 1, v_toPure_1358_);
                leanh::lean_closure_set(v___f_1359_, 2, v_toBind_1354_);
                leanh::lean_inc(v___y_1352_);
                if v_isShared_1357_ == 0 {
                    leanh::lean_ctor_set(v___x_1356_, 1, v___y_1352_);
                    leanh::lean_ctor_set(v___x_1356_, 0, v___y_1352_);
                    v___x_1361_ = v___x_1356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1364_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___y_1352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___y_1352_);
                    v___x_1361_ = v_reuseFailAlloc_1364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1362_ = leanh::lean_apply_2(
                    v_toPure_1358_,
                    leanh::lean_box(0),
                    v___x_1361_,
                );
                v___x_1363_ = leanh::lean_apply_4(
                    v_toBind_1354_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1362_,
                    v___f_1359_,
                );
                return v___x_1363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_monadControl___redArg___lam__4(
    mut v_fst_1366_: *mut leanh::LeanObject,
    mut v_toPure_1367_: *mut leanh::LeanObject,
    mut v_____x_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_unused_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1369_ = leanh::lean_ctor_get(v_____x_1368_, 1);
                v_isSharedCheck_1377_ = (!leanh::lean_is_exclusive(v_____x_1368_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v_unused_1378_ = leanh::lean_ctor_get(v_____x_1368_, 0);
                    leanh::lean_dec(v_unused_1378_);
                    v___x_1371_ = v_____x_1368_;
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1369_);
                    leanh::lean_dec(v_____x_1368_);
                    v___x_1371_ = leanh::lean_box(0);
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1372_ == 0 {
                    leanh::lean_ctor_set(v___x_1371_, 0, v_fst_1366_);
                    v___x_1374_ = v___x_1371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fst_1366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1375_ = leanh::lean_apply_2(
                    v_toPure_1367_,
                    leanh::lean_box(0),
                    v___x_1374_,
                );
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_monadControl___redArg___lam__5(
    mut v_inst_1379_: *mut leanh::LeanObject,
    mut v_____x_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v_toBind_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1381_ = leanh::lean_ctor_get(v_____x_1380_, 0);
                leanh::lean_inc(v_fst_1381_);
                leanh::lean_dec_ref(v_____x_1380_);
                v_toApplicative_1382_ = leanh::lean_ctor_get(v_inst_1379_, 0);
                leanh::lean_inc_ref(v_toApplicative_1382_);
                v_fst_1383_ = leanh::lean_ctor_get(v_fst_1381_, 0);
                v_snd_1384_ = leanh::lean_ctor_get(v_fst_1381_, 1);
                v_isSharedCheck_1397_ = (!leanh::lean_is_exclusive(v_fst_1381_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1386_ = v_fst_1381_;
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1384_);
                    leanh::lean_inc(v_fst_1383_);
                    leanh::lean_dec(v_fst_1381_);
                    v___x_1386_ = leanh::lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_1388_ = leanh::lean_ctor_get(v_inst_1379_, 1);
                leanh::lean_inc(v_toBind_1388_);
                leanh::lean_dec_ref(v_inst_1379_);
                v_toPure_1389_ = leanh::lean_ctor_get(v_toApplicative_1382_, 1);
                leanh::lean_inc_n(v_toPure_1389_, 2);
                leanh::lean_dec_ref(v_toApplicative_1382_);
                v___f_1390_ = leanh::lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1390_, 0, v_fst_1383_);
                leanh::lean_closure_set(v___f_1390_, 1, v_toPure_1389_);
                v___x_1391_ = leanh::lean_box(0);
                if v_isShared_1387_ == 0 {
                    leanh::lean_ctor_set(v___x_1386_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_snd_1384_);
                    v___x_1393_ = v_reuseFailAlloc_1396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1394_ = leanh::lean_apply_2(
                    v_toPure_1389_,
                    leanh::lean_box(0),
                    v___x_1393_,
                );
                v___x_1395_ = leanh::lean_apply_4(
                    v_toBind_1388_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1394_,
                    v___f_1390_,
                );
                return v___x_1395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_monadControl___redArg___lam__6(
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v_toPure_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1401_, 0, v_a_1400_);
    leanh::lean_ctor_set(v___x_1401_, 1, v___y_1398_);
    v___x_1402_ =
        leanh::lean_apply_2(v_toPure_1399_, leanh::lean_box(0), v___x_1401_);
    return v___x_1402_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__7(
    mut v_inst_1403_: *mut leanh::LeanObject,
    mut v___f_1404_: *mut leanh::LeanObject,
    mut v_00_u03b1_1405_: *mut leanh::LeanObject,
    mut v_x_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1408_ = leanh::lean_ctor_get(v_inst_1403_, 0);
    leanh::lean_inc_ref(v_toApplicative_1408_);
    v_toBind_1409_ = leanh::lean_ctor_get(v_inst_1403_, 1);
    leanh::lean_inc_n(v_toBind_1409_, 2);
    leanh::lean_dec_ref(v_inst_1403_);
    v_toPure_1410_ = leanh::lean_ctor_get(v_toApplicative_1408_, 1);
    leanh::lean_inc(v_toPure_1410_);
    leanh::lean_dec_ref(v_toApplicative_1408_);
    v___f_1411_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__6 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1411_, 0, v___y_1407_);
    leanh::lean_closure_set(v___f_1411_, 1, v_toPure_1410_);
    v___x_1412_ = leanh::lean_apply_4(
        v_toBind_1409_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_1406_,
        v___f_1411_,
    );
    v___x_1413_ = leanh::lean_apply_4(
        v_toBind_1409_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1412_,
        v___f_1404_,
    );
    return v___x_1413_;
}
pub unsafe fn l_StateT_monadControl___redArg(
    mut v_inst_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1414_, 2);
    v___f_1415_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1415_, 0, v_inst_1414_);
    v___f_1416_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1416_, 0, v_inst_1414_);
    v___f_1417_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1417_, 0, v_inst_1414_);
    leanh::lean_closure_set(v___f_1417_, 1, v___f_1416_);
    v___x_1418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1418_, 0, v___f_1415_);
    leanh::lean_ctor_set(v___x_1418_, 1, v___f_1417_);
    return v___x_1418_;
}
pub unsafe fn l_StateT_monadControl(
    mut v_00_u03c3_1419_: *mut leanh::LeanObject,
    mut v_m_1420_: *mut leanh::LeanObject,
    mut v_inst_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1421_, 2);
    v___f_1422_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1422_, 0, v_inst_1421_);
    v___f_1423_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1423_, 0, v_inst_1421_);
    v___f_1424_ = leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1424_, 0, v_inst_1421_);
    leanh::lean_closure_set(v___f_1424_, 1, v___f_1423_);
    v___x_1425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1425_, 0, v___f_1422_);
    leanh::lean_ctor_set(v___x_1425_, 1, v___f_1424_);
    return v___x_1425_;
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__0(
    mut v_toPure_1426_: *mut leanh::LeanObject,
    mut v_____x_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v_fst_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_unused_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1428_ = leanh::lean_ctor_get(v_____x_1427_, 0);
                leanh::lean_inc(v_fst_1428_);
                v_snd_1429_ = leanh::lean_ctor_get(v_____x_1427_, 1);
                leanh::lean_inc(v_snd_1429_);
                leanh::lean_dec_ref(v_____x_1427_);
                v_fst_1430_ = leanh::lean_ctor_get(v_fst_1428_, 0);
                v_isSharedCheck_1447_ = (!leanh::lean_is_exclusive(v_fst_1428_)) as u8;
                if v_isSharedCheck_1447_ == 0 {
                    v_unused_1448_ = leanh::lean_ctor_get(v_fst_1428_, 1);
                    leanh::lean_dec(v_unused_1448_);
                    v___x_1432_ = v_fst_1428_;
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1430_);
                    leanh::lean_dec(v_fst_1428_);
                    v___x_1432_ = leanh::lean_box(0);
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1434_ = leanh::lean_ctor_get(v_snd_1429_, 0);
                v_snd_1435_ = leanh::lean_ctor_get(v_snd_1429_, 1);
                v_isSharedCheck_1446_ = (!leanh::lean_is_exclusive(v_snd_1429_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v___x_1437_ = v_snd_1429_;
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1435_);
                    leanh::lean_inc(v_fst_1434_);
                    leanh::lean_dec(v_snd_1429_);
                    v___x_1437_ = leanh::lean_box(0);
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1438_ == 0 {
                    leanh::lean_ctor_set(v___x_1437_, 1, v_fst_1434_);
                    leanh::lean_ctor_set(v___x_1437_, 0, v_fst_1430_);
                    v___x_1440_ = v___x_1437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_fst_1434_);
                    v___x_1440_ = v_reuseFailAlloc_1445_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1433_ == 0 {
                    leanh::lean_ctor_set(v___x_1432_, 1, v_snd_1435_);
                    leanh::lean_ctor_set(v___x_1432_, 0, v___x_1440_);
                    v___x_1442_ = v___x_1432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1435_);
                    v___x_1442_ = v_reuseFailAlloc_1444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1443_ = leanh::lean_apply_2(
                    v_toPure_1426_,
                    leanh::lean_box(0),
                    v___x_1442_,
                );
                return v___x_1443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__1(
    mut v_h_1449_: *mut leanh::LeanObject,
    mut v_s_1450_: *mut leanh::LeanObject,
    mut v_x_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v_fst_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1451_) == 0 {
                    v___x_1452_ = leanh::lean_box(0);
                    v___x_1453_ = leanh::lean_apply_2(v_h_1449_, v___x_1452_, v_s_1450_);
                    return v___x_1453_;
                } else {
                    leanh::lean_dec(v_s_1450_);
                    v_val_1454_ = leanh::lean_ctor_get(v_x_1451_, 0);
                    v_isSharedCheck_1464_ = (!leanh::lean_is_exclusive(v_x_1451_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1456_ = v_x_1451_;
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1454_);
                        leanh::lean_dec(v_x_1451_);
                        v___x_1456_ = leanh::lean_box(0);
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1458_ = leanh::lean_ctor_get(v_val_1454_, 0);
                leanh::lean_inc(v_fst_1458_);
                v_snd_1459_ = leanh::lean_ctor_get(v_val_1454_, 1);
                leanh::lean_inc(v_snd_1459_);
                leanh::lean_dec(v_val_1454_);
                if v_isShared_1457_ == 0 {
                    leanh::lean_ctor_set(v___x_1456_, 0, v_fst_1458_);
                    v___x_1461_ = v___x_1456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_fst_1458_);
                    v___x_1461_ = v_reuseFailAlloc_1463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1462_ = leanh::lean_apply_2(v_h_1449_, v___x_1461_, v_snd_1459_);
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__2(
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_toBind_1466_: *mut leanh::LeanObject,
    mut v___f_1467_: *mut leanh::LeanObject,
    mut v_00_u03b1_1468_: *mut leanh::LeanObject,
    mut v_00_u03b2_1469_: *mut leanh::LeanObject,
    mut v_x_1470_: *mut leanh::LeanObject,
    mut v_h_1471_: *mut leanh::LeanObject,
    mut v_s_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_1472_);
    v___f_1473_ = leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1473_, 0, v_h_1471_);
    leanh::lean_closure_set(v___f_1473_, 1, v_s_1472_);
    v___x_1474_ = leanh::lean_apply_1(v_x_1470_, v_s_1472_);
    v___x_1475_ = leanh::lean_apply_4(
        v_inst_1465_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1474_,
        v___f_1473_,
    );
    v___x_1476_ = leanh::lean_apply_4(
        v_toBind_1466_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1475_,
        v___f_1467_,
    );
    return v___x_1476_;
}
pub unsafe fn l_StateT_tryFinally___redArg(
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_inst_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1479_ = leanh::lean_ctor_get(v_inst_1478_, 0);
    leanh::lean_inc_ref(v_toApplicative_1479_);
    v_toBind_1480_ = leanh::lean_ctor_get(v_inst_1478_, 1);
    leanh::lean_inc(v_toBind_1480_);
    leanh::lean_dec_ref(v_inst_1478_);
    v_toPure_1481_ = leanh::lean_ctor_get(v_toApplicative_1479_, 1);
    leanh::lean_inc(v_toPure_1481_);
    leanh::lean_dec_ref(v_toApplicative_1479_);
    v___f_1482_ = leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1482_, 0, v_toPure_1481_);
    v___f_1483_ = leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_1483_, 0, v_inst_1477_);
    leanh::lean_closure_set(v___f_1483_, 1, v_toBind_1480_);
    leanh::lean_closure_set(v___f_1483_, 2, v___f_1482_);
    return v___f_1483_;
}
pub unsafe fn l_StateT_tryFinally(
    mut v_m_1484_: *mut leanh::LeanObject,
    mut v_00_u03c3_1485_: *mut leanh::LeanObject,
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_inst_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1488_ = leanh::lean_ctor_get(v_inst_1487_, 0);
    leanh::lean_inc_ref(v_toApplicative_1488_);
    v_toBind_1489_ = leanh::lean_ctor_get(v_inst_1487_, 1);
    leanh::lean_inc(v_toBind_1489_);
    leanh::lean_dec_ref(v_inst_1487_);
    v_toPure_1490_ = leanh::lean_ctor_get(v_toApplicative_1488_, 1);
    leanh::lean_inc(v_toPure_1490_);
    leanh::lean_dec_ref(v_toApplicative_1488_);
    v___f_1491_ = leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1491_, 0, v_toPure_1490_);
    v___f_1492_ = leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_1492_, 0, v_inst_1486_);
    leanh::lean_closure_set(v___f_1492_, 1, v_toBind_1489_);
    leanh::lean_closure_set(v___f_1492_, 2, v___f_1491_);
    return v___f_1492_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg___lam__0(
    mut v_x_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1494_ = leanh::lean_ctor_get(v_x_1493_, 0);
                v_snd_1495_ = leanh::lean_ctor_get(v_x_1493_, 1);
                v_isSharedCheck_1502_ = (!leanh::lean_is_exclusive(v_x_1493_)) as u8;
                if v_isSharedCheck_1502_ == 0 {
                    v___x_1497_ = v_x_1493_;
                    v_isShared_1498_ = v_isSharedCheck_1502_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1495_);
                    leanh::lean_inc(v_fst_1494_);
                    leanh::lean_dec(v_x_1493_);
                    v___x_1497_ = leanh::lean_box(0);
                    v_isShared_1498_ = v_isSharedCheck_1502_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1498_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_fst_1494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_snd_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg___lam__1(
    mut v_toFunctor_1503_: *mut leanh::LeanObject,
    mut v_inst_1504_: *mut leanh::LeanObject,
    mut v___f_1505_: *mut leanh::LeanObject,
    mut v_00_u03b1_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
    mut v_s_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1509_ = leanh::lean_ctor_get(v_toFunctor_1503_, 0);
    leanh::lean_inc(v_map_1509_);
    leanh::lean_dec_ref(v_toFunctor_1503_);
    v___x_1510_ = leanh::lean_apply_1(v_x_1507_, v_s_1508_);
    v___x_1511_ = leanh::lean_apply_2(v_inst_1504_, leanh::lean_box(0), v___x_1510_);
    v___x_1512_ = leanh::lean_apply_4(
        v_map_1509_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1505_,
        v___x_1511_,
    );
    return v___x_1512_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg(
    mut v_inst_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1516_ = leanh::lean_ctor_get(v_inst_1514_, 0);
    leanh::lean_inc_ref(v_toApplicative_1516_);
    leanh::lean_dec_ref(v_inst_1514_);
    v_toFunctor_1517_ = leanh::lean_ctor_get(v_toApplicative_1516_, 0);
    leanh::lean_inc_ref(v_toFunctor_1517_);
    leanh::lean_dec_ref(v_toApplicative_1516_);
    v___f_1518_ = l_instMonadAttachStateTOfMonad___redArg___closed__0;
    v___f_1519_ = leanh::lean_alloc_closure(
        l_instMonadAttachStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_1519_, 0, v_toFunctor_1517_);
    leanh::lean_closure_set(v___f_1519_, 1, v_inst_1515_);
    leanh::lean_closure_set(v___f_1519_, 2, v___f_1518_);
    return v___f_1519_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad(
    mut v_m_1520_: *mut leanh::LeanObject,
    mut v_00_u03c3_1521_: *mut leanh::LeanObject,
    mut v_inst_1522_: *mut leanh::LeanObject,
    mut v_inst_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_instMonadAttachStateTOfMonad___redArg(v_inst_1522_, v_inst_1523_);
    return v___x_1524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_State(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_State(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_State(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_State(builtin);
}