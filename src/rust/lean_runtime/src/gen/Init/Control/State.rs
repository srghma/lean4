// Lean compiler output
// Module: Init.Control.State
// Imports: Init.Control.Except
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
pub static l_StateT_run_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateT_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_StateT_run_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_StateT_instMonadFunctor___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateT_instMonadFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_StateT_instMonadFunctor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadAttachStateTOfMonad___redArg___closed__0_value:
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
    m_fun: l_instMonadAttachStateTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadAttachStateTOfMonad___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadAttachStateTOfMonad___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_StateT_mk___redArg(
    mut v_x_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = crate::leanh::lean_apply_1(v_x_763_, v_a_764_);
    return v___x_765_;
}
pub unsafe fn l_StateT_mk(
    mut v_00_u03c3_766_: *mut crate::leanh::LeanObject,
    mut v_m_767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_768_: *mut crate::leanh::LeanObject,
    mut v_x_769_: *mut crate::leanh::LeanObject,
    mut v_a_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = crate::leanh::lean_apply_1(v_x_769_, v_a_770_);
    return v___x_771_;
}
pub unsafe fn l_StateT_run___redArg(
    mut v_x_772_: *mut crate::leanh::LeanObject,
    mut v_s_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_apply_1(v_x_772_, v_s_773_);
    return v___x_774_;
}
pub unsafe fn l_StateT_run(
    mut v_00_u03c3_775_: *mut crate::leanh::LeanObject,
    mut v_m_776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_777_: *mut crate::leanh::LeanObject,
    mut v_x_778_: *mut crate::leanh::LeanObject,
    mut v_s_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = crate::leanh::lean_apply_1(v_x_778_, v_s_779_);
    return v___x_780_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0(
    mut v_x_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_782_ = crate::leanh::lean_ctor_get(v_x_781_, 0);
    crate::leanh::lean_inc(v_fst_782_);
    return v_fst_782_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0___boxed(
    mut v_x_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_StateT_run_x27___redArg___lam__0(v_x_783_);
    crate::leanh::lean_dec_ref(v_x_783_);
    return v_res_784_;
}
pub unsafe fn l_StateT_run_x27___redArg(
    mut v_inst_786_: *mut crate::leanh::LeanObject,
    mut v_x_787_: *mut crate::leanh::LeanObject,
    mut v_s_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_789_ = crate::leanh::lean_ctor_get(v_inst_786_, 0);
    crate::leanh::lean_inc(v_map_789_);
    crate::leanh::lean_dec_ref(v_inst_786_);
    v___f_790_ = l_StateT_run_x27___redArg___closed__0;
    v___x_791_ = crate::leanh::lean_apply_1(v_x_787_, v_s_788_);
    v___x_792_ = crate::leanh::lean_apply_4(
        v_map_789_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_790_,
        v___x_791_,
    );
    return v___x_792_;
}
pub unsafe fn l_StateT_run_x27(
    mut v_00_u03c3_793_: *mut crate::leanh::LeanObject,
    mut v_m_794_: *mut crate::leanh::LeanObject,
    mut v_inst_795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_796_: *mut crate::leanh::LeanObject,
    mut v_x_797_: *mut crate::leanh::LeanObject,
    mut v_s_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_799_ = crate::leanh::lean_ctor_get(v_inst_795_, 0);
    crate::leanh::lean_inc(v_map_799_);
    crate::leanh::lean_dec_ref(v_inst_795_);
    v___f_800_ = l_StateT_run_x27___redArg___closed__0;
    v___x_801_ = crate::leanh::lean_apply_1(v_x_797_, v_s_798_);
    v___x_802_ = crate::leanh::lean_apply_4(
        v_map_799_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_800_,
        v___x_801_,
    );
    return v___x_802_;
}
pub unsafe fn l_StateT_pure___redArg(
    mut v_inst_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_s_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_809_: u8 = 0;
    let mut v_toPure_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_unused_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_806_ = crate::leanh::lean_ctor_get(v_inst_803_, 0);
                v_isSharedCheck_815_ = (!crate::leanh::lean_is_exclusive(v_inst_803_)) as u8;
                if v_isSharedCheck_815_ == 0 {
                    v_unused_816_ = crate::leanh::lean_ctor_get(v_inst_803_, 1);
                    crate::leanh::lean_dec(v_unused_816_);
                    v___x_808_ = v_inst_803_;
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_806_);
                    crate::leanh::lean_dec(v_inst_803_);
                    v___x_808_ = crate::leanh::lean_box(0);
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_810_ = crate::leanh::lean_ctor_get(v_toApplicative_806_, 1);
                crate::leanh::lean_inc(v_toPure_810_);
                crate::leanh::lean_dec_ref(v_toApplicative_806_);
                if v_isShared_809_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_808_, 1, v_s_805_);
                    crate::leanh::lean_ctor_set(v___x_808_, 0, v_a_804_);
                    v___x_812_ = v___x_808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 1, v_s_805_);
                    v___x_812_ = v_reuseFailAlloc_814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_813_ = crate::leanh::lean_apply_2(
                    v_toPure_810_,
                    crate::leanh::lean_box(0),
                    v___x_812_,
                );
                return v___x_813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_pure(
    mut v_00_u03c3_817_: *mut crate::leanh::LeanObject,
    mut v_m_818_: *mut crate::leanh::LeanObject,
    mut v_inst_819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_s_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_unused_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_823_ = crate::leanh::lean_ctor_get(v_inst_819_, 0);
                v_isSharedCheck_832_ = (!crate::leanh::lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_832_ == 0 {
                    v_unused_833_ = crate::leanh::lean_ctor_get(v_inst_819_, 1);
                    crate::leanh::lean_dec(v_unused_833_);
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_823_);
                    crate::leanh::lean_dec(v_inst_819_);
                    v___x_825_ = crate::leanh::lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = crate::leanh::lean_ctor_get(v_toApplicative_823_, 1);
                crate::leanh::lean_inc(v_toPure_827_);
                crate::leanh::lean_dec_ref(v_toApplicative_823_);
                if v_isShared_826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_825_, 1, v_s_822_);
                    crate::leanh::lean_ctor_set(v___x_825_, 0, v_a_821_);
                    v___x_829_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 1, v_s_822_);
                    v___x_829_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_830_ = crate::leanh::lean_apply_2(
                    v_toPure_827_,
                    crate::leanh::lean_box(0),
                    v___x_829_,
                );
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_bind___redArg___lam__0(
    mut v_f_834_: *mut crate::leanh::LeanObject,
    mut v_____x_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_836_ = crate::leanh::lean_ctor_get(v_____x_835_, 0);
    crate::leanh::lean_inc(v_fst_836_);
    v_snd_837_ = crate::leanh::lean_ctor_get(v_____x_835_, 1);
    crate::leanh::lean_inc(v_snd_837_);
    crate::leanh::lean_dec_ref(v_____x_835_);
    v___x_838_ = crate::leanh::lean_apply_2(v_f_834_, v_fst_836_, v_snd_837_);
    return v___x_838_;
}
pub unsafe fn l_StateT_bind___redArg(
    mut v_inst_839_: *mut crate::leanh::LeanObject,
    mut v_x_840_: *mut crate::leanh::LeanObject,
    mut v_f_841_: *mut crate::leanh::LeanObject,
    mut v_s_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_843_ = crate::leanh::lean_ctor_get(v_inst_839_, 1);
    crate::leanh::lean_inc(v_toBind_843_);
    crate::leanh::lean_dec_ref(v_inst_839_);
    v___f_844_ = crate::leanh::lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_844_, 0, v_f_841_);
    v___x_845_ = crate::leanh::lean_apply_1(v_x_840_, v_s_842_);
    v___x_846_ = crate::leanh::lean_apply_4(
        v_toBind_843_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_845_,
        v___f_844_,
    );
    return v___x_846_;
}
pub unsafe fn l_StateT_bind(
    mut v_00_u03c3_847_: *mut crate::leanh::LeanObject,
    mut v_m_848_: *mut crate::leanh::LeanObject,
    mut v_inst_849_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_851_: *mut crate::leanh::LeanObject,
    mut v_x_852_: *mut crate::leanh::LeanObject,
    mut v_f_853_: *mut crate::leanh::LeanObject,
    mut v_s_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_855_ = crate::leanh::lean_ctor_get(v_inst_849_, 1);
    crate::leanh::lean_inc(v_toBind_855_);
    crate::leanh::lean_dec_ref(v_inst_849_);
    v___f_856_ = crate::leanh::lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_856_, 0, v_f_853_);
    v___x_857_ = crate::leanh::lean_apply_1(v_x_852_, v_s_854_);
    v___x_858_ = crate::leanh::lean_apply_4(
        v_toBind_855_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_857_,
        v___f_856_,
    );
    return v___x_858_;
}
pub unsafe fn l_StateT_map___redArg___lam__0(
    mut v_f_859_: *mut crate::leanh::LeanObject,
    mut v_toPure_860_: *mut crate::leanh::LeanObject,
    mut v_____x_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_862_ = crate::leanh::lean_ctor_get(v_____x_861_, 0);
                v_snd_863_ = crate::leanh::lean_ctor_get(v_____x_861_, 1);
                v_isSharedCheck_872_ = (!crate::leanh::lean_is_exclusive(v_____x_861_)) as u8;
                if v_isSharedCheck_872_ == 0 {
                    v___x_865_ = v_____x_861_;
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_863_);
                    crate::leanh::lean_inc(v_fst_862_);
                    crate::leanh::lean_dec(v_____x_861_);
                    v___x_865_ = crate::leanh::lean_box(0);
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_867_ = crate::leanh::lean_apply_1(v_f_859_, v_fst_862_);
                if v_isShared_866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_867_);
                    v___x_869_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_863_);
                    v___x_869_ = v_reuseFailAlloc_871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_870_ = crate::leanh::lean_apply_2(
                    v_toPure_860_,
                    crate::leanh::lean_box(0),
                    v___x_869_,
                );
                return v___x_870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_map___redArg(
    mut v_inst_873_: *mut crate::leanh::LeanObject,
    mut v_f_874_: *mut crate::leanh::LeanObject,
    mut v_x_875_: *mut crate::leanh::LeanObject,
    mut v_s_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_877_ = crate::leanh::lean_ctor_get(v_inst_873_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_877_);
    v_toBind_878_ = crate::leanh::lean_ctor_get(v_inst_873_, 1);
    crate::leanh::lean_inc(v_toBind_878_);
    crate::leanh::lean_dec_ref(v_inst_873_);
    v_toPure_879_ = crate::leanh::lean_ctor_get(v_toApplicative_877_, 1);
    crate::leanh::lean_inc(v_toPure_879_);
    crate::leanh::lean_dec_ref(v_toApplicative_877_);
    v___x_880_ = crate::leanh::lean_apply_1(v_x_875_, v_s_876_);
    v___f_881_ = crate::leanh::lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_881_, 0, v_f_874_);
    crate::leanh::lean_closure_set(v___f_881_, 1, v_toPure_879_);
    v___x_882_ = crate::leanh::lean_apply_4(
        v_toBind_878_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_880_,
        v___f_881_,
    );
    return v___x_882_;
}
pub unsafe fn l_StateT_map(
    mut v_00_u03c3_883_: *mut crate::leanh::LeanObject,
    mut v_m_884_: *mut crate::leanh::LeanObject,
    mut v_inst_885_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_887_: *mut crate::leanh::LeanObject,
    mut v_f_888_: *mut crate::leanh::LeanObject,
    mut v_x_889_: *mut crate::leanh::LeanObject,
    mut v_s_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_891_ = crate::leanh::lean_ctor_get(v_inst_885_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_891_);
    v_toBind_892_ = crate::leanh::lean_ctor_get(v_inst_885_, 1);
    crate::leanh::lean_inc(v_toBind_892_);
    crate::leanh::lean_dec_ref(v_inst_885_);
    v_toPure_893_ = crate::leanh::lean_ctor_get(v_toApplicative_891_, 1);
    crate::leanh::lean_inc(v_toPure_893_);
    crate::leanh::lean_dec_ref(v_toApplicative_891_);
    v___x_894_ = crate::leanh::lean_apply_1(v_x_889_, v_s_890_);
    v___f_895_ = crate::leanh::lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_895_, 0, v_f_888_);
    crate::leanh::lean_closure_set(v___f_895_, 1, v_toPure_893_);
    v___x_896_ = crate::leanh::lean_apply_4(
        v_toBind_892_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_894_,
        v___f_895_,
    );
    return v___x_896_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__0(
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v_toPure_898_: *mut crate::leanh::LeanObject,
    mut v_____x_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_900_ = crate::leanh::lean_ctor_get(v_____x_899_, 1);
                v_isSharedCheck_908_ = (!crate::leanh::lean_is_exclusive(v_____x_899_)) as u8;
                if v_isSharedCheck_908_ == 0 {
                    v_unused_909_ = crate::leanh::lean_ctor_get(v_____x_899_, 0);
                    crate::leanh::lean_dec(v_unused_909_);
                    v___x_902_ = v_____x_899_;
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_900_);
                    crate::leanh::lean_dec(v_____x_899_);
                    v___x_902_ = crate::leanh::lean_box(0);
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_902_, 0, v___y_897_);
                    v___x_905_ = v___x_902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___y_897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_900_);
                    v___x_905_ = v_reuseFailAlloc_907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_906_ = crate::leanh::lean_apply_2(
                    v_toPure_898_,
                    crate::leanh::lean_box(0),
                    v___x_905_,
                );
                return v___x_906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__1(
    mut v_inst_910_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_911_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_916_ = crate::leanh::lean_ctor_get(v_inst_910_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_916_);
    v_toBind_917_ = crate::leanh::lean_ctor_get(v_inst_910_, 1);
    crate::leanh::lean_inc(v_toBind_917_);
    crate::leanh::lean_dec_ref(v_inst_910_);
    v_toPure_918_ = crate::leanh::lean_ctor_get(v_toApplicative_916_, 1);
    crate::leanh::lean_inc(v_toPure_918_);
    crate::leanh::lean_dec_ref(v_toApplicative_916_);
    v___x_919_ = crate::leanh::lean_apply_1(v___y_914_, v___y_915_);
    v___f_920_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_920_, 0, v___y_913_);
    crate::leanh::lean_closure_set(v___f_920_, 1, v_toPure_918_);
    v___x_921_ = crate::leanh::lean_apply_4(
        v_toBind_917_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_919_,
        v___f_920_,
    );
    return v___x_921_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__2(
    mut v_fst_922_: *mut crate::leanh::LeanObject,
    mut v_toPure_923_: *mut crate::leanh::LeanObject,
    mut v_____x_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_925_ = crate::leanh::lean_ctor_get(v_____x_924_, 0);
                v_snd_926_ = crate::leanh::lean_ctor_get(v_____x_924_, 1);
                v_isSharedCheck_935_ = (!crate::leanh::lean_is_exclusive(v_____x_924_)) as u8;
                if v_isSharedCheck_935_ == 0 {
                    v___x_928_ = v_____x_924_;
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_926_);
                    crate::leanh::lean_inc(v_fst_925_);
                    crate::leanh::lean_dec(v_____x_924_);
                    v___x_928_ = crate::leanh::lean_box(0);
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_930_ = crate::leanh::lean_apply_1(v_fst_922_, v_fst_925_);
                if v_isShared_929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_930_);
                    v___x_932_ = v___x_928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 1, v_snd_926_);
                    v___x_932_ = v_reuseFailAlloc_934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_933_ = crate::leanh::lean_apply_2(
                    v_toPure_923_,
                    crate::leanh::lean_box(0),
                    v___x_932_,
                );
                return v___x_933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__3(
    mut v_toApplicative_936_: *mut crate::leanh::LeanObject,
    mut v_x_937_: *mut crate::leanh::LeanObject,
    mut v_toBind_938_: *mut crate::leanh::LeanObject,
    mut v_____x_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_940_ = crate::leanh::lean_ctor_get(v_____x_939_, 0);
    crate::leanh::lean_inc(v_fst_940_);
    v_snd_941_ = crate::leanh::lean_ctor_get(v_____x_939_, 1);
    crate::leanh::lean_inc(v_snd_941_);
    crate::leanh::lean_dec_ref(v_____x_939_);
    v_toPure_942_ = crate::leanh::lean_ctor_get(v_toApplicative_936_, 1);
    crate::leanh::lean_inc(v_toPure_942_);
    crate::leanh::lean_dec_ref(v_toApplicative_936_);
    v___x_943_ = crate::leanh::lean_box(0);
    v___x_944_ = crate::leanh::lean_apply_2(v_x_937_, v___x_943_, v_snd_941_);
    v___f_945_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_945_, 0, v_fst_940_);
    crate::leanh::lean_closure_set(v___f_945_, 1, v_toPure_942_);
    v___x_946_ = crate::leanh::lean_apply_4(
        v_toBind_938_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_944_,
        v___f_945_,
    );
    return v___x_946_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__4(
    mut v_inst_947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_949_: *mut crate::leanh::LeanObject,
    mut v_f_950_: *mut crate::leanh::LeanObject,
    mut v_x_951_: *mut crate::leanh::LeanObject,
    mut v___y_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_953_ = crate::leanh::lean_ctor_get(v_inst_947_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_953_);
    v_toBind_954_ = crate::leanh::lean_ctor_get(v_inst_947_, 1);
    crate::leanh::lean_inc_n(v_toBind_954_, 2);
    crate::leanh::lean_dec_ref(v_inst_947_);
    v___f_955_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_955_, 0, v_toApplicative_953_);
    crate::leanh::lean_closure_set(v___f_955_, 1, v_x_951_);
    crate::leanh::lean_closure_set(v___f_955_, 2, v_toBind_954_);
    v___x_956_ = crate::leanh::lean_apply_1(v_f_950_, v___y_952_);
    v___x_957_ = crate::leanh::lean_apply_4(
        v_toBind_954_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_956_,
        v___f_955_,
    );
    return v___x_957_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__5(
    mut v_toApplicative_958_: *mut crate::leanh::LeanObject,
    mut v_fst_959_: *mut crate::leanh::LeanObject,
    mut v_____x_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_toPure_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_unused_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_961_ = crate::leanh::lean_ctor_get(v_____x_960_, 1);
                v_isSharedCheck_970_ = (!crate::leanh::lean_is_exclusive(v_____x_960_)) as u8;
                if v_isSharedCheck_970_ == 0 {
                    v_unused_971_ = crate::leanh::lean_ctor_get(v_____x_960_, 0);
                    crate::leanh::lean_dec(v_unused_971_);
                    v___x_963_ = v_____x_960_;
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_961_);
                    crate::leanh::lean_dec(v_____x_960_);
                    v___x_963_ = crate::leanh::lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_965_ = crate::leanh::lean_ctor_get(v_toApplicative_958_, 1);
                crate::leanh::lean_inc(v_toPure_965_);
                crate::leanh::lean_dec_ref(v_toApplicative_958_);
                if v_isShared_964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_963_, 0, v_fst_959_);
                    v___x_967_ = v___x_963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_969_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_961_);
                    v___x_967_ = v_reuseFailAlloc_969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_968_ = crate::leanh::lean_apply_2(
                    v_toPure_965_,
                    crate::leanh::lean_box(0),
                    v___x_967_,
                );
                return v___x_968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__6(
    mut v_toApplicative_972_: *mut crate::leanh::LeanObject,
    mut v_y_973_: *mut crate::leanh::LeanObject,
    mut v_toBind_974_: *mut crate::leanh::LeanObject,
    mut v_____x_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_976_ = crate::leanh::lean_ctor_get(v_____x_975_, 0);
    crate::leanh::lean_inc(v_fst_976_);
    v_snd_977_ = crate::leanh::lean_ctor_get(v_____x_975_, 1);
    crate::leanh::lean_inc(v_snd_977_);
    crate::leanh::lean_dec_ref(v_____x_975_);
    v___f_978_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_978_, 0, v_toApplicative_972_);
    crate::leanh::lean_closure_set(v___f_978_, 1, v_fst_976_);
    v___x_979_ = crate::leanh::lean_box(0);
    v___x_980_ = crate::leanh::lean_apply_2(v_y_973_, v___x_979_, v_snd_977_);
    v___x_981_ = crate::leanh::lean_apply_4(
        v_toBind_974_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_980_,
        v___f_978_,
    );
    return v___x_981_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__7(
    mut v_inst_982_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_983_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_984_: *mut crate::leanh::LeanObject,
    mut v_x_985_: *mut crate::leanh::LeanObject,
    mut v_y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_988_ = crate::leanh::lean_ctor_get(v_inst_982_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_988_);
    v_toBind_989_ = crate::leanh::lean_ctor_get(v_inst_982_, 1);
    crate::leanh::lean_inc_n(v_toBind_989_, 2);
    crate::leanh::lean_dec_ref(v_inst_982_);
    v___f_990_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_990_, 0, v_toApplicative_988_);
    crate::leanh::lean_closure_set(v___f_990_, 1, v_y_986_);
    crate::leanh::lean_closure_set(v___f_990_, 2, v_toBind_989_);
    v___x_991_ = crate::leanh::lean_apply_1(v_x_985_, v___y_987_);
    v___x_992_ = crate::leanh::lean_apply_4(
        v_toBind_989_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_991_,
        v___f_990_,
    );
    return v___x_992_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__8(
    mut v_y_993_: *mut crate::leanh::LeanObject,
    mut v_____x_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_995_ = crate::leanh::lean_ctor_get(v_____x_994_, 1);
    crate::leanh::lean_inc(v_snd_995_);
    crate::leanh::lean_dec_ref(v_____x_994_);
    v___x_996_ = crate::leanh::lean_box(0);
    v___x_997_ = crate::leanh::lean_apply_2(v_y_993_, v___x_996_, v_snd_995_);
    return v___x_997_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__9(
    mut v_inst_998_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_999_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1000_: *mut crate::leanh::LeanObject,
    mut v_x_1001_: *mut crate::leanh::LeanObject,
    mut v_y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1004_ = crate::leanh::lean_ctor_get(v_inst_998_, 1);
    crate::leanh::lean_inc(v_toBind_1004_);
    crate::leanh::lean_dec_ref(v_inst_998_);
    v___f_1005_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1005_, 0, v_y_1002_);
    v___x_1006_ = crate::leanh::lean_apply_1(v_x_1001_, v___y_1003_);
    v___x_1007_ = crate::leanh::lean_apply_4(
        v_toBind_1004_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1006_,
        v___f_1005_,
    );
    return v___x_1007_;
}
pub unsafe fn l_StateT_instMonad___redArg(
    mut v_inst_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1008_, 6);
    v___f_1009_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1009_, 0, v_inst_1008_);
    v___f_1010_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1010_, 0, v_inst_1008_);
    v___f_1011_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1011_, 0, v_inst_1008_);
    v___f_1012_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1012_, 0, v_inst_1008_);
    v___x_1013_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1013_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1013_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1013_, 2, v_inst_1008_);
    v___x_1014_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1014_, 0, v___x_1013_);
    crate::leanh::lean_ctor_set(v___x_1014_, 1, v___f_1009_);
    v___x_1015_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1015_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1015_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1015_, 2, v_inst_1008_);
    v___x_1016_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1014_);
    crate::leanh::lean_ctor_set(v___x_1016_, 1, v___x_1015_);
    crate::leanh::lean_ctor_set(v___x_1016_, 2, v___f_1010_);
    crate::leanh::lean_ctor_set(v___x_1016_, 3, v___f_1011_);
    crate::leanh::lean_ctor_set(v___x_1016_, 4, v___f_1012_);
    v___x_1017_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1017_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1017_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1017_, 2, v_inst_1008_);
    v___x_1018_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1016_);
    crate::leanh::lean_ctor_set(v___x_1018_, 1, v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_StateT_instMonad(
    mut v_00_u03c3_1019_: *mut crate::leanh::LeanObject,
    mut v_m_1020_: *mut crate::leanh::LeanObject,
    mut v_inst_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1021_, 6);
    v___f_1022_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1022_, 0, v_inst_1021_);
    v___f_1023_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1023_, 0, v_inst_1021_);
    v___f_1024_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1024_, 0, v_inst_1021_);
    v___f_1025_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1025_, 0, v_inst_1021_);
    v___x_1026_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1026_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1026_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1026_, 2, v_inst_1021_);
    v___x_1027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    crate::leanh::lean_ctor_set(v___x_1027_, 1, v___f_1022_);
    v___x_1028_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1028_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1028_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1028_, 2, v_inst_1021_);
    v___x_1029_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1029_, 0, v___x_1027_);
    crate::leanh::lean_ctor_set(v___x_1029_, 1, v___x_1028_);
    crate::leanh::lean_ctor_set(v___x_1029_, 2, v___f_1023_);
    crate::leanh::lean_ctor_set(v___x_1029_, 3, v___f_1024_);
    crate::leanh::lean_ctor_set(v___x_1029_, 4, v___f_1025_);
    v___x_1030_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1030_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1030_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1030_, 2, v_inst_1021_);
    v___x_1031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    crate::leanh::lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn l_StateT_orElse___redArg___lam__0(
    mut v_x_u2082_1032_: *mut crate::leanh::LeanObject,
    mut v_s_1033_: *mut crate::leanh::LeanObject,
    mut v_x_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = crate::leanh::lean_box(0);
    v___x_1036_ = crate::leanh::lean_apply_2(v_x_u2082_1032_, v___x_1035_, v_s_1033_);
    return v___x_1036_;
}
pub unsafe fn l_StateT_orElse___redArg(
    mut v_inst_1037_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1038_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1039_: *mut crate::leanh::LeanObject,
    mut v_s_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1041_ = crate::leanh::lean_ctor_get(v_inst_1037_, 2);
    crate::leanh::lean_inc(v_orElse_1041_);
    crate::leanh::lean_dec_ref(v_inst_1037_);
    crate::leanh::lean_inc(v_s_1040_);
    v___f_1042_ = crate::leanh::lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1042_, 0, v_x_u2082_1039_);
    crate::leanh::lean_closure_set(v___f_1042_, 1, v_s_1040_);
    v___x_1043_ = crate::leanh::lean_apply_1(v_x_u2081_1038_, v_s_1040_);
    v___x_1044_ = crate::leanh::lean_apply_3(
        v_orElse_1041_,
        crate::leanh::lean_box(0),
        v___x_1043_,
        v___f_1042_,
    );
    return v___x_1044_;
}
pub unsafe fn l_StateT_orElse(
    mut v_00_u03c3_1045_: *mut crate::leanh::LeanObject,
    mut v_m_1046_: *mut crate::leanh::LeanObject,
    mut v_inst_1047_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1048_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1049_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1050_: *mut crate::leanh::LeanObject,
    mut v_s_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1052_ = crate::leanh::lean_ctor_get(v_inst_1047_, 2);
    crate::leanh::lean_inc(v_orElse_1052_);
    crate::leanh::lean_dec_ref(v_inst_1047_);
    crate::leanh::lean_inc(v_s_1051_);
    v___f_1053_ = crate::leanh::lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1053_, 0, v_x_u2082_1050_);
    crate::leanh::lean_closure_set(v___f_1053_, 1, v_s_1051_);
    v___x_1054_ = crate::leanh::lean_apply_1(v_x_u2081_1049_, v_s_1051_);
    v___x_1055_ = crate::leanh::lean_apply_3(
        v_orElse_1052_,
        crate::leanh::lean_box(0),
        v___x_1054_,
        v___f_1053_,
    );
    return v___x_1055_;
}
pub unsafe fn l_StateT_failure___redArg(
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_1057_ = crate::leanh::lean_ctor_get(v_inst_1056_, 1);
    crate::leanh::lean_inc(v_failure_1057_);
    crate::leanh::lean_dec_ref(v_inst_1056_);
    v___x_1058_ = crate::leanh::lean_apply_1(v_failure_1057_, crate::leanh::lean_box(0));
    return v___x_1058_;
}
pub unsafe fn l_StateT_failure(
    mut v_00_u03c3_1059_: *mut crate::leanh::LeanObject,
    mut v_m_1060_: *mut crate::leanh::LeanObject,
    mut v_inst_1061_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1062_: *mut crate::leanh::LeanObject,
    mut v_x_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_1064_ = crate::leanh::lean_ctor_get(v_inst_1061_, 1);
    crate::leanh::lean_inc(v_failure_1064_);
    crate::leanh::lean_dec_ref(v_inst_1061_);
    v___x_1065_ = crate::leanh::lean_apply_1(v_failure_1064_, crate::leanh::lean_box(0));
    return v___x_1065_;
}
pub unsafe fn l_StateT_failure___boxed(
    mut v_00_u03c3_1066_: *mut crate::leanh::LeanObject,
    mut v_m_1067_: *mut crate::leanh::LeanObject,
    mut v_inst_1068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1069_: *mut crate::leanh::LeanObject,
    mut v_x_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_StateT_failure(
        v_00_u03c3_1066_,
        v_m_1067_,
        v_inst_1068_,
        v_00_u03b1_1069_,
        v_x_1070_,
    );
    crate::leanh::lean_dec(v_x_1070_);
    return v_res_1071_;
}
pub unsafe fn l_StateT_instAlternative___redArg(
    mut v_inst_1072_: *mut crate::leanh::LeanObject,
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1072_, 5);
    v___f_1074_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1074_, 0, v_inst_1072_);
    v___f_1075_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1075_, 0, v_inst_1072_);
    v___f_1076_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1076_, 0, v_inst_1072_);
    v___f_1077_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1077_, 0, v_inst_1072_);
    v___x_1078_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1078_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1078_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1078_, 2, v_inst_1072_);
    v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    crate::leanh::lean_ctor_set(v___x_1079_, 1, v___f_1074_);
    v___x_1080_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1080_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1080_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1080_, 2, v_inst_1072_);
    v___x_1081_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 1, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 2, v___f_1075_);
    crate::leanh::lean_ctor_set(v___x_1081_, 3, v___f_1076_);
    crate::leanh::lean_ctor_set(v___x_1081_, 4, v___f_1077_);
    crate::leanh::lean_inc_ref(v_inst_1073_);
    v___x_1082_ =
        crate::leanh::lean_alloc_closure(l_StateT_failure___boxed as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_1082_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1082_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1082_, 2, v_inst_1073_);
    v___x_1083_ = crate::leanh::lean_alloc_closure(l_StateT_orElse as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_1083_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1083_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1083_, 2, v_inst_1073_);
    v___x_1084_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1084_, 0, v___x_1081_);
    crate::leanh::lean_ctor_set(v___x_1084_, 1, v___x_1082_);
    crate::leanh::lean_ctor_set(v___x_1084_, 2, v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_StateT_instAlternative(
    mut v_00_u03c3_1085_: *mut crate::leanh::LeanObject,
    mut v_m_1086_: *mut crate::leanh::LeanObject,
    mut v_inst_1087_: *mut crate::leanh::LeanObject,
    mut v_inst_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_StateT_instAlternative___redArg(v_inst_1087_, v_inst_1088_);
    return v___x_1089_;
}
pub unsafe fn l_StateT_get___redArg(
    mut v_inst_1090_: *mut crate::leanh::LeanObject,
    mut v_s_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v_toPure_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_unused_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1092_ = crate::leanh::lean_ctor_get(v_inst_1090_, 0);
                v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v_inst_1090_)) as u8;
                if v_isSharedCheck_1101_ == 0 {
                    v_unused_1102_ = crate::leanh::lean_ctor_get(v_inst_1090_, 1);
                    crate::leanh::lean_dec(v_unused_1102_);
                    v___x_1094_ = v_inst_1090_;
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1092_);
                    crate::leanh::lean_dec(v_inst_1090_);
                    v___x_1094_ = crate::leanh::lean_box(0);
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1096_ = crate::leanh::lean_ctor_get(v_toApplicative_1092_, 1);
                crate::leanh::lean_inc(v_toPure_1096_);
                crate::leanh::lean_dec_ref(v_toApplicative_1092_);
                crate::leanh::lean_inc(v_s_1091_);
                if v_isShared_1095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1094_, 1, v_s_1091_);
                    crate::leanh::lean_ctor_set(v___x_1094_, 0, v_s_1091_);
                    v___x_1098_ = v___x_1094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_s_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_s_1091_);
                    v___x_1098_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = crate::leanh::lean_apply_2(
                    v_toPure_1096_,
                    crate::leanh::lean_box(0),
                    v___x_1098_,
                );
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_get(
    mut v_00_u03c3_1103_: *mut crate::leanh::LeanObject,
    mut v_m_1104_: *mut crate::leanh::LeanObject,
    mut v_inst_1105_: *mut crate::leanh::LeanObject,
    mut v_s_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v_toPure_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_unused_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1107_ = crate::leanh::lean_ctor_get(v_inst_1105_, 0);
                v_isSharedCheck_1116_ = (!crate::leanh::lean_is_exclusive(v_inst_1105_)) as u8;
                if v_isSharedCheck_1116_ == 0 {
                    v_unused_1117_ = crate::leanh::lean_ctor_get(v_inst_1105_, 1);
                    crate::leanh::lean_dec(v_unused_1117_);
                    v___x_1109_ = v_inst_1105_;
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1107_);
                    crate::leanh::lean_dec(v_inst_1105_);
                    v___x_1109_ = crate::leanh::lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1111_ = crate::leanh::lean_ctor_get(v_toApplicative_1107_, 1);
                crate::leanh::lean_inc(v_toPure_1111_);
                crate::leanh::lean_dec_ref(v_toApplicative_1107_);
                crate::leanh::lean_inc(v_s_1106_);
                if v_isShared_1110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1109_, 1, v_s_1106_);
                    crate::leanh::lean_ctor_set(v___x_1109_, 0, v_s_1106_);
                    v___x_1113_ = v___x_1109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_s_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_s_1106_);
                    v___x_1113_ = v_reuseFailAlloc_1115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1114_ = crate::leanh::lean_apply_2(
                    v_toPure_1111_,
                    crate::leanh::lean_box(0),
                    v___x_1113_,
                );
                return v___x_1114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___redArg(
    mut v_inst_1118_: *mut crate::leanh::LeanObject,
    mut v_s_x27_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v_toPure_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_unused_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1120_ = crate::leanh::lean_ctor_get(v_inst_1118_, 0);
                v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v_inst_1118_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v_unused_1131_ = crate::leanh::lean_ctor_get(v_inst_1118_, 1);
                    crate::leanh::lean_dec(v_unused_1131_);
                    v___x_1122_ = v_inst_1118_;
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1120_);
                    crate::leanh::lean_dec(v_inst_1118_);
                    v___x_1122_ = crate::leanh::lean_box(0);
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1124_ = crate::leanh::lean_ctor_get(v_toApplicative_1120_, 1);
                crate::leanh::lean_inc(v_toPure_1124_);
                crate::leanh::lean_dec_ref(v_toApplicative_1120_);
                v___x_1125_ = crate::leanh::lean_box(0);
                if v_isShared_1123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1122_, 1, v_s_x27_1119_);
                    crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1125_);
                    v___x_1127_ = v___x_1122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_s_x27_1119_);
                    v___x_1127_ = v_reuseFailAlloc_1129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1128_ = crate::leanh::lean_apply_2(
                    v_toPure_1124_,
                    crate::leanh::lean_box(0),
                    v___x_1127_,
                );
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set(
    mut v_00_u03c3_1132_: *mut crate::leanh::LeanObject,
    mut v_m_1133_: *mut crate::leanh::LeanObject,
    mut v_inst_1134_: *mut crate::leanh::LeanObject,
    mut v_s_x27_1135_: *mut crate::leanh::LeanObject,
    mut v_x_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v_toPure_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_unused_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1137_ = crate::leanh::lean_ctor_get(v_inst_1134_, 0);
                v_isSharedCheck_1147_ = (!crate::leanh::lean_is_exclusive(v_inst_1134_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v_unused_1148_ = crate::leanh::lean_ctor_get(v_inst_1134_, 1);
                    crate::leanh::lean_dec(v_unused_1148_);
                    v___x_1139_ = v_inst_1134_;
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1137_);
                    crate::leanh::lean_dec(v_inst_1134_);
                    v___x_1139_ = crate::leanh::lean_box(0);
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1141_ = crate::leanh::lean_ctor_get(v_toApplicative_1137_, 1);
                crate::leanh::lean_inc(v_toPure_1141_);
                crate::leanh::lean_dec_ref(v_toApplicative_1137_);
                v___x_1142_ = crate::leanh::lean_box(0);
                if v_isShared_1140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1139_, 1, v_s_x27_1135_);
                    crate::leanh::lean_ctor_set(v___x_1139_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_s_x27_1135_);
                    v___x_1144_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1145_ = crate::leanh::lean_apply_2(
                    v_toPure_1141_,
                    crate::leanh::lean_box(0),
                    v___x_1144_,
                );
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___boxed(
    mut v_00_u03c3_1149_: *mut crate::leanh::LeanObject,
    mut v_m_1150_: *mut crate::leanh::LeanObject,
    mut v_inst_1151_: *mut crate::leanh::LeanObject,
    mut v_s_x27_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_StateT_set(
        v_00_u03c3_1149_,
        v_m_1150_,
        v_inst_1151_,
        v_s_x27_1152_,
        v_x_1153_,
    );
    crate::leanh::lean_dec(v_x_1153_);
    return v_res_1154_;
}
pub unsafe fn l_StateT_modifyGet___redArg(
    mut v_inst_1155_: *mut crate::leanh::LeanObject,
    mut v_f_1156_: *mut crate::leanh::LeanObject,
    mut v_s_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1158_ = crate::leanh::lean_ctor_get(v_inst_1155_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1158_);
    crate::leanh::lean_dec_ref(v_inst_1155_);
    v_toPure_1159_ = crate::leanh::lean_ctor_get(v_toApplicative_1158_, 1);
    crate::leanh::lean_inc(v_toPure_1159_);
    crate::leanh::lean_dec_ref(v_toApplicative_1158_);
    v___x_1160_ = crate::leanh::lean_apply_1(v_f_1156_, v_s_1157_);
    v___x_1161_ =
        crate::leanh::lean_apply_2(v_toPure_1159_, crate::leanh::lean_box(0), v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_StateT_modifyGet(
    mut v_00_u03c3_1162_: *mut crate::leanh::LeanObject,
    mut v_m_1163_: *mut crate::leanh::LeanObject,
    mut v_inst_1164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1165_: *mut crate::leanh::LeanObject,
    mut v_f_1166_: *mut crate::leanh::LeanObject,
    mut v_s_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1168_ = crate::leanh::lean_ctor_get(v_inst_1164_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1168_);
    crate::leanh::lean_dec_ref(v_inst_1164_);
    v_toPure_1169_ = crate::leanh::lean_ctor_get(v_toApplicative_1168_, 1);
    crate::leanh::lean_inc(v_toPure_1169_);
    crate::leanh::lean_dec_ref(v_toApplicative_1168_);
    v___x_1170_ = crate::leanh::lean_apply_1(v_f_1166_, v_s_1167_);
    v___x_1171_ =
        crate::leanh::lean_apply_2(v_toPure_1169_, crate::leanh::lean_box(0), v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_StateT_lift___redArg___lam__0(
    mut v_s_1172_: *mut crate::leanh::LeanObject,
    mut v_toPure_1173_: *mut crate::leanh::LeanObject,
    mut v_a_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1175_, 0, v_a_1174_);
    crate::leanh::lean_ctor_set(v___x_1175_, 1, v_s_1172_);
    v___x_1176_ =
        crate::leanh::lean_apply_2(v_toPure_1173_, crate::leanh::lean_box(0), v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn l_StateT_lift___redArg(
    mut v_inst_1177_: *mut crate::leanh::LeanObject,
    mut v_t_1178_: *mut crate::leanh::LeanObject,
    mut v_s_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1180_ = crate::leanh::lean_ctor_get(v_inst_1177_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1180_);
    v_toBind_1181_ = crate::leanh::lean_ctor_get(v_inst_1177_, 1);
    crate::leanh::lean_inc(v_toBind_1181_);
    crate::leanh::lean_dec_ref(v_inst_1177_);
    v_toPure_1182_ = crate::leanh::lean_ctor_get(v_toApplicative_1180_, 1);
    crate::leanh::lean_inc(v_toPure_1182_);
    crate::leanh::lean_dec_ref(v_toApplicative_1180_);
    v___f_1183_ = crate::leanh::lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1183_, 0, v_s_1179_);
    crate::leanh::lean_closure_set(v___f_1183_, 1, v_toPure_1182_);
    v___x_1184_ = crate::leanh::lean_apply_4(
        v_toBind_1181_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_t_1178_,
        v___f_1183_,
    );
    return v___x_1184_;
}
pub unsafe fn l_StateT_lift(
    mut v_00_u03c3_1185_: *mut crate::leanh::LeanObject,
    mut v_m_1186_: *mut crate::leanh::LeanObject,
    mut v_inst_1187_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1188_: *mut crate::leanh::LeanObject,
    mut v_t_1189_: *mut crate::leanh::LeanObject,
    mut v_s_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1191_ = crate::leanh::lean_ctor_get(v_inst_1187_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1191_);
    v_toBind_1192_ = crate::leanh::lean_ctor_get(v_inst_1187_, 1);
    crate::leanh::lean_inc(v_toBind_1192_);
    crate::leanh::lean_dec_ref(v_inst_1187_);
    v_toPure_1193_ = crate::leanh::lean_ctor_get(v_toApplicative_1191_, 1);
    crate::leanh::lean_inc(v_toPure_1193_);
    crate::leanh::lean_dec_ref(v_toApplicative_1191_);
    v___f_1194_ = crate::leanh::lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1194_, 0, v_s_1190_);
    crate::leanh::lean_closure_set(v___f_1194_, 1, v_toPure_1193_);
    v___x_1195_ = crate::leanh::lean_apply_4(
        v_toBind_1192_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_t_1189_,
        v___f_1194_,
    );
    return v___x_1195_;
}
pub unsafe fn l_StateT_instMonadLift___redArg(
    mut v_inst_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = crate::leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1197_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1197_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1197_, 2, v_inst_1196_);
    return v___x_1197_;
}
pub unsafe fn l_StateT_instMonadLift(
    mut v_00_u03c3_1198_: *mut crate::leanh::LeanObject,
    mut v_m_1199_: *mut crate::leanh::LeanObject,
    mut v_inst_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = crate::leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1201_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1201_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1201_, 2, v_inst_1200_);
    return v___x_1201_;
}
pub unsafe fn l_StateT_instMonadFunctor___lam__0(
    mut v_00_u03b1_1202_: *mut crate::leanh::LeanObject,
    mut v_f_1203_: *mut crate::leanh::LeanObject,
    mut v_x_1204_: *mut crate::leanh::LeanObject,
    mut v_s_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = crate::leanh::lean_apply_1(v_x_1204_, v_s_1205_);
    v___x_1207_ = crate::leanh::lean_apply_2(v_f_1203_, crate::leanh::lean_box(0), v___x_1206_);
    return v___x_1207_;
}
pub unsafe fn l_StateT_instMonadFunctor(
    mut v_00_u03c3_1209_: *mut crate::leanh::LeanObject,
    mut v_m_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1211_ = l_StateT_instMonadFunctor___closed__0;
    return v___f_1211_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__0(
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v_toPure_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1215_, 0, v_a_1214_);
    crate::leanh::lean_ctor_set(v___x_1215_, 1, v___y_1212_);
    v___x_1216_ =
        crate::leanh::lean_apply_2(v_toPure_1213_, crate::leanh::lean_box(0), v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__1(
    mut v_inst_1217_: *mut crate::leanh::LeanObject,
    mut v_inst_1218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1222_ = crate::leanh::lean_ctor_get(v_inst_1218_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1222_);
    v_throw_1223_ = crate::leanh::lean_ctor_get(v_inst_1217_, 0);
    crate::leanh::lean_inc(v_throw_1223_);
    crate::leanh::lean_dec_ref(v_inst_1217_);
    v_toBind_1224_ = crate::leanh::lean_ctor_get(v_inst_1218_, 1);
    crate::leanh::lean_inc(v_toBind_1224_);
    crate::leanh::lean_dec_ref(v_inst_1218_);
    v_toPure_1225_ = crate::leanh::lean_ctor_get(v_toApplicative_1222_, 1);
    crate::leanh::lean_inc(v_toPure_1225_);
    crate::leanh::lean_dec_ref(v_toApplicative_1222_);
    v___x_1226_ = crate::leanh::lean_apply_2(v_throw_1223_, crate::leanh::lean_box(0), v___y_1220_);
    v___f_1227_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1227_, 0, v___y_1221_);
    crate::leanh::lean_closure_set(v___f_1227_, 1, v_toPure_1225_);
    v___x_1228_ = crate::leanh::lean_apply_4(
        v_toBind_1224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1226_,
        v___f_1227_,
    );
    return v___x_1228_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__2(
    mut v_c_1229_: *mut crate::leanh::LeanObject,
    mut v_s_1230_: *mut crate::leanh::LeanObject,
    mut v_e_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = crate::leanh::lean_apply_2(v_c_1229_, v_e_1231_, v_s_1230_);
    return v___x_1232_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__3(
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1234_: *mut crate::leanh::LeanObject,
    mut v_x_1235_: *mut crate::leanh::LeanObject,
    mut v_c_1236_: *mut crate::leanh::LeanObject,
    mut v_s_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_1238_ = crate::leanh::lean_ctor_get(v_inst_1233_, 1);
    crate::leanh::lean_inc(v_tryCatch_1238_);
    crate::leanh::lean_dec_ref(v_inst_1233_);
    crate::leanh::lean_inc(v_s_1237_);
    v___f_1239_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1239_, 0, v_c_1236_);
    crate::leanh::lean_closure_set(v___f_1239_, 1, v_s_1237_);
    v___x_1240_ = crate::leanh::lean_apply_1(v_x_1235_, v_s_1237_);
    v___x_1241_ = crate::leanh::lean_apply_3(
        v_tryCatch_1238_,
        crate::leanh::lean_box(0),
        v___x_1240_,
        v___f_1239_,
    );
    return v___x_1241_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg(
    mut v_inst_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1243_);
    v___f_1244_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1244_, 0, v_inst_1243_);
    crate::leanh::lean_closure_set(v___f_1244_, 1, v_inst_1242_);
    v___f_1245_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1245_, 0, v_inst_1243_);
    v___x_1246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1246_, 0, v___f_1244_);
    crate::leanh::lean_ctor_set(v___x_1246_, 1, v___f_1245_);
    return v___x_1246_;
}
pub unsafe fn l_StateT_instMonadExceptOf(
    mut v_00_u03c3_1247_: *mut crate::leanh::LeanObject,
    mut v_m_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1250_: *mut crate::leanh::LeanObject,
    mut v_inst_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1251_);
    v___f_1252_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1252_, 0, v_inst_1251_);
    crate::leanh::lean_closure_set(v___f_1252_, 1, v_inst_1249_);
    v___f_1253_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1253_, 0, v_inst_1251_);
    v___x_1254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1254_, 0, v___f_1252_);
    crate::leanh::lean_ctor_set(v___x_1254_, 1, v___f_1253_);
    return v___x_1254_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__0(
    mut v_toPure_1255_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_a_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_1256_) == 0 {
                    v_a_1257_ = crate::leanh::lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1265_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1259_ = v_____do__lift_1256_;
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1257_);
                        crate::leanh::lean_dec(v_____do__lift_1256_);
                        v___x_1259_ = crate::leanh::lean_box(0);
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1266_ = crate::leanh::lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1276_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1268_ = v_____do__lift_1256_;
                        v_isShared_1269_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1266_);
                        crate::leanh::lean_dec(v_____do__lift_1256_);
                        v___x_1268_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1263_ = crate::leanh::lean_apply_2(
                    v_toPure_1255_,
                    crate::leanh::lean_box(0),
                    v___x_1262_,
                );
                return v___x_1263_;
            }
            3 => {
                v___x_1270_ = crate::leanh::lean_box(0);
                v___x_1271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                crate::leanh::lean_ctor_set(v___x_1271_, 1, v_a_1266_);
                if v_isShared_1269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1274_ = crate::leanh::lean_apply_2(
                    v_toPure_1255_,
                    crate::leanh::lean_box(0),
                    v___x_1273_,
                );
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ForM_forIn___redArg___lam__1(
    mut v_f_1277_: *mut crate::leanh::LeanObject,
    mut v_toBind_1278_: *mut crate::leanh::LeanObject,
    mut v___f_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_b_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = crate::leanh::lean_apply_2(v_f_1277_, v_a_1280_, v_b_1281_);
    v___x_1283_ = crate::leanh::lean_apply_4(
        v_toBind_1278_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1282_,
        v___f_1279_,
    );
    return v___x_1283_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__2(
    mut v_toPure_1284_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1285_) == 0 {
        let mut v_a_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1286_ = crate::leanh::lean_ctor_get(v_____do__lift_1285_, 0);
        crate::leanh::lean_inc(v_a_1286_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1285_, 1);
        v___x_1287_ =
            crate::leanh::lean_apply_2(v_toPure_1284_, crate::leanh::lean_box(0), v_a_1286_);
        return v___x_1287_;
    } else {
        let mut v_a_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1288_ = crate::leanh::lean_ctor_get(v_____do__lift_1285_, 0);
        crate::leanh::lean_inc(v_a_1288_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1285_, 1);
        v_snd_1289_ = crate::leanh::lean_ctor_get(v_a_1288_, 1);
        crate::leanh::lean_inc(v_snd_1289_);
        crate::leanh::lean_dec(v_a_1288_);
        v___x_1290_ =
            crate::leanh::lean_apply_2(v_toPure_1284_, crate::leanh::lean_box(0), v_snd_1289_);
        return v___x_1290_;
    }
}
pub unsafe fn l_ForM_forIn___redArg(
    mut v_inst_1291_: *mut crate::leanh::LeanObject,
    mut v_inst_1292_: *mut crate::leanh::LeanObject,
    mut v_x_1293_: *mut crate::leanh::LeanObject,
    mut v_b_1294_: *mut crate::leanh::LeanObject,
    mut v_f_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1296_ = crate::leanh::lean_ctor_get(v_inst_1291_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1296_);
    v_toBind_1297_ = crate::leanh::lean_ctor_get(v_inst_1291_, 1);
    crate::leanh::lean_inc_n(v_toBind_1297_, 2);
    crate::leanh::lean_dec_ref(v_inst_1291_);
    v_toPure_1298_ = crate::leanh::lean_ctor_get(v_toApplicative_1296_, 1);
    crate::leanh::lean_inc_n(v_toPure_1298_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1296_);
    v___f_1299_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1299_, 0, v_toPure_1298_);
    v_g_1300_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v_g_1300_, 0, v_f_1295_);
    crate::leanh::lean_closure_set(v_g_1300_, 1, v_toBind_1297_);
    crate::leanh::lean_closure_set(v_g_1300_, 2, v___f_1299_);
    v___f_1301_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1301_, 0, v_toPure_1298_);
    v___x_1302_ = crate::leanh::lean_apply_3(v_inst_1292_, v_x_1293_, v_g_1300_, v_b_1294_);
    v___x_1303_ = crate::leanh::lean_apply_4(
        v_toBind_1297_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1302_,
        v___f_1301_,
    );
    return v___x_1303_;
}
pub unsafe fn l_ForM_forIn(
    mut v_m_1304_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1305_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_1306_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1307_: *mut crate::leanh::LeanObject,
    mut v_inst_1308_: *mut crate::leanh::LeanObject,
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v_b_1311_: *mut crate::leanh::LeanObject,
    mut v_f_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1313_ = crate::leanh::lean_ctor_get(v_inst_1308_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1313_);
    v_toBind_1314_ = crate::leanh::lean_ctor_get(v_inst_1308_, 1);
    crate::leanh::lean_inc_n(v_toBind_1314_, 2);
    crate::leanh::lean_dec_ref(v_inst_1308_);
    v_toPure_1315_ = crate::leanh::lean_ctor_get(v_toApplicative_1313_, 1);
    crate::leanh::lean_inc_n(v_toPure_1315_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1313_);
    v___f_1316_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1316_, 0, v_toPure_1315_);
    v_g_1317_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v_g_1317_, 0, v_f_1312_);
    crate::leanh::lean_closure_set(v_g_1317_, 1, v_toBind_1314_);
    crate::leanh::lean_closure_set(v_g_1317_, 2, v___f_1316_);
    v___f_1318_ = crate::leanh::lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1318_, 0, v_toPure_1315_);
    v___x_1319_ = crate::leanh::lean_apply_3(v_inst_1309_, v_x_1310_, v_g_1317_, v_b_1311_);
    v___x_1320_ = crate::leanh::lean_apply_4(
        v_toBind_1314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1319_,
        v___f_1318_,
    );
    return v___x_1320_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad___redArg(
    mut v_inst_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1321_, 2);
    v___x_1322_ = crate::leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1322_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1322_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1322_, 2, v_inst_1321_);
    v___x_1323_ =
        crate::leanh::lean_alloc_closure(l_StateT_set___boxed as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_1323_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1323_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1323_, 2, v_inst_1321_);
    v___x_1324_ =
        crate::leanh::lean_alloc_closure(l_StateT_modifyGet as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1324_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1324_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1324_, 2, v_inst_1321_);
    v___x_1325_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1322_);
    crate::leanh::lean_ctor_set(v___x_1325_, 1, v___x_1323_);
    crate::leanh::lean_ctor_set(v___x_1325_, 2, v___x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad(
    mut v_00_u03c3_1326_: *mut crate::leanh::LeanObject,
    mut v_m_1327_: *mut crate::leanh::LeanObject,
    mut v_inst_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__0(
    mut v_fst_1330_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1331_: *mut crate::leanh::LeanObject,
    mut v_x_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = crate::leanh::lean_apply_1(v_x_1332_, v_fst_1330_);
    return v___x_1333_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__1(
    mut v_snd_1334_: *mut crate::leanh::LeanObject,
    mut v_toPure_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1337_, 0, v_a_1336_);
    crate::leanh::lean_ctor_set(v___x_1337_, 1, v_snd_1334_);
    v___x_1338_ =
        crate::leanh::lean_apply_2(v_toPure_1335_, crate::leanh::lean_box(0), v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__2(
    mut v_f_1339_: *mut crate::leanh::LeanObject,
    mut v_toPure_1340_: *mut crate::leanh::LeanObject,
    mut v_toBind_1341_: *mut crate::leanh::LeanObject,
    mut v_____x_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1343_ = crate::leanh::lean_ctor_get(v_____x_1342_, 0);
    crate::leanh::lean_inc(v_fst_1343_);
    v_snd_1344_ = crate::leanh::lean_ctor_get(v_____x_1342_, 1);
    crate::leanh::lean_inc(v_snd_1344_);
    crate::leanh::lean_dec_ref(v_____x_1342_);
    v___f_1345_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1345_, 0, v_fst_1343_);
    v___x_1346_ = crate::leanh::lean_apply_1(v_f_1339_, v___f_1345_);
    v___f_1347_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1347_, 0, v_snd_1344_);
    crate::leanh::lean_closure_set(v___f_1347_, 1, v_toPure_1340_);
    v___x_1348_ = crate::leanh::lean_apply_4(
        v_toBind_1341_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1346_,
        v___f_1347_,
    );
    return v___x_1348_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__3(
    mut v_inst_1349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1350_: *mut crate::leanh::LeanObject,
    mut v_f_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_toPure_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1353_ = crate::leanh::lean_ctor_get(v_inst_1349_, 0);
                v_toBind_1354_ = crate::leanh::lean_ctor_get(v_inst_1349_, 1);
                v_isSharedCheck_1365_ = (!crate::leanh::lean_is_exclusive(v_inst_1349_)) as u8;
                if v_isSharedCheck_1365_ == 0 {
                    v___x_1356_ = v_inst_1349_;
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_1354_);
                    crate::leanh::lean_inc(v_toApplicative_1353_);
                    crate::leanh::lean_dec(v_inst_1349_);
                    v___x_1356_ = crate::leanh::lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1358_ = crate::leanh::lean_ctor_get(v_toApplicative_1353_, 1);
                crate::leanh::lean_inc_n(v_toPure_1358_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_1353_);
                crate::leanh::lean_inc(v_toBind_1354_);
                v___f_1359_ = crate::leanh::lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__2 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1359_, 0, v_f_1351_);
                crate::leanh::lean_closure_set(v___f_1359_, 1, v_toPure_1358_);
                crate::leanh::lean_closure_set(v___f_1359_, 2, v_toBind_1354_);
                crate::leanh::lean_inc(v___y_1352_);
                if v_isShared_1357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1356_, 1, v___y_1352_);
                    crate::leanh::lean_ctor_set(v___x_1356_, 0, v___y_1352_);
                    v___x_1361_ = v___x_1356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1364_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___y_1352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___y_1352_);
                    v___x_1361_ = v_reuseFailAlloc_1364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1362_ = crate::leanh::lean_apply_2(
                    v_toPure_1358_,
                    crate::leanh::lean_box(0),
                    v___x_1361_,
                );
                v___x_1363_ = crate::leanh::lean_apply_4(
                    v_toBind_1354_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_fst_1366_: *mut crate::leanh::LeanObject,
    mut v_toPure_1367_: *mut crate::leanh::LeanObject,
    mut v_____x_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_unused_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1369_ = crate::leanh::lean_ctor_get(v_____x_1368_, 1);
                v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v_____x_1368_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v_unused_1378_ = crate::leanh::lean_ctor_get(v_____x_1368_, 0);
                    crate::leanh::lean_dec(v_unused_1378_);
                    v___x_1371_ = v_____x_1368_;
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1369_);
                    crate::leanh::lean_dec(v_____x_1368_);
                    v___x_1371_ = crate::leanh::lean_box(0);
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1372_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1371_, 0, v_fst_1366_);
                    v___x_1374_ = v___x_1371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fst_1366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1375_ = crate::leanh::lean_apply_2(
                    v_toPure_1367_,
                    crate::leanh::lean_box(0),
                    v___x_1374_,
                );
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_monadControl___redArg___lam__5(
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_____x_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v_toBind_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1381_ = crate::leanh::lean_ctor_get(v_____x_1380_, 0);
                crate::leanh::lean_inc(v_fst_1381_);
                crate::leanh::lean_dec_ref(v_____x_1380_);
                v_toApplicative_1382_ = crate::leanh::lean_ctor_get(v_inst_1379_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1382_);
                v_fst_1383_ = crate::leanh::lean_ctor_get(v_fst_1381_, 0);
                v_snd_1384_ = crate::leanh::lean_ctor_get(v_fst_1381_, 1);
                v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v_fst_1381_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1386_ = v_fst_1381_;
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1384_);
                    crate::leanh::lean_inc(v_fst_1383_);
                    crate::leanh::lean_dec(v_fst_1381_);
                    v___x_1386_ = crate::leanh::lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_1388_ = crate::leanh::lean_ctor_get(v_inst_1379_, 1);
                crate::leanh::lean_inc(v_toBind_1388_);
                crate::leanh::lean_dec_ref(v_inst_1379_);
                v_toPure_1389_ = crate::leanh::lean_ctor_get(v_toApplicative_1382_, 1);
                crate::leanh::lean_inc_n(v_toPure_1389_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_1382_);
                v___f_1390_ = crate::leanh::lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1390_, 0, v_fst_1383_);
                crate::leanh::lean_closure_set(v___f_1390_, 1, v_toPure_1389_);
                v___x_1391_ = crate::leanh::lean_box(0);
                if v_isShared_1387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1386_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_snd_1384_);
                    v___x_1393_ = v_reuseFailAlloc_1396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1394_ = crate::leanh::lean_apply_2(
                    v_toPure_1389_,
                    crate::leanh::lean_box(0),
                    v___x_1393_,
                );
                v___x_1395_ = crate::leanh::lean_apply_4(
                    v_toBind_1388_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v_toPure_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1401_, 0, v_a_1400_);
    crate::leanh::lean_ctor_set(v___x_1401_, 1, v___y_1398_);
    v___x_1402_ =
        crate::leanh::lean_apply_2(v_toPure_1399_, crate::leanh::lean_box(0), v___x_1401_);
    return v___x_1402_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__7(
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v___f_1404_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1405_: *mut crate::leanh::LeanObject,
    mut v_x_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1408_ = crate::leanh::lean_ctor_get(v_inst_1403_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1408_);
    v_toBind_1409_ = crate::leanh::lean_ctor_get(v_inst_1403_, 1);
    crate::leanh::lean_inc_n(v_toBind_1409_, 2);
    crate::leanh::lean_dec_ref(v_inst_1403_);
    v_toPure_1410_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 1);
    crate::leanh::lean_inc(v_toPure_1410_);
    crate::leanh::lean_dec_ref(v_toApplicative_1408_);
    v___f_1411_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__6 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1411_, 0, v___y_1407_);
    crate::leanh::lean_closure_set(v___f_1411_, 1, v_toPure_1410_);
    v___x_1412_ = crate::leanh::lean_apply_4(
        v_toBind_1409_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_1406_,
        v___f_1411_,
    );
    v___x_1413_ = crate::leanh::lean_apply_4(
        v_toBind_1409_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1412_,
        v___f_1404_,
    );
    return v___x_1413_;
}
pub unsafe fn l_StateT_monadControl___redArg(
    mut v_inst_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1414_, 2);
    v___f_1415_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1415_, 0, v_inst_1414_);
    v___f_1416_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1416_, 0, v_inst_1414_);
    v___f_1417_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1417_, 0, v_inst_1414_);
    crate::leanh::lean_closure_set(v___f_1417_, 1, v___f_1416_);
    v___x_1418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1418_, 0, v___f_1415_);
    crate::leanh::lean_ctor_set(v___x_1418_, 1, v___f_1417_);
    return v___x_1418_;
}
pub unsafe fn l_StateT_monadControl(
    mut v_00_u03c3_1419_: *mut crate::leanh::LeanObject,
    mut v_m_1420_: *mut crate::leanh::LeanObject,
    mut v_inst_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1421_, 2);
    v___f_1422_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1422_, 0, v_inst_1421_);
    v___f_1423_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1423_, 0, v_inst_1421_);
    v___f_1424_ = crate::leanh::lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1424_, 0, v_inst_1421_);
    crate::leanh::lean_closure_set(v___f_1424_, 1, v___f_1423_);
    v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1425_, 0, v___f_1422_);
    crate::leanh::lean_ctor_set(v___x_1425_, 1, v___f_1424_);
    return v___x_1425_;
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__0(
    mut v_toPure_1426_: *mut crate::leanh::LeanObject,
    mut v_____x_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v_fst_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_unused_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1428_ = crate::leanh::lean_ctor_get(v_____x_1427_, 0);
                crate::leanh::lean_inc(v_fst_1428_);
                v_snd_1429_ = crate::leanh::lean_ctor_get(v_____x_1427_, 1);
                crate::leanh::lean_inc(v_snd_1429_);
                crate::leanh::lean_dec_ref(v_____x_1427_);
                v_fst_1430_ = crate::leanh::lean_ctor_get(v_fst_1428_, 0);
                v_isSharedCheck_1447_ = (!crate::leanh::lean_is_exclusive(v_fst_1428_)) as u8;
                if v_isSharedCheck_1447_ == 0 {
                    v_unused_1448_ = crate::leanh::lean_ctor_get(v_fst_1428_, 1);
                    crate::leanh::lean_dec(v_unused_1448_);
                    v___x_1432_ = v_fst_1428_;
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1430_);
                    crate::leanh::lean_dec(v_fst_1428_);
                    v___x_1432_ = crate::leanh::lean_box(0);
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1434_ = crate::leanh::lean_ctor_get(v_snd_1429_, 0);
                v_snd_1435_ = crate::leanh::lean_ctor_get(v_snd_1429_, 1);
                v_isSharedCheck_1446_ = (!crate::leanh::lean_is_exclusive(v_snd_1429_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v___x_1437_ = v_snd_1429_;
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1435_);
                    crate::leanh::lean_inc(v_fst_1434_);
                    crate::leanh::lean_dec(v_snd_1429_);
                    v___x_1437_ = crate::leanh::lean_box(0);
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1437_, 1, v_fst_1434_);
                    crate::leanh::lean_ctor_set(v___x_1437_, 0, v_fst_1430_);
                    v___x_1440_ = v___x_1437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_fst_1434_);
                    v___x_1440_ = v_reuseFailAlloc_1445_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1432_, 1, v_snd_1435_);
                    crate::leanh::lean_ctor_set(v___x_1432_, 0, v___x_1440_);
                    v___x_1442_ = v___x_1432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1435_);
                    v___x_1442_ = v_reuseFailAlloc_1444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1443_ = crate::leanh::lean_apply_2(
                    v_toPure_1426_,
                    crate::leanh::lean_box(0),
                    v___x_1442_,
                );
                return v___x_1443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__1(
    mut v_h_1449_: *mut crate::leanh::LeanObject,
    mut v_s_1450_: *mut crate::leanh::LeanObject,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v_fst_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1451_) == 0 {
                    v___x_1452_ = crate::leanh::lean_box(0);
                    v___x_1453_ = crate::leanh::lean_apply_2(v_h_1449_, v___x_1452_, v_s_1450_);
                    return v___x_1453_;
                } else {
                    crate::leanh::lean_dec(v_s_1450_);
                    v_val_1454_ = crate::leanh::lean_ctor_get(v_x_1451_, 0);
                    v_isSharedCheck_1464_ = (!crate::leanh::lean_is_exclusive(v_x_1451_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1456_ = v_x_1451_;
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1454_);
                        crate::leanh::lean_dec(v_x_1451_);
                        v___x_1456_ = crate::leanh::lean_box(0);
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1458_ = crate::leanh::lean_ctor_get(v_val_1454_, 0);
                crate::leanh::lean_inc(v_fst_1458_);
                v_snd_1459_ = crate::leanh::lean_ctor_get(v_val_1454_, 1);
                crate::leanh::lean_inc(v_snd_1459_);
                crate::leanh::lean_dec(v_val_1454_);
                if v_isShared_1457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1456_, 0, v_fst_1458_);
                    v___x_1461_ = v___x_1456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_fst_1458_);
                    v___x_1461_ = v_reuseFailAlloc_1463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1462_ = crate::leanh::lean_apply_2(v_h_1449_, v___x_1461_, v_snd_1459_);
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__2(
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_toBind_1466_: *mut crate::leanh::LeanObject,
    mut v___f_1467_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
    mut v_h_1471_: *mut crate::leanh::LeanObject,
    mut v_s_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_1472_);
    v___f_1473_ = crate::leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1473_, 0, v_h_1471_);
    crate::leanh::lean_closure_set(v___f_1473_, 1, v_s_1472_);
    v___x_1474_ = crate::leanh::lean_apply_1(v_x_1470_, v_s_1472_);
    v___x_1475_ = crate::leanh::lean_apply_4(
        v_inst_1465_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1474_,
        v___f_1473_,
    );
    v___x_1476_ = crate::leanh::lean_apply_4(
        v_toBind_1466_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1475_,
        v___f_1467_,
    );
    return v___x_1476_;
}
pub unsafe fn l_StateT_tryFinally___redArg(
    mut v_inst_1477_: *mut crate::leanh::LeanObject,
    mut v_inst_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1479_ = crate::leanh::lean_ctor_get(v_inst_1478_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1479_);
    v_toBind_1480_ = crate::leanh::lean_ctor_get(v_inst_1478_, 1);
    crate::leanh::lean_inc(v_toBind_1480_);
    crate::leanh::lean_dec_ref(v_inst_1478_);
    v_toPure_1481_ = crate::leanh::lean_ctor_get(v_toApplicative_1479_, 1);
    crate::leanh::lean_inc(v_toPure_1481_);
    crate::leanh::lean_dec_ref(v_toApplicative_1479_);
    v___f_1482_ = crate::leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1482_, 0, v_toPure_1481_);
    v___f_1483_ = crate::leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1483_, 0, v_inst_1477_);
    crate::leanh::lean_closure_set(v___f_1483_, 1, v_toBind_1480_);
    crate::leanh::lean_closure_set(v___f_1483_, 2, v___f_1482_);
    return v___f_1483_;
}
pub unsafe fn l_StateT_tryFinally(
    mut v_m_1484_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1485_: *mut crate::leanh::LeanObject,
    mut v_inst_1486_: *mut crate::leanh::LeanObject,
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1488_ = crate::leanh::lean_ctor_get(v_inst_1487_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1488_);
    v_toBind_1489_ = crate::leanh::lean_ctor_get(v_inst_1487_, 1);
    crate::leanh::lean_inc(v_toBind_1489_);
    crate::leanh::lean_dec_ref(v_inst_1487_);
    v_toPure_1490_ = crate::leanh::lean_ctor_get(v_toApplicative_1488_, 1);
    crate::leanh::lean_inc(v_toPure_1490_);
    crate::leanh::lean_dec_ref(v_toApplicative_1488_);
    v___f_1491_ = crate::leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1491_, 0, v_toPure_1490_);
    v___f_1492_ = crate::leanh::lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1492_, 0, v_inst_1486_);
    crate::leanh::lean_closure_set(v___f_1492_, 1, v_toBind_1489_);
    crate::leanh::lean_closure_set(v___f_1492_, 2, v___f_1491_);
    return v___f_1492_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg___lam__0(
    mut v_x_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1494_ = crate::leanh::lean_ctor_get(v_x_1493_, 0);
                v_snd_1495_ = crate::leanh::lean_ctor_get(v_x_1493_, 1);
                v_isSharedCheck_1502_ = (!crate::leanh::lean_is_exclusive(v_x_1493_)) as u8;
                if v_isSharedCheck_1502_ == 0 {
                    v___x_1497_ = v_x_1493_;
                    v_isShared_1498_ = v_isSharedCheck_1502_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1495_);
                    crate::leanh::lean_inc(v_fst_1494_);
                    crate::leanh::lean_dec(v_x_1493_);
                    v___x_1497_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_fst_1494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_snd_1495_);
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
    mut v_toFunctor_1503_: *mut crate::leanh::LeanObject,
    mut v_inst_1504_: *mut crate::leanh::LeanObject,
    mut v___f_1505_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
    mut v_s_1508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1509_ = crate::leanh::lean_ctor_get(v_toFunctor_1503_, 0);
    crate::leanh::lean_inc(v_map_1509_);
    crate::leanh::lean_dec_ref(v_toFunctor_1503_);
    v___x_1510_ = crate::leanh::lean_apply_1(v_x_1507_, v_s_1508_);
    v___x_1511_ = crate::leanh::lean_apply_2(v_inst_1504_, crate::leanh::lean_box(0), v___x_1510_);
    v___x_1512_ = crate::leanh::lean_apply_4(
        v_map_1509_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1505_,
        v___x_1511_,
    );
    return v___x_1512_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg(
    mut v_inst_1514_: *mut crate::leanh::LeanObject,
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1516_ = crate::leanh::lean_ctor_get(v_inst_1514_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1516_);
    crate::leanh::lean_dec_ref(v_inst_1514_);
    v_toFunctor_1517_ = crate::leanh::lean_ctor_get(v_toApplicative_1516_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1517_);
    crate::leanh::lean_dec_ref(v_toApplicative_1516_);
    v___f_1518_ = l_instMonadAttachStateTOfMonad___redArg___closed__0;
    v___f_1519_ = crate::leanh::lean_alloc_closure(
        l_instMonadAttachStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1519_, 0, v_toFunctor_1517_);
    crate::leanh::lean_closure_set(v___f_1519_, 1, v_inst_1515_);
    crate::leanh::lean_closure_set(v___f_1519_, 2, v___f_1518_);
    return v___f_1519_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad(
    mut v_m_1520_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1521_: *mut crate::leanh::LeanObject,
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_instMonadAttachStateTOfMonad___redArg(v_inst_1522_, v_inst_1523_);
    return v___x_1524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_State(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_State(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_State(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_State(builtin);
}
