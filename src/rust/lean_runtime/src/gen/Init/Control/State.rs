// Lean compiler output
// Module: Init.Control.State
// Imports: Init.Control.Except
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_StateT_run_x27___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_StateT_instMonadFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateT_instMonadFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateT_instMonadFunctor___closed__0_value) as *mut LeanObject;
pub static l_instMonadAttachStateTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadAttachStateTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadAttachStateTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachStateTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_StateT_mk___redArg(
    mut v_x_763_: *mut LeanObject,
    mut v_a_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_apply_1(v_x_763_, v_a_764_);
    return v___x_765_;
}
pub unsafe fn l_StateT_mk(
    mut v_00_u03c3_766_: *mut LeanObject,
    mut v_m_767_: *mut LeanObject,
    mut v_00_u03b1_768_: *mut LeanObject,
    mut v_x_769_: *mut LeanObject,
    mut v_a_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = lean_apply_1(v_x_769_, v_a_770_);
    return v___x_771_;
}
pub unsafe fn l_StateT_run___redArg(
    mut v_x_772_: *mut LeanObject,
    mut v_s_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_apply_1(v_x_772_, v_s_773_);
    return v___x_774_;
}
pub unsafe fn l_StateT_run(
    mut v_00_u03c3_775_: *mut LeanObject,
    mut v_m_776_: *mut LeanObject,
    mut v_00_u03b1_777_: *mut LeanObject,
    mut v_x_778_: *mut LeanObject,
    mut v_s_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = lean_apply_1(v_x_778_, v_s_779_);
    return v___x_780_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0(mut v_x_781_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_782_: *mut LeanObject = core::ptr::null_mut();
    v_fst_782_ = lean_ctor_get(v_x_781_, 0);
    lean_inc(v_fst_782_);
    return v_fst_782_;
}
pub unsafe fn l_StateT_run_x27___redArg___lam__0___boxed(
    mut v_x_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_StateT_run_x27___redArg___lam__0(v_x_783_);
    lean_dec_ref(v_x_783_);
    return v_res_784_;
}
pub unsafe fn l_StateT_run_x27___redArg(
    mut v_inst_786_: *mut LeanObject,
    mut v_x_787_: *mut LeanObject,
    mut v_s_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    v_map_789_ = lean_ctor_get(v_inst_786_, 0);
    lean_inc(v_map_789_);
    lean_dec_ref(v_inst_786_);
    v___f_790_ = l_StateT_run_x27___redArg___closed__0;
    v___x_791_ = lean_apply_1(v_x_787_, v_s_788_);
    v___x_792_ = lean_apply_4(v_map_789_, lean_box(0), lean_box(0), v___f_790_, v___x_791_);
    return v___x_792_;
}
pub unsafe fn l_StateT_run_x27(
    mut v_00_u03c3_793_: *mut LeanObject,
    mut v_m_794_: *mut LeanObject,
    mut v_inst_795_: *mut LeanObject,
    mut v_00_u03b1_796_: *mut LeanObject,
    mut v_x_797_: *mut LeanObject,
    mut v_s_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v_map_799_ = lean_ctor_get(v_inst_795_, 0);
    lean_inc(v_map_799_);
    lean_dec_ref(v_inst_795_);
    v___f_800_ = l_StateT_run_x27___redArg___closed__0;
    v___x_801_ = lean_apply_1(v_x_797_, v_s_798_);
    v___x_802_ = lean_apply_4(v_map_799_, lean_box(0), lean_box(0), v___f_800_, v___x_801_);
    return v___x_802_;
}
pub unsafe fn l_StateT_pure___redArg(
    mut v_inst_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
    mut v_s_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_809_: u8 = 0;
    let mut v_toPure_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_unused_816_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_806_ = lean_ctor_get(v_inst_803_, 0);
                v_isSharedCheck_815_ = (!lean_is_exclusive(v_inst_803_)) as u8;
                if v_isSharedCheck_815_ == 0 {
                    v_unused_816_ = lean_ctor_get(v_inst_803_, 1);
                    lean_dec(v_unused_816_);
                    v___x_808_ = v_inst_803_;
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_806_);
                    lean_dec(v_inst_803_);
                    v___x_808_ = lean_box(0);
                    v_isShared_809_ = v_isSharedCheck_815_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_810_ = lean_ctor_get(v_toApplicative_806_, 1);
                lean_inc(v_toPure_810_);
                lean_dec_ref(v_toApplicative_806_);
                if v_isShared_809_ == 0 {
                    lean_ctor_set(v___x_808_, 1, v_s_805_);
                    lean_ctor_set(v___x_808_, 0, v_a_804_);
                    v___x_812_ = v___x_808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_804_);
                    lean_ctor_set(v_reuseFailAlloc_814_, 1, v_s_805_);
                    v___x_812_ = v_reuseFailAlloc_814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_813_ = lean_apply_2(v_toPure_810_, lean_box(0), v___x_812_);
                return v___x_813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_pure(
    mut v_00_u03c3_817_: *mut LeanObject,
    mut v_m_818_: *mut LeanObject,
    mut v_inst_819_: *mut LeanObject,
    mut v_00_u03b1_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_s_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_unused_833_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_823_ = lean_ctor_get(v_inst_819_, 0);
                v_isSharedCheck_832_ = (!lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_832_ == 0 {
                    v_unused_833_ = lean_ctor_get(v_inst_819_, 1);
                    lean_dec(v_unused_833_);
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_823_);
                    lean_dec(v_inst_819_);
                    v___x_825_ = lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = lean_ctor_get(v_toApplicative_823_, 1);
                lean_inc(v_toPure_827_);
                lean_dec_ref(v_toApplicative_823_);
                if v_isShared_826_ == 0 {
                    lean_ctor_set(v___x_825_, 1, v_s_822_);
                    lean_ctor_set(v___x_825_, 0, v_a_821_);
                    v___x_829_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_821_);
                    lean_ctor_set(v_reuseFailAlloc_831_, 1, v_s_822_);
                    v___x_829_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_830_ = lean_apply_2(v_toPure_827_, lean_box(0), v___x_829_);
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_bind___redArg___lam__0(
    mut v_f_834_: *mut LeanObject,
    mut v_____x_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    v_fst_836_ = lean_ctor_get(v_____x_835_, 0);
    lean_inc(v_fst_836_);
    v_snd_837_ = lean_ctor_get(v_____x_835_, 1);
    lean_inc(v_snd_837_);
    lean_dec_ref(v_____x_835_);
    v___x_838_ = lean_apply_2(v_f_834_, v_fst_836_, v_snd_837_);
    return v___x_838_;
}
pub unsafe fn l_StateT_bind___redArg(
    mut v_inst_839_: *mut LeanObject,
    mut v_x_840_: *mut LeanObject,
    mut v_f_841_: *mut LeanObject,
    mut v_s_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_843_ = lean_ctor_get(v_inst_839_, 1);
    lean_inc(v_toBind_843_);
    lean_dec_ref(v_inst_839_);
    v___f_844_ = lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_844_, 0, v_f_841_);
    v___x_845_ = lean_apply_1(v_x_840_, v_s_842_);
    v___x_846_ = lean_apply_4(
        v_toBind_843_,
        lean_box(0),
        lean_box(0),
        v___x_845_,
        v___f_844_,
    );
    return v___x_846_;
}
pub unsafe fn l_StateT_bind(
    mut v_00_u03c3_847_: *mut LeanObject,
    mut v_m_848_: *mut LeanObject,
    mut v_inst_849_: *mut LeanObject,
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_00_u03b2_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
    mut v_f_853_: *mut LeanObject,
    mut v_s_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_855_ = lean_ctor_get(v_inst_849_, 1);
    lean_inc(v_toBind_855_);
    lean_dec_ref(v_inst_849_);
    v___f_856_ = lean_alloc_closure(
        l_StateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_856_, 0, v_f_853_);
    v___x_857_ = lean_apply_1(v_x_852_, v_s_854_);
    v___x_858_ = lean_apply_4(
        v_toBind_855_,
        lean_box(0),
        lean_box(0),
        v___x_857_,
        v___f_856_,
    );
    return v___x_858_;
}
pub unsafe fn l_StateT_map___redArg___lam__0(
    mut v_f_859_: *mut LeanObject,
    mut v_toPure_860_: *mut LeanObject,
    mut v_____x_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_862_ = lean_ctor_get(v_____x_861_, 0);
                v_snd_863_ = lean_ctor_get(v_____x_861_, 1);
                v_isSharedCheck_872_ = (!lean_is_exclusive(v_____x_861_)) as u8;
                if v_isSharedCheck_872_ == 0 {
                    v___x_865_ = v_____x_861_;
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_863_);
                    lean_inc(v_fst_862_);
                    lean_dec(v_____x_861_);
                    v___x_865_ = lean_box(0);
                    v_isShared_866_ = v_isSharedCheck_872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_867_ = lean_apply_1(v_f_859_, v_fst_862_);
                if v_isShared_866_ == 0 {
                    lean_ctor_set(v___x_865_, 0, v___x_867_);
                    v___x_869_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
                    lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_863_);
                    v___x_869_ = v_reuseFailAlloc_871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_870_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_869_);
                return v___x_870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_map___redArg(
    mut v_inst_873_: *mut LeanObject,
    mut v_f_874_: *mut LeanObject,
    mut v_x_875_: *mut LeanObject,
    mut v_s_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_877_ = lean_ctor_get(v_inst_873_, 0);
    lean_inc_ref(v_toApplicative_877_);
    v_toBind_878_ = lean_ctor_get(v_inst_873_, 1);
    lean_inc(v_toBind_878_);
    lean_dec_ref(v_inst_873_);
    v_toPure_879_ = lean_ctor_get(v_toApplicative_877_, 1);
    lean_inc(v_toPure_879_);
    lean_dec_ref(v_toApplicative_877_);
    v___x_880_ = lean_apply_1(v_x_875_, v_s_876_);
    v___f_881_ = lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_881_, 0, v_f_874_);
    lean_closure_set(v___f_881_, 1, v_toPure_879_);
    v___x_882_ = lean_apply_4(
        v_toBind_878_,
        lean_box(0),
        lean_box(0),
        v___x_880_,
        v___f_881_,
    );
    return v___x_882_;
}
pub unsafe fn l_StateT_map(
    mut v_00_u03c3_883_: *mut LeanObject,
    mut v_m_884_: *mut LeanObject,
    mut v_inst_885_: *mut LeanObject,
    mut v_00_u03b1_886_: *mut LeanObject,
    mut v_00_u03b2_887_: *mut LeanObject,
    mut v_f_888_: *mut LeanObject,
    mut v_x_889_: *mut LeanObject,
    mut v_s_890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_891_ = lean_ctor_get(v_inst_885_, 0);
    lean_inc_ref(v_toApplicative_891_);
    v_toBind_892_ = lean_ctor_get(v_inst_885_, 1);
    lean_inc(v_toBind_892_);
    lean_dec_ref(v_inst_885_);
    v_toPure_893_ = lean_ctor_get(v_toApplicative_891_, 1);
    lean_inc(v_toPure_893_);
    lean_dec_ref(v_toApplicative_891_);
    v___x_894_ = lean_apply_1(v_x_889_, v_s_890_);
    v___f_895_ = lean_alloc_closure(
        l_StateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_895_, 0, v_f_888_);
    lean_closure_set(v___f_895_, 1, v_toPure_893_);
    v___x_896_ = lean_apply_4(
        v_toBind_892_,
        lean_box(0),
        lean_box(0),
        v___x_894_,
        v___f_895_,
    );
    return v___x_896_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__0(
    mut v___y_897_: *mut LeanObject,
    mut v_toPure_898_: *mut LeanObject,
    mut v_____x_899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_900_ = lean_ctor_get(v_____x_899_, 1);
                v_isSharedCheck_908_ = (!lean_is_exclusive(v_____x_899_)) as u8;
                if v_isSharedCheck_908_ == 0 {
                    v_unused_909_ = lean_ctor_get(v_____x_899_, 0);
                    lean_dec(v_unused_909_);
                    v___x_902_ = v_____x_899_;
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_900_);
                    lean_dec(v_____x_899_);
                    v___x_902_ = lean_box(0);
                    v_isShared_903_ = v_isSharedCheck_908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_903_ == 0 {
                    lean_ctor_set(v___x_902_, 0, v___y_897_);
                    v___x_905_ = v___x_902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_907_, 0, v___y_897_);
                    lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_900_);
                    v___x_905_ = v_reuseFailAlloc_907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_906_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_905_);
                return v___x_906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__1(
    mut v_inst_910_: *mut LeanObject,
    mut v_00_u03b1_911_: *mut LeanObject,
    mut v_00_u03b2_912_: *mut LeanObject,
    mut v___y_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_916_ = lean_ctor_get(v_inst_910_, 0);
    lean_inc_ref(v_toApplicative_916_);
    v_toBind_917_ = lean_ctor_get(v_inst_910_, 1);
    lean_inc(v_toBind_917_);
    lean_dec_ref(v_inst_910_);
    v_toPure_918_ = lean_ctor_get(v_toApplicative_916_, 1);
    lean_inc(v_toPure_918_);
    lean_dec_ref(v_toApplicative_916_);
    v___x_919_ = lean_apply_1(v___y_914_, v___y_915_);
    v___f_920_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_920_, 0, v___y_913_);
    lean_closure_set(v___f_920_, 1, v_toPure_918_);
    v___x_921_ = lean_apply_4(
        v_toBind_917_,
        lean_box(0),
        lean_box(0),
        v___x_919_,
        v___f_920_,
    );
    return v___x_921_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__2(
    mut v_fst_922_: *mut LeanObject,
    mut v_toPure_923_: *mut LeanObject,
    mut v_____x_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_925_ = lean_ctor_get(v_____x_924_, 0);
                v_snd_926_ = lean_ctor_get(v_____x_924_, 1);
                v_isSharedCheck_935_ = (!lean_is_exclusive(v_____x_924_)) as u8;
                if v_isSharedCheck_935_ == 0 {
                    v___x_928_ = v_____x_924_;
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_926_);
                    lean_inc(v_fst_925_);
                    lean_dec(v_____x_924_);
                    v___x_928_ = lean_box(0);
                    v_isShared_929_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_930_ = lean_apply_1(v_fst_922_, v_fst_925_);
                if v_isShared_929_ == 0 {
                    lean_ctor_set(v___x_928_, 0, v___x_930_);
                    v___x_932_ = v___x_928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_930_);
                    lean_ctor_set(v_reuseFailAlloc_934_, 1, v_snd_926_);
                    v___x_932_ = v_reuseFailAlloc_934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_933_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_932_);
                return v___x_933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__3(
    mut v_toApplicative_936_: *mut LeanObject,
    mut v_x_937_: *mut LeanObject,
    mut v_toBind_938_: *mut LeanObject,
    mut v_____x_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    v_fst_940_ = lean_ctor_get(v_____x_939_, 0);
    lean_inc(v_fst_940_);
    v_snd_941_ = lean_ctor_get(v_____x_939_, 1);
    lean_inc(v_snd_941_);
    lean_dec_ref(v_____x_939_);
    v_toPure_942_ = lean_ctor_get(v_toApplicative_936_, 1);
    lean_inc(v_toPure_942_);
    lean_dec_ref(v_toApplicative_936_);
    v___x_943_ = lean_box(0);
    v___x_944_ = lean_apply_2(v_x_937_, v___x_943_, v_snd_941_);
    v___f_945_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_945_, 0, v_fst_940_);
    lean_closure_set(v___f_945_, 1, v_toPure_942_);
    v___x_946_ = lean_apply_4(
        v_toBind_938_,
        lean_box(0),
        lean_box(0),
        v___x_944_,
        v___f_945_,
    );
    return v___x_946_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__4(
    mut v_inst_947_: *mut LeanObject,
    mut v_00_u03b1_948_: *mut LeanObject,
    mut v_00_u03b2_949_: *mut LeanObject,
    mut v_f_950_: *mut LeanObject,
    mut v_x_951_: *mut LeanObject,
    mut v___y_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_953_ = lean_ctor_get(v_inst_947_, 0);
    lean_inc_ref(v_toApplicative_953_);
    v_toBind_954_ = lean_ctor_get(v_inst_947_, 1);
    lean_inc_n(v_toBind_954_, 2);
    lean_dec_ref(v_inst_947_);
    v___f_955_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_955_, 0, v_toApplicative_953_);
    lean_closure_set(v___f_955_, 1, v_x_951_);
    lean_closure_set(v___f_955_, 2, v_toBind_954_);
    v___x_956_ = lean_apply_1(v_f_950_, v___y_952_);
    v___x_957_ = lean_apply_4(
        v_toBind_954_,
        lean_box(0),
        lean_box(0),
        v___x_956_,
        v___f_955_,
    );
    return v___x_957_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__5(
    mut v_toApplicative_958_: *mut LeanObject,
    mut v_fst_959_: *mut LeanObject,
    mut v_____x_960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_toPure_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_unused_971_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_961_ = lean_ctor_get(v_____x_960_, 1);
                v_isSharedCheck_970_ = (!lean_is_exclusive(v_____x_960_)) as u8;
                if v_isSharedCheck_970_ == 0 {
                    v_unused_971_ = lean_ctor_get(v_____x_960_, 0);
                    lean_dec(v_unused_971_);
                    v___x_963_ = v_____x_960_;
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_961_);
                    lean_dec(v_____x_960_);
                    v___x_963_ = lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_965_ = lean_ctor_get(v_toApplicative_958_, 1);
                lean_inc(v_toPure_965_);
                lean_dec_ref(v_toApplicative_958_);
                if v_isShared_964_ == 0 {
                    lean_ctor_set(v___x_963_, 0, v_fst_959_);
                    v___x_967_ = v___x_963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_959_);
                    lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_961_);
                    v___x_967_ = v_reuseFailAlloc_969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_968_ = lean_apply_2(v_toPure_965_, lean_box(0), v___x_967_);
                return v___x_968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_instMonad___redArg___lam__6(
    mut v_toApplicative_972_: *mut LeanObject,
    mut v_y_973_: *mut LeanObject,
    mut v_toBind_974_: *mut LeanObject,
    mut v_____x_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v_fst_976_ = lean_ctor_get(v_____x_975_, 0);
    lean_inc(v_fst_976_);
    v_snd_977_ = lean_ctor_get(v_____x_975_, 1);
    lean_inc(v_snd_977_);
    lean_dec_ref(v_____x_975_);
    v___f_978_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_978_, 0, v_toApplicative_972_);
    lean_closure_set(v___f_978_, 1, v_fst_976_);
    v___x_979_ = lean_box(0);
    v___x_980_ = lean_apply_2(v_y_973_, v___x_979_, v_snd_977_);
    v___x_981_ = lean_apply_4(
        v_toBind_974_,
        lean_box(0),
        lean_box(0),
        v___x_980_,
        v___f_978_,
    );
    return v___x_981_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__7(
    mut v_inst_982_: *mut LeanObject,
    mut v_00_u03b1_983_: *mut LeanObject,
    mut v_00_u03b2_984_: *mut LeanObject,
    mut v_x_985_: *mut LeanObject,
    mut v_y_986_: *mut LeanObject,
    mut v___y_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_988_ = lean_ctor_get(v_inst_982_, 0);
    lean_inc_ref(v_toApplicative_988_);
    v_toBind_989_ = lean_ctor_get(v_inst_982_, 1);
    lean_inc_n(v_toBind_989_, 2);
    lean_dec_ref(v_inst_982_);
    v___f_990_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_990_, 0, v_toApplicative_988_);
    lean_closure_set(v___f_990_, 1, v_y_986_);
    lean_closure_set(v___f_990_, 2, v_toBind_989_);
    v___x_991_ = lean_apply_1(v_x_985_, v___y_987_);
    v___x_992_ = lean_apply_4(
        v_toBind_989_,
        lean_box(0),
        lean_box(0),
        v___x_991_,
        v___f_990_,
    );
    return v___x_992_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__8(
    mut v_y_993_: *mut LeanObject,
    mut v_____x_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    v_snd_995_ = lean_ctor_get(v_____x_994_, 1);
    lean_inc(v_snd_995_);
    lean_dec_ref(v_____x_994_);
    v___x_996_ = lean_box(0);
    v___x_997_ = lean_apply_2(v_y_993_, v___x_996_, v_snd_995_);
    return v___x_997_;
}
pub unsafe fn l_StateT_instMonad___redArg___lam__9(
    mut v_inst_998_: *mut LeanObject,
    mut v_00_u03b1_999_: *mut LeanObject,
    mut v_00_u03b2_1000_: *mut LeanObject,
    mut v_x_1001_: *mut LeanObject,
    mut v_y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1004_ = lean_ctor_get(v_inst_998_, 1);
    lean_inc(v_toBind_1004_);
    lean_dec_ref(v_inst_998_);
    v___f_1005_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1005_, 0, v_y_1002_);
    v___x_1006_ = lean_apply_1(v_x_1001_, v___y_1003_);
    v___x_1007_ = lean_apply_4(
        v_toBind_1004_,
        lean_box(0),
        lean_box(0),
        v___x_1006_,
        v___f_1005_,
    );
    return v___x_1007_;
}
pub unsafe fn l_StateT_instMonad___redArg(mut v_inst_1008_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1008_, 6);
    v___f_1009_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1009_, 0, v_inst_1008_);
    v___f_1010_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1010_, 0, v_inst_1008_);
    v___f_1011_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1011_, 0, v_inst_1008_);
    v___f_1012_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1012_, 0, v_inst_1008_);
    v___x_1013_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1013_, 0, lean_box(0));
    lean_closure_set(v___x_1013_, 1, lean_box(0));
    lean_closure_set(v___x_1013_, 2, v_inst_1008_);
    v___x_1014_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1014_, 0, v___x_1013_);
    lean_ctor_set(v___x_1014_, 1, v___f_1009_);
    v___x_1015_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1015_, 0, lean_box(0));
    lean_closure_set(v___x_1015_, 1, lean_box(0));
    lean_closure_set(v___x_1015_, 2, v_inst_1008_);
    v___x_1016_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1016_, 0, v___x_1014_);
    lean_ctor_set(v___x_1016_, 1, v___x_1015_);
    lean_ctor_set(v___x_1016_, 2, v___f_1010_);
    lean_ctor_set(v___x_1016_, 3, v___f_1011_);
    lean_ctor_set(v___x_1016_, 4, v___f_1012_);
    v___x_1017_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1017_, 0, lean_box(0));
    lean_closure_set(v___x_1017_, 1, lean_box(0));
    lean_closure_set(v___x_1017_, 2, v_inst_1008_);
    v___x_1018_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1018_, 0, v___x_1016_);
    lean_ctor_set(v___x_1018_, 1, v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_StateT_instMonad(
    mut v_00_u03c3_1019_: *mut LeanObject,
    mut v_m_1020_: *mut LeanObject,
    mut v_inst_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1021_, 6);
    v___f_1022_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1022_, 0, v_inst_1021_);
    v___f_1023_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1023_, 0, v_inst_1021_);
    v___f_1024_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1024_, 0, v_inst_1021_);
    v___f_1025_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1025_, 0, v_inst_1021_);
    v___x_1026_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1026_, 0, lean_box(0));
    lean_closure_set(v___x_1026_, 1, lean_box(0));
    lean_closure_set(v___x_1026_, 2, v_inst_1021_);
    v___x_1027_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    lean_ctor_set(v___x_1027_, 1, v___f_1022_);
    v___x_1028_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1028_, 0, lean_box(0));
    lean_closure_set(v___x_1028_, 1, lean_box(0));
    lean_closure_set(v___x_1028_, 2, v_inst_1021_);
    v___x_1029_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1029_, 0, v___x_1027_);
    lean_ctor_set(v___x_1029_, 1, v___x_1028_);
    lean_ctor_set(v___x_1029_, 2, v___f_1023_);
    lean_ctor_set(v___x_1029_, 3, v___f_1024_);
    lean_ctor_set(v___x_1029_, 4, v___f_1025_);
    v___x_1030_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1030_, 0, lean_box(0));
    lean_closure_set(v___x_1030_, 1, lean_box(0));
    lean_closure_set(v___x_1030_, 2, v_inst_1021_);
    v___x_1031_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn l_StateT_orElse___redArg___lam__0(
    mut v_x_u2082_1032_: *mut LeanObject,
    mut v_s_1033_: *mut LeanObject,
    mut v_x_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = lean_box(0);
    v___x_1036_ = lean_apply_2(v_x_u2082_1032_, v___x_1035_, v_s_1033_);
    return v___x_1036_;
}
pub unsafe fn l_StateT_orElse___redArg(
    mut v_inst_1037_: *mut LeanObject,
    mut v_x_u2081_1038_: *mut LeanObject,
    mut v_x_u2082_1039_: *mut LeanObject,
    mut v_s_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_1041_ = lean_ctor_get(v_inst_1037_, 2);
    lean_inc(v_orElse_1041_);
    lean_dec_ref(v_inst_1037_);
    lean_inc(v_s_1040_);
    v___f_1042_ = lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1042_, 0, v_x_u2082_1039_);
    lean_closure_set(v___f_1042_, 1, v_s_1040_);
    v___x_1043_ = lean_apply_1(v_x_u2081_1038_, v_s_1040_);
    v___x_1044_ = lean_apply_3(v_orElse_1041_, lean_box(0), v___x_1043_, v___f_1042_);
    return v___x_1044_;
}
pub unsafe fn l_StateT_orElse(
    mut v_00_u03c3_1045_: *mut LeanObject,
    mut v_m_1046_: *mut LeanObject,
    mut v_inst_1047_: *mut LeanObject,
    mut v_00_u03b1_1048_: *mut LeanObject,
    mut v_x_u2081_1049_: *mut LeanObject,
    mut v_x_u2082_1050_: *mut LeanObject,
    mut v_s_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_1052_ = lean_ctor_get(v_inst_1047_, 2);
    lean_inc(v_orElse_1052_);
    lean_dec_ref(v_inst_1047_);
    lean_inc(v_s_1051_);
    v___f_1053_ = lean_alloc_closure(
        l_StateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1053_, 0, v_x_u2082_1050_);
    lean_closure_set(v___f_1053_, 1, v_s_1051_);
    v___x_1054_ = lean_apply_1(v_x_u2081_1049_, v_s_1051_);
    v___x_1055_ = lean_apply_3(v_orElse_1052_, lean_box(0), v___x_1054_, v___f_1053_);
    return v___x_1055_;
}
pub unsafe fn l_StateT_failure___redArg(mut v_inst_1056_: *mut LeanObject) -> *mut LeanObject {
    let mut v_failure_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v_failure_1057_ = lean_ctor_get(v_inst_1056_, 1);
    lean_inc(v_failure_1057_);
    lean_dec_ref(v_inst_1056_);
    v___x_1058_ = lean_apply_1(v_failure_1057_, lean_box(0));
    return v___x_1058_;
}
pub unsafe fn l_StateT_failure(
    mut v_00_u03c3_1059_: *mut LeanObject,
    mut v_m_1060_: *mut LeanObject,
    mut v_inst_1061_: *mut LeanObject,
    mut v_00_u03b1_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v_failure_1064_ = lean_ctor_get(v_inst_1061_, 1);
    lean_inc(v_failure_1064_);
    lean_dec_ref(v_inst_1061_);
    v___x_1065_ = lean_apply_1(v_failure_1064_, lean_box(0));
    return v___x_1065_;
}
pub unsafe fn l_StateT_failure___boxed(
    mut v_00_u03c3_1066_: *mut LeanObject,
    mut v_m_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_00_u03b1_1069_: *mut LeanObject,
    mut v_x_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1071_: *mut LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_StateT_failure(
        v_00_u03c3_1066_,
        v_m_1067_,
        v_inst_1068_,
        v_00_u03b1_1069_,
        v_x_1070_,
    );
    lean_dec(v_x_1070_);
    return v_res_1071_;
}
pub unsafe fn l_StateT_instAlternative___redArg(
    mut v_inst_1072_: *mut LeanObject,
    mut v_inst_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1072_, 5);
    v___f_1074_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1074_, 0, v_inst_1072_);
    v___f_1075_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1075_, 0, v_inst_1072_);
    v___f_1076_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1076_, 0, v_inst_1072_);
    v___f_1077_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1077_, 0, v_inst_1072_);
    v___x_1078_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1078_, 0, lean_box(0));
    lean_closure_set(v___x_1078_, 1, lean_box(0));
    lean_closure_set(v___x_1078_, 2, v_inst_1072_);
    v___x_1079_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    lean_ctor_set(v___x_1079_, 1, v___f_1074_);
    v___x_1080_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1080_, 0, lean_box(0));
    lean_closure_set(v___x_1080_, 1, lean_box(0));
    lean_closure_set(v___x_1080_, 2, v_inst_1072_);
    v___x_1081_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1081_, 0, v___x_1079_);
    lean_ctor_set(v___x_1081_, 1, v___x_1080_);
    lean_ctor_set(v___x_1081_, 2, v___f_1075_);
    lean_ctor_set(v___x_1081_, 3, v___f_1076_);
    lean_ctor_set(v___x_1081_, 4, v___f_1077_);
    lean_inc_ref(v_inst_1073_);
    v___x_1082_ = lean_alloc_closure(l_StateT_failure___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1082_, 0, lean_box(0));
    lean_closure_set(v___x_1082_, 1, lean_box(0));
    lean_closure_set(v___x_1082_, 2, v_inst_1073_);
    v___x_1083_ = lean_alloc_closure(l_StateT_orElse as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_1083_, 0, lean_box(0));
    lean_closure_set(v___x_1083_, 1, lean_box(0));
    lean_closure_set(v___x_1083_, 2, v_inst_1073_);
    v___x_1084_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1084_, 0, v___x_1081_);
    lean_ctor_set(v___x_1084_, 1, v___x_1082_);
    lean_ctor_set(v___x_1084_, 2, v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_StateT_instAlternative(
    mut v_00_u03c3_1085_: *mut LeanObject,
    mut v_m_1086_: *mut LeanObject,
    mut v_inst_1087_: *mut LeanObject,
    mut v_inst_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_StateT_instAlternative___redArg(v_inst_1087_, v_inst_1088_);
    return v___x_1089_;
}
pub unsafe fn l_StateT_get___redArg(
    mut v_inst_1090_: *mut LeanObject,
    mut v_s_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v_toPure_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_unused_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1092_ = lean_ctor_get(v_inst_1090_, 0);
                v_isSharedCheck_1101_ = (!lean_is_exclusive(v_inst_1090_)) as u8;
                if v_isSharedCheck_1101_ == 0 {
                    v_unused_1102_ = lean_ctor_get(v_inst_1090_, 1);
                    lean_dec(v_unused_1102_);
                    v___x_1094_ = v_inst_1090_;
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1092_);
                    lean_dec(v_inst_1090_);
                    v___x_1094_ = lean_box(0);
                    v_isShared_1095_ = v_isSharedCheck_1101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1096_ = lean_ctor_get(v_toApplicative_1092_, 1);
                lean_inc(v_toPure_1096_);
                lean_dec_ref(v_toApplicative_1092_);
                lean_inc(v_s_1091_);
                if v_isShared_1095_ == 0 {
                    lean_ctor_set(v___x_1094_, 1, v_s_1091_);
                    lean_ctor_set(v___x_1094_, 0, v_s_1091_);
                    v___x_1098_ = v___x_1094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_s_1091_);
                    lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_s_1091_);
                    v___x_1098_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = lean_apply_2(v_toPure_1096_, lean_box(0), v___x_1098_);
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_get(
    mut v_00_u03c3_1103_: *mut LeanObject,
    mut v_m_1104_: *mut LeanObject,
    mut v_inst_1105_: *mut LeanObject,
    mut v_s_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v_toPure_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_unused_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1107_ = lean_ctor_get(v_inst_1105_, 0);
                v_isSharedCheck_1116_ = (!lean_is_exclusive(v_inst_1105_)) as u8;
                if v_isSharedCheck_1116_ == 0 {
                    v_unused_1117_ = lean_ctor_get(v_inst_1105_, 1);
                    lean_dec(v_unused_1117_);
                    v___x_1109_ = v_inst_1105_;
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1107_);
                    lean_dec(v_inst_1105_);
                    v___x_1109_ = lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1111_ = lean_ctor_get(v_toApplicative_1107_, 1);
                lean_inc(v_toPure_1111_);
                lean_dec_ref(v_toApplicative_1107_);
                lean_inc(v_s_1106_);
                if v_isShared_1110_ == 0 {
                    lean_ctor_set(v___x_1109_, 1, v_s_1106_);
                    lean_ctor_set(v___x_1109_, 0, v_s_1106_);
                    v___x_1113_ = v___x_1109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_s_1106_);
                    lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_s_1106_);
                    v___x_1113_ = v_reuseFailAlloc_1115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1114_ = lean_apply_2(v_toPure_1111_, lean_box(0), v___x_1113_);
                return v___x_1114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___redArg(
    mut v_inst_1118_: *mut LeanObject,
    mut v_s_x27_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v_toPure_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_unused_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1120_ = lean_ctor_get(v_inst_1118_, 0);
                v_isSharedCheck_1130_ = (!lean_is_exclusive(v_inst_1118_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v_unused_1131_ = lean_ctor_get(v_inst_1118_, 1);
                    lean_dec(v_unused_1131_);
                    v___x_1122_ = v_inst_1118_;
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1120_);
                    lean_dec(v_inst_1118_);
                    v___x_1122_ = lean_box(0);
                    v_isShared_1123_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1124_ = lean_ctor_get(v_toApplicative_1120_, 1);
                lean_inc(v_toPure_1124_);
                lean_dec_ref(v_toApplicative_1120_);
                v___x_1125_ = lean_box(0);
                if v_isShared_1123_ == 0 {
                    lean_ctor_set(v___x_1122_, 1, v_s_x27_1119_);
                    lean_ctor_set(v___x_1122_, 0, v___x_1125_);
                    v___x_1127_ = v___x_1122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_s_x27_1119_);
                    v___x_1127_ = v_reuseFailAlloc_1129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1128_ = lean_apply_2(v_toPure_1124_, lean_box(0), v___x_1127_);
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set(
    mut v_00_u03c3_1132_: *mut LeanObject,
    mut v_m_1133_: *mut LeanObject,
    mut v_inst_1134_: *mut LeanObject,
    mut v_s_x27_1135_: *mut LeanObject,
    mut v_x_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v_toPure_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_unused_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1137_ = lean_ctor_get(v_inst_1134_, 0);
                v_isSharedCheck_1147_ = (!lean_is_exclusive(v_inst_1134_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v_unused_1148_ = lean_ctor_get(v_inst_1134_, 1);
                    lean_dec(v_unused_1148_);
                    v___x_1139_ = v_inst_1134_;
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1137_);
                    lean_dec(v_inst_1134_);
                    v___x_1139_ = lean_box(0);
                    v_isShared_1140_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1141_ = lean_ctor_get(v_toApplicative_1137_, 1);
                lean_inc(v_toPure_1141_);
                lean_dec_ref(v_toApplicative_1137_);
                v___x_1142_ = lean_box(0);
                if v_isShared_1140_ == 0 {
                    lean_ctor_set(v___x_1139_, 1, v_s_x27_1135_);
                    lean_ctor_set(v___x_1139_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_s_x27_1135_);
                    v___x_1144_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1145_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1144_);
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_set___boxed(
    mut v_00_u03c3_1149_: *mut LeanObject,
    mut v_m_1150_: *mut LeanObject,
    mut v_inst_1151_: *mut LeanObject,
    mut v_s_x27_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_StateT_set(
        v_00_u03c3_1149_,
        v_m_1150_,
        v_inst_1151_,
        v_s_x27_1152_,
        v_x_1153_,
    );
    lean_dec(v_x_1153_);
    return v_res_1154_;
}
pub unsafe fn l_StateT_modifyGet___redArg(
    mut v_inst_1155_: *mut LeanObject,
    mut v_f_1156_: *mut LeanObject,
    mut v_s_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1158_ = lean_ctor_get(v_inst_1155_, 0);
    lean_inc_ref(v_toApplicative_1158_);
    lean_dec_ref(v_inst_1155_);
    v_toPure_1159_ = lean_ctor_get(v_toApplicative_1158_, 1);
    lean_inc(v_toPure_1159_);
    lean_dec_ref(v_toApplicative_1158_);
    v___x_1160_ = lean_apply_1(v_f_1156_, v_s_1157_);
    v___x_1161_ = lean_apply_2(v_toPure_1159_, lean_box(0), v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_StateT_modifyGet(
    mut v_00_u03c3_1162_: *mut LeanObject,
    mut v_m_1163_: *mut LeanObject,
    mut v_inst_1164_: *mut LeanObject,
    mut v_00_u03b1_1165_: *mut LeanObject,
    mut v_f_1166_: *mut LeanObject,
    mut v_s_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1168_ = lean_ctor_get(v_inst_1164_, 0);
    lean_inc_ref(v_toApplicative_1168_);
    lean_dec_ref(v_inst_1164_);
    v_toPure_1169_ = lean_ctor_get(v_toApplicative_1168_, 1);
    lean_inc(v_toPure_1169_);
    lean_dec_ref(v_toApplicative_1168_);
    v___x_1170_ = lean_apply_1(v_f_1166_, v_s_1167_);
    v___x_1171_ = lean_apply_2(v_toPure_1169_, lean_box(0), v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_StateT_lift___redArg___lam__0(
    mut v_s_1172_: *mut LeanObject,
    mut v_toPure_1173_: *mut LeanObject,
    mut v_a_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1175_, 0, v_a_1174_);
    lean_ctor_set(v___x_1175_, 1, v_s_1172_);
    v___x_1176_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn l_StateT_lift___redArg(
    mut v_inst_1177_: *mut LeanObject,
    mut v_t_1178_: *mut LeanObject,
    mut v_s_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1180_ = lean_ctor_get(v_inst_1177_, 0);
    lean_inc_ref(v_toApplicative_1180_);
    v_toBind_1181_ = lean_ctor_get(v_inst_1177_, 1);
    lean_inc(v_toBind_1181_);
    lean_dec_ref(v_inst_1177_);
    v_toPure_1182_ = lean_ctor_get(v_toApplicative_1180_, 1);
    lean_inc(v_toPure_1182_);
    lean_dec_ref(v_toApplicative_1180_);
    v___f_1183_ = lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1183_, 0, v_s_1179_);
    lean_closure_set(v___f_1183_, 1, v_toPure_1182_);
    v___x_1184_ = lean_apply_4(
        v_toBind_1181_,
        lean_box(0),
        lean_box(0),
        v_t_1178_,
        v___f_1183_,
    );
    return v___x_1184_;
}
pub unsafe fn l_StateT_lift(
    mut v_00_u03c3_1185_: *mut LeanObject,
    mut v_m_1186_: *mut LeanObject,
    mut v_inst_1187_: *mut LeanObject,
    mut v_00_u03b1_1188_: *mut LeanObject,
    mut v_t_1189_: *mut LeanObject,
    mut v_s_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1191_ = lean_ctor_get(v_inst_1187_, 0);
    lean_inc_ref(v_toApplicative_1191_);
    v_toBind_1192_ = lean_ctor_get(v_inst_1187_, 1);
    lean_inc(v_toBind_1192_);
    lean_dec_ref(v_inst_1187_);
    v_toPure_1193_ = lean_ctor_get(v_toApplicative_1191_, 1);
    lean_inc(v_toPure_1193_);
    lean_dec_ref(v_toApplicative_1191_);
    v___f_1194_ = lean_alloc_closure(
        l_StateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1194_, 0, v_s_1190_);
    lean_closure_set(v___f_1194_, 1, v_toPure_1193_);
    v___x_1195_ = lean_apply_4(
        v_toBind_1192_,
        lean_box(0),
        lean_box(0),
        v_t_1189_,
        v___f_1194_,
    );
    return v___x_1195_;
}
pub unsafe fn l_StateT_instMonadLift___redArg(
    mut v_inst_1196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1197_, 0, lean_box(0));
    lean_closure_set(v___x_1197_, 1, lean_box(0));
    lean_closure_set(v___x_1197_, 2, v_inst_1196_);
    return v___x_1197_;
}
pub unsafe fn l_StateT_instMonadLift(
    mut v_00_u03c3_1198_: *mut LeanObject,
    mut v_m_1199_: *mut LeanObject,
    mut v_inst_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1201_, 0, lean_box(0));
    lean_closure_set(v___x_1201_, 1, lean_box(0));
    lean_closure_set(v___x_1201_, 2, v_inst_1200_);
    return v___x_1201_;
}
pub unsafe fn l_StateT_instMonadFunctor___lam__0(
    mut v_00_u03b1_1202_: *mut LeanObject,
    mut v_f_1203_: *mut LeanObject,
    mut v_x_1204_: *mut LeanObject,
    mut v_s_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    v___x_1206_ = lean_apply_1(v_x_1204_, v_s_1205_);
    v___x_1207_ = lean_apply_2(v_f_1203_, lean_box(0), v___x_1206_);
    return v___x_1207_;
}
pub unsafe fn l_StateT_instMonadFunctor(
    mut v_00_u03c3_1209_: *mut LeanObject,
    mut v_m_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1211_: *mut LeanObject = core::ptr::null_mut();
    v___f_1211_ = l_StateT_instMonadFunctor___closed__0;
    return v___f_1211_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__0(
    mut v___y_1212_: *mut LeanObject,
    mut v_toPure_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1215_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1215_, 0, v_a_1214_);
    lean_ctor_set(v___x_1215_, 1, v___y_1212_);
    v___x_1216_ = lean_apply_2(v_toPure_1213_, lean_box(0), v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__1(
    mut v_inst_1217_: *mut LeanObject,
    mut v_inst_1218_: *mut LeanObject,
    mut v_00_u03b1_1219_: *mut LeanObject,
    mut v___y_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1222_ = lean_ctor_get(v_inst_1218_, 0);
    lean_inc_ref(v_toApplicative_1222_);
    v_throw_1223_ = lean_ctor_get(v_inst_1217_, 0);
    lean_inc(v_throw_1223_);
    lean_dec_ref(v_inst_1217_);
    v_toBind_1224_ = lean_ctor_get(v_inst_1218_, 1);
    lean_inc(v_toBind_1224_);
    lean_dec_ref(v_inst_1218_);
    v_toPure_1225_ = lean_ctor_get(v_toApplicative_1222_, 1);
    lean_inc(v_toPure_1225_);
    lean_dec_ref(v_toApplicative_1222_);
    v___x_1226_ = lean_apply_2(v_throw_1223_, lean_box(0), v___y_1220_);
    v___f_1227_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1227_, 0, v___y_1221_);
    lean_closure_set(v___f_1227_, 1, v_toPure_1225_);
    v___x_1228_ = lean_apply_4(
        v_toBind_1224_,
        lean_box(0),
        lean_box(0),
        v___x_1226_,
        v___f_1227_,
    );
    return v___x_1228_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__2(
    mut v_c_1229_: *mut LeanObject,
    mut v_s_1230_: *mut LeanObject,
    mut v_e_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    v___x_1232_ = lean_apply_2(v_c_1229_, v_e_1231_, v_s_1230_);
    return v___x_1232_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg___lam__3(
    mut v_inst_1233_: *mut LeanObject,
    mut v_00_u03b1_1234_: *mut LeanObject,
    mut v_x_1235_: *mut LeanObject,
    mut v_c_1236_: *mut LeanObject,
    mut v_s_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_1238_ = lean_ctor_get(v_inst_1233_, 1);
    lean_inc(v_tryCatch_1238_);
    lean_dec_ref(v_inst_1233_);
    lean_inc(v_s_1237_);
    v___f_1239_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1239_, 0, v_c_1236_);
    lean_closure_set(v___f_1239_, 1, v_s_1237_);
    v___x_1240_ = lean_apply_1(v_x_1235_, v_s_1237_);
    v___x_1241_ = lean_apply_3(v_tryCatch_1238_, lean_box(0), v___x_1240_, v___f_1239_);
    return v___x_1241_;
}
pub unsafe fn l_StateT_instMonadExceptOf___redArg(
    mut v_inst_1242_: *mut LeanObject,
    mut v_inst_1243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1243_);
    v___f_1244_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1244_, 0, v_inst_1243_);
    lean_closure_set(v___f_1244_, 1, v_inst_1242_);
    v___f_1245_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1245_, 0, v_inst_1243_);
    v___x_1246_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1246_, 0, v___f_1244_);
    lean_ctor_set(v___x_1246_, 1, v___f_1245_);
    return v___x_1246_;
}
pub unsafe fn l_StateT_instMonadExceptOf(
    mut v_00_u03c3_1247_: *mut LeanObject,
    mut v_m_1248_: *mut LeanObject,
    mut v_inst_1249_: *mut LeanObject,
    mut v_00_u03b5_1250_: *mut LeanObject,
    mut v_inst_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1251_);
    v___f_1252_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1252_, 0, v_inst_1251_);
    lean_closure_set(v___f_1252_, 1, v_inst_1249_);
    v___f_1253_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1253_, 0, v_inst_1251_);
    v___x_1254_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1254_, 0, v___f_1252_);
    lean_ctor_set(v___x_1254_, 1, v___f_1253_);
    return v___x_1254_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__0(
    mut v_toPure_1255_: *mut LeanObject,
    mut v_____do__lift_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_a_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_1256_) == 0 {
                    v_a_1257_ = lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1265_ = (!lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1259_ = v_____do__lift_1256_;
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1257_);
                        lean_dec(v_____do__lift_1256_);
                        v___x_1259_ = lean_box(0);
                        v_isShared_1260_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1266_ = lean_ctor_get(v_____do__lift_1256_, 0);
                    v_isSharedCheck_1276_ = (!lean_is_exclusive(v_____do__lift_1256_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1268_ = v_____do__lift_1256_;
                        v_isShared_1269_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1266_);
                        lean_dec(v_____do__lift_1256_);
                        v___x_1268_ = lean_box(0);
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
                    v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1263_ = lean_apply_2(v_toPure_1255_, lean_box(0), v___x_1262_);
                return v___x_1263_;
            }
            3 => {
                v___x_1270_ = lean_box(0);
                v___x_1271_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                lean_ctor_set(v___x_1271_, 1, v_a_1266_);
                if v_isShared_1269_ == 0 {
                    lean_ctor_set(v___x_1268_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1274_ = lean_apply_2(v_toPure_1255_, lean_box(0), v___x_1273_);
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ForM_forIn___redArg___lam__1(
    mut v_f_1277_: *mut LeanObject,
    mut v_toBind_1278_: *mut LeanObject,
    mut v___f_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_b_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = lean_apply_2(v_f_1277_, v_a_1280_, v_b_1281_);
    v___x_1283_ = lean_apply_4(
        v_toBind_1278_,
        lean_box(0),
        lean_box(0),
        v___x_1282_,
        v___f_1279_,
    );
    return v___x_1283_;
}
pub unsafe fn l_ForM_forIn___redArg___lam__2(
    mut v_toPure_1284_: *mut LeanObject,
    mut v_____do__lift_1285_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1285_) == 0 {
        let mut v_a_1286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
        v_a_1286_ = lean_ctor_get(v_____do__lift_1285_, 0);
        lean_inc(v_a_1286_);
        lean_dec_ref_known(v_____do__lift_1285_, 1);
        v___x_1287_ = lean_apply_2(v_toPure_1284_, lean_box(0), v_a_1286_);
        return v___x_1287_;
    } else {
        let mut v_a_1288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
        v_a_1288_ = lean_ctor_get(v_____do__lift_1285_, 0);
        lean_inc(v_a_1288_);
        lean_dec_ref_known(v_____do__lift_1285_, 1);
        v_snd_1289_ = lean_ctor_get(v_a_1288_, 1);
        lean_inc(v_snd_1289_);
        lean_dec(v_a_1288_);
        v___x_1290_ = lean_apply_2(v_toPure_1284_, lean_box(0), v_snd_1289_);
        return v___x_1290_;
    }
}
pub unsafe fn l_ForM_forIn___redArg(
    mut v_inst_1291_: *mut LeanObject,
    mut v_inst_1292_: *mut LeanObject,
    mut v_x_1293_: *mut LeanObject,
    mut v_b_1294_: *mut LeanObject,
    mut v_f_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1296_ = lean_ctor_get(v_inst_1291_, 0);
    lean_inc_ref(v_toApplicative_1296_);
    v_toBind_1297_ = lean_ctor_get(v_inst_1291_, 1);
    lean_inc_n(v_toBind_1297_, 2);
    lean_dec_ref(v_inst_1291_);
    v_toPure_1298_ = lean_ctor_get(v_toApplicative_1296_, 1);
    lean_inc_n(v_toPure_1298_, 2);
    lean_dec_ref(v_toApplicative_1296_);
    v___f_1299_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1299_, 0, v_toPure_1298_);
    v_g_1300_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v_g_1300_, 0, v_f_1295_);
    lean_closure_set(v_g_1300_, 1, v_toBind_1297_);
    lean_closure_set(v_g_1300_, 2, v___f_1299_);
    v___f_1301_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1301_, 0, v_toPure_1298_);
    v___x_1302_ = lean_apply_3(v_inst_1292_, v_x_1293_, v_g_1300_, v_b_1294_);
    v___x_1303_ = lean_apply_4(
        v_toBind_1297_,
        lean_box(0),
        lean_box(0),
        v___x_1302_,
        v___f_1301_,
    );
    return v___x_1303_;
}
pub unsafe fn l_ForM_forIn(
    mut v_m_1304_: *mut LeanObject,
    mut v_00_u03b2_1305_: *mut LeanObject,
    mut v_00_u03c1_1306_: *mut LeanObject,
    mut v_00_u03b1_1307_: *mut LeanObject,
    mut v_inst_1308_: *mut LeanObject,
    mut v_inst_1309_: *mut LeanObject,
    mut v_x_1310_: *mut LeanObject,
    mut v_b_1311_: *mut LeanObject,
    mut v_f_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1313_ = lean_ctor_get(v_inst_1308_, 0);
    lean_inc_ref(v_toApplicative_1313_);
    v_toBind_1314_ = lean_ctor_get(v_inst_1308_, 1);
    lean_inc_n(v_toBind_1314_, 2);
    lean_dec_ref(v_inst_1308_);
    v_toPure_1315_ = lean_ctor_get(v_toApplicative_1313_, 1);
    lean_inc_n(v_toPure_1315_, 2);
    lean_dec_ref(v_toApplicative_1313_);
    v___f_1316_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1316_, 0, v_toPure_1315_);
    v_g_1317_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v_g_1317_, 0, v_f_1312_);
    lean_closure_set(v_g_1317_, 1, v_toBind_1314_);
    lean_closure_set(v_g_1317_, 2, v___f_1316_);
    v___f_1318_ = lean_alloc_closure(
        l_ForM_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1318_, 0, v_toPure_1315_);
    v___x_1319_ = lean_apply_3(v_inst_1309_, v_x_1310_, v_g_1317_, v_b_1311_);
    v___x_1320_ = lean_apply_4(
        v_toBind_1314_,
        lean_box(0),
        lean_box(0),
        v___x_1319_,
        v___f_1318_,
    );
    return v___x_1320_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad___redArg(
    mut v_inst_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1321_, 2);
    v___x_1322_ = lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1322_, 0, lean_box(0));
    lean_closure_set(v___x_1322_, 1, lean_box(0));
    lean_closure_set(v___x_1322_, 2, v_inst_1321_);
    v___x_1323_ = lean_alloc_closure(l_StateT_set___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1323_, 0, lean_box(0));
    lean_closure_set(v___x_1323_, 1, lean_box(0));
    lean_closure_set(v___x_1323_, 2, v_inst_1321_);
    v___x_1324_ = lean_alloc_closure(l_StateT_modifyGet as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1324_, 0, lean_box(0));
    lean_closure_set(v___x_1324_, 1, lean_box(0));
    lean_closure_set(v___x_1324_, 2, v_inst_1321_);
    v___x_1325_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1325_, 0, v___x_1322_);
    lean_ctor_set(v___x_1325_, 1, v___x_1323_);
    lean_ctor_set(v___x_1325_, 2, v___x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_instMonadStateOfStateTOfMonad(
    mut v_00_u03c3_1326_: *mut LeanObject,
    mut v_m_1327_: *mut LeanObject,
    mut v_inst_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1329_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__0(
    mut v_fst_1330_: *mut LeanObject,
    mut v_00_u03b2_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    v___x_1333_ = lean_apply_1(v_x_1332_, v_fst_1330_);
    return v___x_1333_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__1(
    mut v_snd_1334_: *mut LeanObject,
    mut v_toPure_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1337_, 0, v_a_1336_);
    lean_ctor_set(v___x_1337_, 1, v_snd_1334_);
    v___x_1338_ = lean_apply_2(v_toPure_1335_, lean_box(0), v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__2(
    mut v_f_1339_: *mut LeanObject,
    mut v_toPure_1340_: *mut LeanObject,
    mut v_toBind_1341_: *mut LeanObject,
    mut v_____x_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1343_ = lean_ctor_get(v_____x_1342_, 0);
    lean_inc(v_fst_1343_);
    v_snd_1344_ = lean_ctor_get(v_____x_1342_, 1);
    lean_inc(v_snd_1344_);
    lean_dec_ref(v_____x_1342_);
    v___f_1345_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1345_, 0, v_fst_1343_);
    v___x_1346_ = lean_apply_1(v_f_1339_, v___f_1345_);
    v___f_1347_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1347_, 0, v_snd_1344_);
    lean_closure_set(v___f_1347_, 1, v_toPure_1340_);
    v___x_1348_ = lean_apply_4(
        v_toBind_1341_,
        lean_box(0),
        lean_box(0),
        v___x_1346_,
        v___f_1347_,
    );
    return v___x_1348_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__3(
    mut v_inst_1349_: *mut LeanObject,
    mut v_00_u03b1_1350_: *mut LeanObject,
    mut v_f_1351_: *mut LeanObject,
    mut v___y_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_toPure_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1353_ = lean_ctor_get(v_inst_1349_, 0);
                v_toBind_1354_ = lean_ctor_get(v_inst_1349_, 1);
                v_isSharedCheck_1365_ = (!lean_is_exclusive(v_inst_1349_)) as u8;
                if v_isSharedCheck_1365_ == 0 {
                    v___x_1356_ = v_inst_1349_;
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1354_);
                    lean_inc(v_toApplicative_1353_);
                    lean_dec(v_inst_1349_);
                    v___x_1356_ = lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1358_ = lean_ctor_get(v_toApplicative_1353_, 1);
                lean_inc_n(v_toPure_1358_, 2);
                lean_dec_ref(v_toApplicative_1353_);
                lean_inc(v_toBind_1354_);
                v___f_1359_ = lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__2 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_1359_, 0, v_f_1351_);
                lean_closure_set(v___f_1359_, 1, v_toPure_1358_);
                lean_closure_set(v___f_1359_, 2, v_toBind_1354_);
                lean_inc(v___y_1352_);
                if v_isShared_1357_ == 0 {
                    lean_ctor_set(v___x_1356_, 1, v___y_1352_);
                    lean_ctor_set(v___x_1356_, 0, v___y_1352_);
                    v___x_1361_ = v___x_1356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___y_1352_);
                    lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___y_1352_);
                    v___x_1361_ = v_reuseFailAlloc_1364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1362_ = lean_apply_2(v_toPure_1358_, lean_box(0), v___x_1361_);
                v___x_1363_ = lean_apply_4(
                    v_toBind_1354_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_fst_1366_: *mut LeanObject,
    mut v_toPure_1367_: *mut LeanObject,
    mut v_____x_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_unused_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1369_ = lean_ctor_get(v_____x_1368_, 1);
                v_isSharedCheck_1377_ = (!lean_is_exclusive(v_____x_1368_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v_unused_1378_ = lean_ctor_get(v_____x_1368_, 0);
                    lean_dec(v_unused_1378_);
                    v___x_1371_ = v_____x_1368_;
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1369_);
                    lean_dec(v_____x_1368_);
                    v___x_1371_ = lean_box(0);
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1372_ == 0 {
                    lean_ctor_set(v___x_1371_, 0, v_fst_1366_);
                    v___x_1374_ = v___x_1371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fst_1366_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1375_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1374_);
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_monadControl___redArg___lam__5(
    mut v_inst_1379_: *mut LeanObject,
    mut v_____x_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v_toBind_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1381_ = lean_ctor_get(v_____x_1380_, 0);
                lean_inc(v_fst_1381_);
                lean_dec_ref(v_____x_1380_);
                v_toApplicative_1382_ = lean_ctor_get(v_inst_1379_, 0);
                lean_inc_ref(v_toApplicative_1382_);
                v_fst_1383_ = lean_ctor_get(v_fst_1381_, 0);
                v_snd_1384_ = lean_ctor_get(v_fst_1381_, 1);
                v_isSharedCheck_1397_ = (!lean_is_exclusive(v_fst_1381_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1386_ = v_fst_1381_;
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1384_);
                    lean_inc(v_fst_1383_);
                    lean_dec(v_fst_1381_);
                    v___x_1386_ = lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_1388_ = lean_ctor_get(v_inst_1379_, 1);
                lean_inc(v_toBind_1388_);
                lean_dec_ref(v_inst_1379_);
                v_toPure_1389_ = lean_ctor_get(v_toApplicative_1382_, 1);
                lean_inc_n(v_toPure_1389_, 2);
                lean_dec_ref(v_toApplicative_1382_);
                v___f_1390_ = lean_alloc_closure(
                    l_StateT_monadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1390_, 0, v_fst_1383_);
                lean_closure_set(v___f_1390_, 1, v_toPure_1389_);
                v___x_1391_ = lean_box(0);
                if v_isShared_1387_ == 0 {
                    lean_ctor_set(v___x_1386_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_snd_1384_);
                    v___x_1393_ = v_reuseFailAlloc_1396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1394_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1393_);
                v___x_1395_ = lean_apply_4(
                    v_toBind_1388_,
                    lean_box(0),
                    lean_box(0),
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
    mut v___y_1398_: *mut LeanObject,
    mut v_toPure_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1401_, 0, v_a_1400_);
    lean_ctor_set(v___x_1401_, 1, v___y_1398_);
    v___x_1402_ = lean_apply_2(v_toPure_1399_, lean_box(0), v___x_1401_);
    return v___x_1402_;
}
pub unsafe fn l_StateT_monadControl___redArg___lam__7(
    mut v_inst_1403_: *mut LeanObject,
    mut v___f_1404_: *mut LeanObject,
    mut v_00_u03b1_1405_: *mut LeanObject,
    mut v_x_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1408_ = lean_ctor_get(v_inst_1403_, 0);
    lean_inc_ref(v_toApplicative_1408_);
    v_toBind_1409_ = lean_ctor_get(v_inst_1403_, 1);
    lean_inc_n(v_toBind_1409_, 2);
    lean_dec_ref(v_inst_1403_);
    v_toPure_1410_ = lean_ctor_get(v_toApplicative_1408_, 1);
    lean_inc(v_toPure_1410_);
    lean_dec_ref(v_toApplicative_1408_);
    v___f_1411_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__6 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1411_, 0, v___y_1407_);
    lean_closure_set(v___f_1411_, 1, v_toPure_1410_);
    v___x_1412_ = lean_apply_4(
        v_toBind_1409_,
        lean_box(0),
        lean_box(0),
        v_x_1406_,
        v___f_1411_,
    );
    v___x_1413_ = lean_apply_4(
        v_toBind_1409_,
        lean_box(0),
        lean_box(0),
        v___x_1412_,
        v___f_1404_,
    );
    return v___x_1413_;
}
pub unsafe fn l_StateT_monadControl___redArg(mut v_inst_1414_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1414_, 2);
    v___f_1415_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1415_, 0, v_inst_1414_);
    v___f_1416_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1416_, 0, v_inst_1414_);
    v___f_1417_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1417_, 0, v_inst_1414_);
    lean_closure_set(v___f_1417_, 1, v___f_1416_);
    v___x_1418_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1418_, 0, v___f_1415_);
    lean_ctor_set(v___x_1418_, 1, v___f_1417_);
    return v___x_1418_;
}
pub unsafe fn l_StateT_monadControl(
    mut v_00_u03c3_1419_: *mut LeanObject,
    mut v_m_1420_: *mut LeanObject,
    mut v_inst_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1421_, 2);
    v___f_1422_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1422_, 0, v_inst_1421_);
    v___f_1423_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1423_, 0, v_inst_1421_);
    v___f_1424_ = lean_alloc_closure(
        l_StateT_monadControl___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1424_, 0, v_inst_1421_);
    lean_closure_set(v___f_1424_, 1, v___f_1423_);
    v___x_1425_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v___f_1422_);
    lean_ctor_set(v___x_1425_, 1, v___f_1424_);
    return v___x_1425_;
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__0(
    mut v_toPure_1426_: *mut LeanObject,
    mut v_____x_1427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v_fst_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_unused_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1428_ = lean_ctor_get(v_____x_1427_, 0);
                lean_inc(v_fst_1428_);
                v_snd_1429_ = lean_ctor_get(v_____x_1427_, 1);
                lean_inc(v_snd_1429_);
                lean_dec_ref(v_____x_1427_);
                v_fst_1430_ = lean_ctor_get(v_fst_1428_, 0);
                v_isSharedCheck_1447_ = (!lean_is_exclusive(v_fst_1428_)) as u8;
                if v_isSharedCheck_1447_ == 0 {
                    v_unused_1448_ = lean_ctor_get(v_fst_1428_, 1);
                    lean_dec(v_unused_1448_);
                    v___x_1432_ = v_fst_1428_;
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fst_1430_);
                    lean_dec(v_fst_1428_);
                    v___x_1432_ = lean_box(0);
                    v_isShared_1433_ = v_isSharedCheck_1447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1434_ = lean_ctor_get(v_snd_1429_, 0);
                v_snd_1435_ = lean_ctor_get(v_snd_1429_, 1);
                v_isSharedCheck_1446_ = (!lean_is_exclusive(v_snd_1429_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v___x_1437_ = v_snd_1429_;
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1435_);
                    lean_inc(v_fst_1434_);
                    lean_dec(v_snd_1429_);
                    v___x_1437_ = lean_box(0);
                    v_isShared_1438_ = v_isSharedCheck_1446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1438_ == 0 {
                    lean_ctor_set(v___x_1437_, 1, v_fst_1434_);
                    lean_ctor_set(v___x_1437_, 0, v_fst_1430_);
                    v___x_1440_ = v___x_1437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1430_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_fst_1434_);
                    v___x_1440_ = v_reuseFailAlloc_1445_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1433_ == 0 {
                    lean_ctor_set(v___x_1432_, 1, v_snd_1435_);
                    lean_ctor_set(v___x_1432_, 0, v___x_1440_);
                    v___x_1442_ = v___x_1432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1435_);
                    v___x_1442_ = v_reuseFailAlloc_1444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1443_ = lean_apply_2(v_toPure_1426_, lean_box(0), v___x_1442_);
                return v___x_1443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__1(
    mut v_h_1449_: *mut LeanObject,
    mut v_s_1450_: *mut LeanObject,
    mut v_x_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v_fst_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1451_) == 0 {
                    v___x_1452_ = lean_box(0);
                    v___x_1453_ = lean_apply_2(v_h_1449_, v___x_1452_, v_s_1450_);
                    return v___x_1453_;
                } else {
                    lean_dec(v_s_1450_);
                    v_val_1454_ = lean_ctor_get(v_x_1451_, 0);
                    v_isSharedCheck_1464_ = (!lean_is_exclusive(v_x_1451_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1456_ = v_x_1451_;
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1454_);
                        lean_dec(v_x_1451_);
                        v___x_1456_ = lean_box(0);
                        v_isShared_1457_ = v_isSharedCheck_1464_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1458_ = lean_ctor_get(v_val_1454_, 0);
                lean_inc(v_fst_1458_);
                v_snd_1459_ = lean_ctor_get(v_val_1454_, 1);
                lean_inc(v_snd_1459_);
                lean_dec(v_val_1454_);
                if v_isShared_1457_ == 0 {
                    lean_ctor_set(v___x_1456_, 0, v_fst_1458_);
                    v___x_1461_ = v___x_1456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_fst_1458_);
                    v___x_1461_ = v_reuseFailAlloc_1463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1462_ = lean_apply_2(v_h_1449_, v___x_1461_, v_snd_1459_);
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_StateT_tryFinally___redArg___lam__2(
    mut v_inst_1465_: *mut LeanObject,
    mut v_toBind_1466_: *mut LeanObject,
    mut v___f_1467_: *mut LeanObject,
    mut v_00_u03b1_1468_: *mut LeanObject,
    mut v_00_u03b2_1469_: *mut LeanObject,
    mut v_x_1470_: *mut LeanObject,
    mut v_h_1471_: *mut LeanObject,
    mut v_s_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_1472_);
    v___f_1473_ = lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1473_, 0, v_h_1471_);
    lean_closure_set(v___f_1473_, 1, v_s_1472_);
    v___x_1474_ = lean_apply_1(v_x_1470_, v_s_1472_);
    v___x_1475_ = lean_apply_4(
        v_inst_1465_,
        lean_box(0),
        lean_box(0),
        v___x_1474_,
        v___f_1473_,
    );
    v___x_1476_ = lean_apply_4(
        v_toBind_1466_,
        lean_box(0),
        lean_box(0),
        v___x_1475_,
        v___f_1467_,
    );
    return v___x_1476_;
}
pub unsafe fn l_StateT_tryFinally___redArg(
    mut v_inst_1477_: *mut LeanObject,
    mut v_inst_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1479_ = lean_ctor_get(v_inst_1478_, 0);
    lean_inc_ref(v_toApplicative_1479_);
    v_toBind_1480_ = lean_ctor_get(v_inst_1478_, 1);
    lean_inc(v_toBind_1480_);
    lean_dec_ref(v_inst_1478_);
    v_toPure_1481_ = lean_ctor_get(v_toApplicative_1479_, 1);
    lean_inc(v_toPure_1481_);
    lean_dec_ref(v_toApplicative_1479_);
    v___f_1482_ = lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1482_, 0, v_toPure_1481_);
    v___f_1483_ = lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1483_, 0, v_inst_1477_);
    lean_closure_set(v___f_1483_, 1, v_toBind_1480_);
    lean_closure_set(v___f_1483_, 2, v___f_1482_);
    return v___f_1483_;
}
pub unsafe fn l_StateT_tryFinally(
    mut v_m_1484_: *mut LeanObject,
    mut v_00_u03c3_1485_: *mut LeanObject,
    mut v_inst_1486_: *mut LeanObject,
    mut v_inst_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1492_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1488_ = lean_ctor_get(v_inst_1487_, 0);
    lean_inc_ref(v_toApplicative_1488_);
    v_toBind_1489_ = lean_ctor_get(v_inst_1487_, 1);
    lean_inc(v_toBind_1489_);
    lean_dec_ref(v_inst_1487_);
    v_toPure_1490_ = lean_ctor_get(v_toApplicative_1488_, 1);
    lean_inc(v_toPure_1490_);
    lean_dec_ref(v_toApplicative_1488_);
    v___f_1491_ = lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1491_, 0, v_toPure_1490_);
    v___f_1492_ = lean_alloc_closure(
        l_StateT_tryFinally___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1492_, 0, v_inst_1486_);
    lean_closure_set(v___f_1492_, 1, v_toBind_1489_);
    lean_closure_set(v___f_1492_, 2, v___f_1491_);
    return v___f_1492_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg___lam__0(
    mut v_x_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1494_ = lean_ctor_get(v_x_1493_, 0);
                v_snd_1495_ = lean_ctor_get(v_x_1493_, 1);
                v_isSharedCheck_1502_ = (!lean_is_exclusive(v_x_1493_)) as u8;
                if v_isSharedCheck_1502_ == 0 {
                    v___x_1497_ = v_x_1493_;
                    v_isShared_1498_ = v_isSharedCheck_1502_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1495_);
                    lean_inc(v_fst_1494_);
                    lean_dec(v_x_1493_);
                    v___x_1497_ = lean_box(0);
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
                    v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_fst_1494_);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_snd_1495_);
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
    mut v_toFunctor_1503_: *mut LeanObject,
    mut v_inst_1504_: *mut LeanObject,
    mut v___f_1505_: *mut LeanObject,
    mut v_00_u03b1_1506_: *mut LeanObject,
    mut v_x_1507_: *mut LeanObject,
    mut v_s_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    v_map_1509_ = lean_ctor_get(v_toFunctor_1503_, 0);
    lean_inc(v_map_1509_);
    lean_dec_ref(v_toFunctor_1503_);
    v___x_1510_ = lean_apply_1(v_x_1507_, v_s_1508_);
    v___x_1511_ = lean_apply_2(v_inst_1504_, lean_box(0), v___x_1510_);
    v___x_1512_ = lean_apply_4(
        v_map_1509_,
        lean_box(0),
        lean_box(0),
        v___f_1505_,
        v___x_1511_,
    );
    return v___x_1512_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad___redArg(
    mut v_inst_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1519_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1516_ = lean_ctor_get(v_inst_1514_, 0);
    lean_inc_ref(v_toApplicative_1516_);
    lean_dec_ref(v_inst_1514_);
    v_toFunctor_1517_ = lean_ctor_get(v_toApplicative_1516_, 0);
    lean_inc_ref(v_toFunctor_1517_);
    lean_dec_ref(v_toApplicative_1516_);
    v___f_1518_ = l_instMonadAttachStateTOfMonad___redArg___closed__0;
    v___f_1519_ = lean_alloc_closure(
        l_instMonadAttachStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_1519_, 0, v_toFunctor_1517_);
    lean_closure_set(v___f_1519_, 1, v_inst_1515_);
    lean_closure_set(v___f_1519_, 2, v___f_1518_);
    return v___f_1519_;
}
pub unsafe fn l_instMonadAttachStateTOfMonad(
    mut v_m_1520_: *mut LeanObject,
    mut v_00_u03c3_1521_: *mut LeanObject,
    mut v_inst_1522_: *mut LeanObject,
    mut v_inst_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_instMonadAttachStateTOfMonad___redArg(v_inst_1522_, v_inst_1523_);
    return v___x_1524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_State(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_State(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_State(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_State(builtin);
}
