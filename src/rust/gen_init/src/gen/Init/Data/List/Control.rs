// Lean compiler output
// Module: Init.Data.List.Control
// Imports: Init.Control.Lawful
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_mapTR, l_List_mapTR_loop___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
use crate::ffi::{lean_array_push, lean_array_to_list};
pub static l_List_mapA___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_mapA___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_mapA___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapA___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_zipWithM___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_List_zipWithM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_zipWithM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_instFunctor___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_instFunctor___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_mapTR as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instFunctor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_instFunctor___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_instFunctor___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_instFunctor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_List_instFunctor: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_mapM_loop___redArg(
    mut v_inst_793_: *mut crate::leanh::LeanObject,
    mut v_f_794_: *mut crate::leanh::LeanObject,
    mut v_x_795_: *mut crate::leanh::LeanObject,
    mut v_x_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_795_) == 0 {
        let mut v_toApplicative_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_797_ = crate::leanh::lean_ctor_get(v_inst_793_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_797_);
        crate::leanh::lean_dec(v_f_794_);
        crate::leanh::lean_dec_ref(v_inst_793_);
        v_toPure_798_ = crate::leanh::lean_ctor_get(v_toApplicative_797_, 1);
        crate::leanh::lean_inc(v_toPure_798_);
        crate::leanh::lean_dec_ref(v_toApplicative_797_);
        v___x_799_ = l_List_reverse___redArg(v_x_796_);
        v___x_800_ =
            crate::leanh::lean_apply_2(v_toPure_798_, crate::leanh::lean_box(0), v___x_799_);
        return v___x_800_;
    } else {
        let mut v_toBind_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_801_ = crate::leanh::lean_ctor_get(v_inst_793_, 1);
        crate::leanh::lean_inc(v_toBind_801_);
        v_head_802_ = crate::leanh::lean_ctor_get(v_x_795_, 0);
        crate::leanh::lean_inc(v_head_802_);
        v_tail_803_ = crate::leanh::lean_ctor_get(v_x_795_, 1);
        crate::leanh::lean_inc(v_tail_803_);
        crate::leanh::lean_dec_ref_known(v_x_795_, 2);
        crate::leanh::lean_inc(v_f_794_);
        v___f_804_ = crate::leanh::lean_alloc_closure(
            l_List_mapM_loop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_804_, 0, v_x_796_);
        crate::leanh::lean_closure_set(v___f_804_, 1, v_inst_793_);
        crate::leanh::lean_closure_set(v___f_804_, 2, v_f_794_);
        crate::leanh::lean_closure_set(v___f_804_, 3, v_tail_803_);
        v___x_805_ = crate::leanh::lean_apply_1(v_f_794_, v_head_802_);
        v___x_806_ = crate::leanh::lean_apply_4(
            v_toBind_801_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_805_,
            v___f_804_,
        );
        return v___x_806_;
    }
}
pub unsafe fn l_List_mapM_loop___redArg___lam__0(
    mut v_x_807_: *mut crate::leanh::LeanObject,
    mut v_inst_808_: *mut crate::leanh::LeanObject,
    mut v_f_809_: *mut crate::leanh::LeanObject,
    mut v_tail_810_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_812_, 0, v_____do__lift_811_);
    crate::leanh::lean_ctor_set(v___x_812_, 1, v_x_807_);
    v___x_813_ = l_List_mapM_loop___redArg(v_inst_808_, v_f_809_, v_tail_810_, v___x_812_);
    return v___x_813_;
}
pub unsafe fn l_List_mapM_loop(
    mut v_m_814_: *mut crate::leanh::LeanObject,
    mut v_inst_815_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_817_: *mut crate::leanh::LeanObject,
    mut v_f_818_: *mut crate::leanh::LeanObject,
    mut v_x_819_: *mut crate::leanh::LeanObject,
    mut v_x_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_List_mapM_loop___redArg(v_inst_815_, v_f_818_, v_x_819_, v_x_820_);
    return v___x_821_;
}
pub unsafe fn l_List_mapM___redArg(
    mut v_inst_822_: *mut crate::leanh::LeanObject,
    mut v_f_823_: *mut crate::leanh::LeanObject,
    mut v_as_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = crate::leanh::lean_box(0);
    v___x_826_ = l_List_mapM_loop___redArg(v_inst_822_, v_f_823_, v_as_824_, v___x_825_);
    return v___x_826_;
}
pub unsafe fn l_List_mapM(
    mut v_m_827_: *mut crate::leanh::LeanObject,
    mut v_inst_828_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_830_: *mut crate::leanh::LeanObject,
    mut v_f_831_: *mut crate::leanh::LeanObject,
    mut v_as_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_833_ = crate::leanh::lean_box(0);
    v___x_834_ = l_List_mapM_loop___redArg(v_inst_828_, v_f_831_, v_as_832_, v___x_833_);
    return v___x_834_;
}
pub unsafe fn l_List_mapA___redArg___lam__0(
    mut v_head_835_: *mut crate::leanh::LeanObject,
    mut v_tail_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_837_, 0, v_head_835_);
    crate::leanh::lean_ctor_set(v___x_837_, 1, v_tail_836_);
    return v___x_837_;
}
pub unsafe fn l_List_mapA___redArg(
    mut v_inst_839_: *mut crate::leanh::LeanObject,
    mut v_f_840_: *mut crate::leanh::LeanObject,
    mut v_x_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_841_) == 0 {
        let mut v_toPure_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_840_);
        v_toPure_842_ = crate::leanh::lean_ctor_get(v_inst_839_, 1);
        crate::leanh::lean_inc(v_toPure_842_);
        crate::leanh::lean_dec_ref(v_inst_839_);
        v___x_843_ = crate::leanh::lean_box(0);
        v___x_844_ =
            crate::leanh::lean_apply_2(v_toPure_842_, crate::leanh::lean_box(0), v___x_843_);
        return v___x_844_;
    } else {
        let mut v_toFunctor_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSeq_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_845_ = crate::leanh::lean_ctor_get(v_inst_839_, 0);
        v_toSeq_846_ = crate::leanh::lean_ctor_get(v_inst_839_, 2);
        crate::leanh::lean_inc(v_toSeq_846_);
        v_head_847_ = crate::leanh::lean_ctor_get(v_x_841_, 0);
        crate::leanh::lean_inc(v_head_847_);
        v_tail_848_ = crate::leanh::lean_ctor_get(v_x_841_, 1);
        crate::leanh::lean_inc(v_tail_848_);
        crate::leanh::lean_dec_ref_known(v_x_841_, 2);
        v_map_849_ = crate::leanh::lean_ctor_get(v_toFunctor_845_, 0);
        crate::leanh::lean_inc(v_map_849_);
        v___f_850_ = l_List_mapA___redArg___closed__0;
        crate::leanh::lean_inc(v_f_840_);
        v___f_851_ = crate::leanh::lean_alloc_closure(
            l_List_mapA___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_851_, 0, v_inst_839_);
        crate::leanh::lean_closure_set(v___f_851_, 1, v_f_840_);
        crate::leanh::lean_closure_set(v___f_851_, 2, v_tail_848_);
        v___x_852_ = crate::leanh::lean_apply_1(v_f_840_, v_head_847_);
        v___x_853_ = crate::leanh::lean_apply_4(
            v_map_849_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_850_,
            v___x_852_,
        );
        v___x_854_ = crate::leanh::lean_apply_4(
            v_toSeq_846_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_853_,
            v___f_851_,
        );
        return v___x_854_;
    }
}
pub unsafe fn l_List_mapA___redArg___lam__1(
    mut v_inst_855_: *mut crate::leanh::LeanObject,
    mut v_f_856_: *mut crate::leanh::LeanObject,
    mut v_tail_857_: *mut crate::leanh::LeanObject,
    mut v_x_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l_List_mapA___redArg(v_inst_855_, v_f_856_, v_tail_857_);
    return v___x_859_;
}
pub unsafe fn l_List_mapA(
    mut v_m_860_: *mut crate::leanh::LeanObject,
    mut v_inst_861_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_863_: *mut crate::leanh::LeanObject,
    mut v_f_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_List_mapA___redArg(v_inst_861_, v_f_864_, v_x_865_);
    return v___x_866_;
}
pub unsafe fn l_List_forM___redArg(
    mut v_inst_867_: *mut crate::leanh::LeanObject,
    mut v_as_868_: *mut crate::leanh::LeanObject,
    mut v_f_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_as_868_) == 0 {
        let mut v_toApplicative_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_870_ = crate::leanh::lean_ctor_get(v_inst_867_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_870_);
        crate::leanh::lean_dec(v_f_869_);
        crate::leanh::lean_dec_ref(v_inst_867_);
        v_toPure_871_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 1);
        crate::leanh::lean_inc(v_toPure_871_);
        crate::leanh::lean_dec_ref(v_toApplicative_870_);
        v___x_872_ = crate::leanh::lean_box(0);
        v___x_873_ =
            crate::leanh::lean_apply_2(v_toPure_871_, crate::leanh::lean_box(0), v___x_872_);
        return v___x_873_;
    } else {
        let mut v_toBind_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_874_ = crate::leanh::lean_ctor_get(v_inst_867_, 1);
        crate::leanh::lean_inc(v_toBind_874_);
        v_head_875_ = crate::leanh::lean_ctor_get(v_as_868_, 0);
        crate::leanh::lean_inc(v_head_875_);
        v_tail_876_ = crate::leanh::lean_ctor_get(v_as_868_, 1);
        crate::leanh::lean_inc(v_tail_876_);
        crate::leanh::lean_dec_ref_known(v_as_868_, 2);
        crate::leanh::lean_inc(v_f_869_);
        v___f_877_ = crate::leanh::lean_alloc_closure(
            l_List_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_877_, 0, v_inst_867_);
        crate::leanh::lean_closure_set(v___f_877_, 1, v_tail_876_);
        crate::leanh::lean_closure_set(v___f_877_, 2, v_f_869_);
        v___x_878_ = crate::leanh::lean_apply_1(v_f_869_, v_head_875_);
        v___x_879_ = crate::leanh::lean_apply_4(
            v_toBind_874_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_878_,
            v___f_877_,
        );
        return v___x_879_;
    }
}
pub unsafe fn l_List_forM___redArg___lam__0(
    mut v_inst_880_: *mut crate::leanh::LeanObject,
    mut v_tail_881_: *mut crate::leanh::LeanObject,
    mut v_f_882_: *mut crate::leanh::LeanObject,
    mut v_____r_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = l_List_forM___redArg(v_inst_880_, v_tail_881_, v_f_882_);
    return v___x_884_;
}
pub unsafe fn l_List_forM(
    mut v_m_885_: *mut crate::leanh::LeanObject,
    mut v_inst_886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_887_: *mut crate::leanh::LeanObject,
    mut v_as_888_: *mut crate::leanh::LeanObject,
    mut v_f_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_List_forM___redArg(v_inst_886_, v_as_888_, v_f_889_);
    return v___x_890_;
}
pub unsafe fn l_List_forA___redArg(
    mut v_inst_891_: *mut crate::leanh::LeanObject,
    mut v_as_892_: *mut crate::leanh::LeanObject,
    mut v_f_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_as_892_) == 0 {
        let mut v_toPure_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_893_);
        v_toPure_894_ = crate::leanh::lean_ctor_get(v_inst_891_, 1);
        crate::leanh::lean_inc(v_toPure_894_);
        crate::leanh::lean_dec_ref(v_inst_891_);
        v___x_895_ = crate::leanh::lean_box(0);
        v___x_896_ =
            crate::leanh::lean_apply_2(v_toPure_894_, crate::leanh::lean_box(0), v___x_895_);
        return v___x_896_;
    } else {
        let mut v_toSeqRight_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toSeqRight_897_ = crate::leanh::lean_ctor_get(v_inst_891_, 4);
        crate::leanh::lean_inc(v_toSeqRight_897_);
        v_head_898_ = crate::leanh::lean_ctor_get(v_as_892_, 0);
        crate::leanh::lean_inc(v_head_898_);
        v_tail_899_ = crate::leanh::lean_ctor_get(v_as_892_, 1);
        crate::leanh::lean_inc(v_tail_899_);
        crate::leanh::lean_dec_ref_known(v_as_892_, 2);
        crate::leanh::lean_inc(v_f_893_);
        v___f_900_ = crate::leanh::lean_alloc_closure(
            l_List_forA___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_900_, 0, v_inst_891_);
        crate::leanh::lean_closure_set(v___f_900_, 1, v_tail_899_);
        crate::leanh::lean_closure_set(v___f_900_, 2, v_f_893_);
        v___x_901_ = crate::leanh::lean_apply_1(v_f_893_, v_head_898_);
        v___x_902_ = crate::leanh::lean_apply_4(
            v_toSeqRight_897_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_901_,
            v___f_900_,
        );
        return v___x_902_;
    }
}
pub unsafe fn l_List_forA___redArg___lam__0(
    mut v_inst_903_: *mut crate::leanh::LeanObject,
    mut v_tail_904_: *mut crate::leanh::LeanObject,
    mut v_f_905_: *mut crate::leanh::LeanObject,
    mut v_x_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l_List_forA___redArg(v_inst_903_, v_tail_904_, v_f_905_);
    return v___x_907_;
}
pub unsafe fn l_List_forA(
    mut v_m_908_: *mut crate::leanh::LeanObject,
    mut v_inst_909_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_910_: *mut crate::leanh::LeanObject,
    mut v_as_911_: *mut crate::leanh::LeanObject,
    mut v_f_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_List_forA___redArg(v_inst_909_, v_as_911_, v_f_912_);
    return v___x_913_;
}
pub unsafe fn l_List_zipWithM_loop___redArg(
    mut v_inst_914_: *mut crate::leanh::LeanObject,
    mut v_f_915_: *mut crate::leanh::LeanObject,
    mut v_x_916_: *mut crate::leanh::LeanObject,
    mut v_x_917_: *mut crate::leanh::LeanObject,
    mut v_x_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_919_ = crate::leanh::lean_ctor_get(v_inst_914_, 0);
                v_toBind_920_ = crate::leanh::lean_ctor_get(v_inst_914_, 1);
                crate::leanh::lean_inc(v_toBind_920_);
                v_toPure_921_ = crate::leanh::lean_ctor_get(v_toApplicative_919_, 1);
                if crate::leanh::lean_obj_tag(v_x_916_) == 1 {
                    if crate::leanh::lean_obj_tag(v_x_917_) == 1 {
                        v_head_926_ = crate::leanh::lean_ctor_get(v_x_916_, 0);
                        crate::leanh::lean_inc(v_head_926_);
                        v_tail_927_ = crate::leanh::lean_ctor_get(v_x_916_, 1);
                        crate::leanh::lean_inc(v_tail_927_);
                        crate::leanh::lean_dec_ref_known(v_x_916_, 2);
                        v_head_928_ = crate::leanh::lean_ctor_get(v_x_917_, 0);
                        crate::leanh::lean_inc(v_head_928_);
                        v_tail_929_ = crate::leanh::lean_ctor_get(v_x_917_, 1);
                        crate::leanh::lean_inc(v_tail_929_);
                        crate::leanh::lean_dec_ref_known(v_x_917_, 2);
                        crate::leanh::lean_inc(v_f_915_);
                        v___f_930_ = crate::leanh::lean_alloc_closure(
                            l_List_zipWithM_loop___redArg___lam__0 as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_930_, 0, v_x_918_);
                        crate::leanh::lean_closure_set(v___f_930_, 1, v_inst_914_);
                        crate::leanh::lean_closure_set(v___f_930_, 2, v_f_915_);
                        crate::leanh::lean_closure_set(v___f_930_, 3, v_tail_927_);
                        crate::leanh::lean_closure_set(v___f_930_, 4, v_tail_929_);
                        v___x_931_ = crate::leanh::lean_apply_2(v_f_915_, v_head_926_, v_head_928_);
                        v___x_932_ = crate::leanh::lean_apply_4(
                            v_toBind_920_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_931_,
                            v___f_930_,
                        );
                        return v___x_932_;
                    } else {
                        crate::leanh::lean_inc(v_toPure_921_);
                        crate::leanh::lean_dec_ref_known(v_x_916_, 2);
                        crate::leanh::lean_dec(v_toBind_920_);
                        crate::leanh::lean_dec(v_x_917_);
                        crate::leanh::lean_dec(v_f_915_);
                        crate::leanh::lean_dec_ref(v_inst_914_);
                        v_acc_923_ = v_x_918_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_toPure_921_);
                    crate::leanh::lean_dec(v_toBind_920_);
                    crate::leanh::lean_dec(v_x_917_);
                    crate::leanh::lean_dec(v_x_916_);
                    crate::leanh::lean_dec(v_f_915_);
                    crate::leanh::lean_dec_ref(v_inst_914_);
                    v_acc_923_ = v_x_918_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_924_ = lean_array_to_list(v_acc_923_);
                v___x_925_ = crate::leanh::lean_apply_2(
                    v_toPure_921_,
                    crate::leanh::lean_box(0),
                    v___x_924_,
                );
                return v___x_925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithM_loop___redArg___lam__0(
    mut v_x_933_: *mut crate::leanh::LeanObject,
    mut v_inst_934_: *mut crate::leanh::LeanObject,
    mut v_f_935_: *mut crate::leanh::LeanObject,
    mut v_tail_936_: *mut crate::leanh::LeanObject,
    mut v_tail_937_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = lean_array_push(v_x_933_, v_____do__lift_938_);
    v___x_940_ =
        l_List_zipWithM_loop___redArg(v_inst_934_, v_f_935_, v_tail_936_, v_tail_937_, v___x_939_);
    return v___x_940_;
}
pub unsafe fn l_List_zipWithM_loop(
    mut v_m_941_: *mut crate::leanh::LeanObject,
    mut v_inst_942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_943_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_944_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_945_: *mut crate::leanh::LeanObject,
    mut v_f_946_: *mut crate::leanh::LeanObject,
    mut v_x_947_: *mut crate::leanh::LeanObject,
    mut v_x_948_: *mut crate::leanh::LeanObject,
    mut v_x_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_950_ = l_List_zipWithM_loop___redArg(v_inst_942_, v_f_946_, v_x_947_, v_x_948_, v_x_949_);
    return v___x_950_;
}
pub unsafe fn l_List_zipWithM___redArg(
    mut v_inst_953_: *mut crate::leanh::LeanObject,
    mut v_f_954_: *mut crate::leanh::LeanObject,
    mut v_as_955_: *mut crate::leanh::LeanObject,
    mut v_bs_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = l_List_zipWithM___redArg___closed__0;
    v___x_958_ =
        l_List_zipWithM_loop___redArg(v_inst_953_, v_f_954_, v_as_955_, v_bs_956_, v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_List_zipWithM(
    mut v_m_959_: *mut crate::leanh::LeanObject,
    mut v_inst_960_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_963_: *mut crate::leanh::LeanObject,
    mut v_f_964_: *mut crate::leanh::LeanObject,
    mut v_as_965_: *mut crate::leanh::LeanObject,
    mut v_bs_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_List_zipWithM___redArg___closed__0;
    v___x_968_ =
        l_List_zipWithM_loop___redArg(v_inst_960_, v_f_964_, v_as_965_, v_bs_966_, v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_List_filterAuxM___redArg___lam__0___boxed(
    mut v_inst_969_: *mut crate::leanh::LeanObject,
    mut v_f_970_: *mut crate::leanh::LeanObject,
    mut v_tail_971_: *mut crate::leanh::LeanObject,
    mut v_x_972_: *mut crate::leanh::LeanObject,
    mut v_head_973_: *mut crate::leanh::LeanObject,
    mut v_b_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_975_: u8 = 0;
    let mut v_res_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_975_ = (crate::leanh::lean_unbox(v_b_974_) as u8);
    v_res_976_ = l_List_filterAuxM___redArg___lam__0(
        v_inst_969_,
        v_f_970_,
        v_tail_971_,
        v_x_972_,
        v_head_973_,
        v_b_boxed_975_,
    );
    return v_res_976_;
}
pub unsafe fn l_List_filterAuxM___redArg(
    mut v_inst_977_: *mut crate::leanh::LeanObject,
    mut v_f_978_: *mut crate::leanh::LeanObject,
    mut v_x_979_: *mut crate::leanh::LeanObject,
    mut v_x_980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_979_) == 0 {
        let mut v_toApplicative_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_981_ = crate::leanh::lean_ctor_get(v_inst_977_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_981_);
        crate::leanh::lean_dec(v_f_978_);
        crate::leanh::lean_dec_ref(v_inst_977_);
        v_toPure_982_ = crate::leanh::lean_ctor_get(v_toApplicative_981_, 1);
        crate::leanh::lean_inc(v_toPure_982_);
        crate::leanh::lean_dec_ref(v_toApplicative_981_);
        v___x_983_ = crate::leanh::lean_apply_2(v_toPure_982_, crate::leanh::lean_box(0), v_x_980_);
        return v___x_983_;
    } else {
        let mut v_toBind_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_984_ = crate::leanh::lean_ctor_get(v_inst_977_, 1);
        crate::leanh::lean_inc(v_toBind_984_);
        v_head_985_ = crate::leanh::lean_ctor_get(v_x_979_, 0);
        crate::leanh::lean_inc_n(v_head_985_, 2);
        v_tail_986_ = crate::leanh::lean_ctor_get(v_x_979_, 1);
        crate::leanh::lean_inc(v_tail_986_);
        crate::leanh::lean_dec_ref_known(v_x_979_, 2);
        crate::leanh::lean_inc(v_f_978_);
        v___f_987_ = crate::leanh::lean_alloc_closure(
            l_List_filterAuxM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_987_, 0, v_inst_977_);
        crate::leanh::lean_closure_set(v___f_987_, 1, v_f_978_);
        crate::leanh::lean_closure_set(v___f_987_, 2, v_tail_986_);
        crate::leanh::lean_closure_set(v___f_987_, 3, v_x_980_);
        crate::leanh::lean_closure_set(v___f_987_, 4, v_head_985_);
        v___x_988_ = crate::leanh::lean_apply_1(v_f_978_, v_head_985_);
        v___x_989_ = crate::leanh::lean_apply_4(
            v_toBind_984_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_988_,
            v___f_987_,
        );
        return v___x_989_;
    }
}
pub unsafe fn l_List_filterAuxM___redArg___lam__0(
    mut v_inst_990_: *mut crate::leanh::LeanObject,
    mut v_f_991_: *mut crate::leanh::LeanObject,
    mut v_tail_992_: *mut crate::leanh::LeanObject,
    mut v_x_993_: *mut crate::leanh::LeanObject,
    mut v_head_994_: *mut crate::leanh::LeanObject,
    mut v_b_995_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_b_995_ == 0 {
        let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_head_994_);
        v___x_996_ = l_List_filterAuxM___redArg(v_inst_990_, v_f_991_, v_tail_992_, v_x_993_);
        return v___x_996_;
    } else {
        let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_997_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_997_, 0, v_head_994_);
        crate::leanh::lean_ctor_set(v___x_997_, 1, v_x_993_);
        v___x_998_ = l_List_filterAuxM___redArg(v_inst_990_, v_f_991_, v_tail_992_, v___x_997_);
        return v___x_998_;
    }
}
pub unsafe fn l_List_filterAuxM(
    mut v_m_999_: *mut crate::leanh::LeanObject,
    mut v_inst_1000_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1001_: *mut crate::leanh::LeanObject,
    mut v_f_1002_: *mut crate::leanh::LeanObject,
    mut v_x_1003_: *mut crate::leanh::LeanObject,
    mut v_x_1004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = l_List_filterAuxM___redArg(v_inst_1000_, v_f_1002_, v_x_1003_, v_x_1004_);
    return v___x_1005_;
}
pub unsafe fn l_List_filterM___redArg___lam__0(
    mut v_toPure_1006_: *mut crate::leanh::LeanObject,
    mut v_as_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = l_List_reverse___redArg(v_as_1007_);
    v___x_1009_ =
        crate::leanh::lean_apply_2(v_toPure_1006_, crate::leanh::lean_box(0), v___x_1008_);
    return v___x_1009_;
}
pub unsafe fn l_List_filterM___redArg(
    mut v_inst_1010_: *mut crate::leanh::LeanObject,
    mut v_p_1011_: *mut crate::leanh::LeanObject,
    mut v_as_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1013_ = crate::leanh::lean_ctor_get(v_inst_1010_, 0);
    v_toBind_1014_ = crate::leanh::lean_ctor_get(v_inst_1010_, 1);
    crate::leanh::lean_inc(v_toBind_1014_);
    v_toPure_1015_ = crate::leanh::lean_ctor_get(v_toApplicative_1013_, 1);
    crate::leanh::lean_inc(v_toPure_1015_);
    v___x_1016_ = crate::leanh::lean_box(0);
    v___x_1017_ = l_List_filterAuxM___redArg(v_inst_1010_, v_p_1011_, v_as_1012_, v___x_1016_);
    v___f_1018_ = crate::leanh::lean_alloc_closure(
        l_List_filterM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1018_, 0, v_toPure_1015_);
    v___x_1019_ = crate::leanh::lean_apply_4(
        v_toBind_1014_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1017_,
        v___f_1018_,
    );
    return v___x_1019_;
}
pub unsafe fn l_List_filterM(
    mut v_m_1020_: *mut crate::leanh::LeanObject,
    mut v_inst_1021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1022_: *mut crate::leanh::LeanObject,
    mut v_p_1023_: *mut crate::leanh::LeanObject,
    mut v_as_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1025_ = crate::leanh::lean_ctor_get(v_inst_1021_, 0);
    v_toBind_1026_ = crate::leanh::lean_ctor_get(v_inst_1021_, 1);
    crate::leanh::lean_inc(v_toBind_1026_);
    v_toPure_1027_ = crate::leanh::lean_ctor_get(v_toApplicative_1025_, 1);
    crate::leanh::lean_inc(v_toPure_1027_);
    v___x_1028_ = crate::leanh::lean_box(0);
    v___x_1029_ = l_List_filterAuxM___redArg(v_inst_1021_, v_p_1023_, v_as_1024_, v___x_1028_);
    v___f_1030_ = crate::leanh::lean_alloc_closure(
        l_List_filterM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1030_, 0, v_toPure_1027_);
    v___x_1031_ = crate::leanh::lean_apply_4(
        v_toBind_1026_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1029_,
        v___f_1030_,
    );
    return v___x_1031_;
}
pub unsafe fn l_List_filterRevM___redArg(
    mut v_inst_1032_: *mut crate::leanh::LeanObject,
    mut v_p_1033_: *mut crate::leanh::LeanObject,
    mut v_as_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = l_List_reverse___redArg(v_as_1034_);
    v___x_1036_ = crate::leanh::lean_box(0);
    v___x_1037_ = l_List_filterAuxM___redArg(v_inst_1032_, v_p_1033_, v___x_1035_, v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_List_filterRevM(
    mut v_m_1038_: *mut crate::leanh::LeanObject,
    mut v_inst_1039_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1040_: *mut crate::leanh::LeanObject,
    mut v_p_1041_: *mut crate::leanh::LeanObject,
    mut v_as_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_List_reverse___redArg(v_as_1042_);
    v___x_1044_ = crate::leanh::lean_box(0);
    v___x_1045_ = l_List_filterAuxM___redArg(v_inst_1039_, v_p_1041_, v___x_1043_, v___x_1044_);
    return v___x_1045_;
}
pub unsafe fn l_List_filterMapM_loop___redArg___lam__0___boxed(
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_f_1047_: *mut crate::leanh::LeanObject,
    mut v_tail_1048_: *mut crate::leanh::LeanObject,
    mut v_x_1049_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_List_filterMapM_loop___redArg___lam__0(
        v_inst_1046_,
        v_f_1047_,
        v_tail_1048_,
        v_x_1049_,
        v_____do__lift_1050_,
    );
    crate::leanh::lean_dec(v_____do__lift_1050_);
    return v_res_1051_;
}
pub unsafe fn l_List_filterMapM_loop___redArg(
    mut v_inst_1052_: *mut crate::leanh::LeanObject,
    mut v_f_1053_: *mut crate::leanh::LeanObject,
    mut v_x_1054_: *mut crate::leanh::LeanObject,
    mut v_x_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1054_) == 0 {
        let mut v_toApplicative_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1056_ = crate::leanh::lean_ctor_get(v_inst_1052_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1056_);
        crate::leanh::lean_dec(v_f_1053_);
        crate::leanh::lean_dec_ref(v_inst_1052_);
        v_toPure_1057_ = crate::leanh::lean_ctor_get(v_toApplicative_1056_, 1);
        crate::leanh::lean_inc(v_toPure_1057_);
        crate::leanh::lean_dec_ref(v_toApplicative_1056_);
        v___x_1058_ = l_List_reverse___redArg(v_x_1055_);
        v___x_1059_ =
            crate::leanh::lean_apply_2(v_toPure_1057_, crate::leanh::lean_box(0), v___x_1058_);
        return v___x_1059_;
    } else {
        let mut v_toBind_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1060_ = crate::leanh::lean_ctor_get(v_inst_1052_, 1);
        crate::leanh::lean_inc(v_toBind_1060_);
        v_head_1061_ = crate::leanh::lean_ctor_get(v_x_1054_, 0);
        crate::leanh::lean_inc(v_head_1061_);
        v_tail_1062_ = crate::leanh::lean_ctor_get(v_x_1054_, 1);
        crate::leanh::lean_inc(v_tail_1062_);
        crate::leanh::lean_dec_ref_known(v_x_1054_, 2);
        crate::leanh::lean_inc(v_f_1053_);
        v___f_1063_ = crate::leanh::lean_alloc_closure(
            l_List_filterMapM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1063_, 0, v_inst_1052_);
        crate::leanh::lean_closure_set(v___f_1063_, 1, v_f_1053_);
        crate::leanh::lean_closure_set(v___f_1063_, 2, v_tail_1062_);
        crate::leanh::lean_closure_set(v___f_1063_, 3, v_x_1055_);
        v___x_1064_ = crate::leanh::lean_apply_1(v_f_1053_, v_head_1061_);
        v___x_1065_ = crate::leanh::lean_apply_4(
            v_toBind_1060_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1064_,
            v___f_1063_,
        );
        return v___x_1065_;
    }
}
pub unsafe fn l_List_filterMapM_loop___redArg___lam__0(
    mut v_inst_1066_: *mut crate::leanh::LeanObject,
    mut v_f_1067_: *mut crate::leanh::LeanObject,
    mut v_tail_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1070_) == 0 {
        let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1071_ =
            l_List_filterMapM_loop___redArg(v_inst_1066_, v_f_1067_, v_tail_1068_, v_x_1069_);
        return v___x_1071_;
    } else {
        let mut v_val_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1072_ = crate::leanh::lean_ctor_get(v_____do__lift_1070_, 0);
        crate::leanh::lean_inc(v_val_1072_);
        v___x_1073_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1073_, 0, v_val_1072_);
        crate::leanh::lean_ctor_set(v___x_1073_, 1, v_x_1069_);
        v___x_1074_ =
            l_List_filterMapM_loop___redArg(v_inst_1066_, v_f_1067_, v_tail_1068_, v___x_1073_);
        return v___x_1074_;
    }
}
pub unsafe fn l_List_filterMapM_loop(
    mut v_m_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1077_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1078_: *mut crate::leanh::LeanObject,
    mut v_f_1079_: *mut crate::leanh::LeanObject,
    mut v_x_1080_: *mut crate::leanh::LeanObject,
    mut v_x_1081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_List_filterMapM_loop___redArg(v_inst_1076_, v_f_1079_, v_x_1080_, v_x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_List_filterMapM___redArg(
    mut v_inst_1083_: *mut crate::leanh::LeanObject,
    mut v_f_1084_: *mut crate::leanh::LeanObject,
    mut v_as_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = crate::leanh::lean_box(0);
    v___x_1087_ = l_List_filterMapM_loop___redArg(v_inst_1083_, v_f_1084_, v_as_1085_, v___x_1086_);
    return v___x_1087_;
}
pub unsafe fn l_List_filterMapM(
    mut v_m_1088_: *mut crate::leanh::LeanObject,
    mut v_inst_1089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1090_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1091_: *mut crate::leanh::LeanObject,
    mut v_f_1092_: *mut crate::leanh::LeanObject,
    mut v_as_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = crate::leanh::lean_box(0);
    v___x_1095_ = l_List_filterMapM_loop___redArg(v_inst_1089_, v_f_1092_, v_as_1093_, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_List_foldlM___redArg(
    mut v_inst_1096_: *mut crate::leanh::LeanObject,
    mut v_x_1097_: *mut crate::leanh::LeanObject,
    mut v_x_1098_: *mut crate::leanh::LeanObject,
    mut v_x_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1099_) == 0 {
        let mut v_toApplicative_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1100_ = crate::leanh::lean_ctor_get(v_inst_1096_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1100_);
        crate::leanh::lean_dec(v_x_1097_);
        crate::leanh::lean_dec_ref(v_inst_1096_);
        v_toPure_1101_ = crate::leanh::lean_ctor_get(v_toApplicative_1100_, 1);
        crate::leanh::lean_inc(v_toPure_1101_);
        crate::leanh::lean_dec_ref(v_toApplicative_1100_);
        v___x_1102_ =
            crate::leanh::lean_apply_2(v_toPure_1101_, crate::leanh::lean_box(0), v_x_1098_);
        return v___x_1102_;
    } else {
        let mut v_toBind_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1103_ = crate::leanh::lean_ctor_get(v_inst_1096_, 1);
        crate::leanh::lean_inc(v_toBind_1103_);
        v_head_1104_ = crate::leanh::lean_ctor_get(v_x_1099_, 0);
        crate::leanh::lean_inc(v_head_1104_);
        v_tail_1105_ = crate::leanh::lean_ctor_get(v_x_1099_, 1);
        crate::leanh::lean_inc(v_tail_1105_);
        crate::leanh::lean_dec_ref_known(v_x_1099_, 2);
        crate::leanh::lean_inc(v_x_1097_);
        v___f_1106_ = crate::leanh::lean_alloc_closure(
            l_List_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1106_, 0, v_inst_1096_);
        crate::leanh::lean_closure_set(v___f_1106_, 1, v_x_1097_);
        crate::leanh::lean_closure_set(v___f_1106_, 2, v_tail_1105_);
        v___x_1107_ = crate::leanh::lean_apply_2(v_x_1097_, v_x_1098_, v_head_1104_);
        v___x_1108_ = crate::leanh::lean_apply_4(
            v_toBind_1103_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1107_,
            v___f_1106_,
        );
        return v___x_1108_;
    }
}
pub unsafe fn l_List_foldlM___redArg___lam__0(
    mut v_inst_1109_: *mut crate::leanh::LeanObject,
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_tail_1111_: *mut crate::leanh::LeanObject,
    mut v_s_x27_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = l_List_foldlM___redArg(v_inst_1109_, v_x_1110_, v_s_x27_1112_, v_tail_1111_);
    return v___x_1113_;
}
pub unsafe fn l_List_foldlM(
    mut v_m_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_s_1116_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
    mut v_x_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_List_foldlM___redArg(v_inst_1115_, v_x_1118_, v_x_1119_, v_x_1120_);
    return v___x_1121_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter___redArg(
    mut v_x_1122_: *mut crate::leanh::LeanObject,
    mut v_x_1123_: *mut crate::leanh::LeanObject,
    mut v_x_1124_: *mut crate::leanh::LeanObject,
    mut v_h__1_1125_: *mut crate::leanh::LeanObject,
    mut v_h__2_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1124_) == 0 {
        let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1126_);
        v___x_1127_ = crate::leanh::lean_apply_2(v_h__1_1125_, v_x_1122_, v_x_1123_);
        return v___x_1127_;
    } else {
        let mut v_head_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1125_);
        v_head_1128_ = crate::leanh::lean_ctor_get(v_x_1124_, 0);
        crate::leanh::lean_inc(v_head_1128_);
        v_tail_1129_ = crate::leanh::lean_ctor_get(v_x_1124_, 1);
        crate::leanh::lean_inc(v_tail_1129_);
        crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
        v___x_1130_ = crate::leanh::lean_apply_4(
            v_h__2_1126_,
            v_x_1122_,
            v_x_1123_,
            v_head_1128_,
            v_tail_1129_,
        );
        return v___x_1130_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter(
    mut v_m_1131_: *mut crate::leanh::LeanObject,
    mut v_s_1132_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1133_: *mut crate::leanh::LeanObject,
    mut v_motive_1134_: *mut crate::leanh::LeanObject,
    mut v_x_1135_: *mut crate::leanh::LeanObject,
    mut v_x_1136_: *mut crate::leanh::LeanObject,
    mut v_x_1137_: *mut crate::leanh::LeanObject,
    mut v_h__1_1138_: *mut crate::leanh::LeanObject,
    mut v_h__2_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1137_) == 0 {
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1139_);
        v___x_1140_ = crate::leanh::lean_apply_2(v_h__1_1138_, v_x_1135_, v_x_1136_);
        return v___x_1140_;
    } else {
        let mut v_head_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1138_);
        v_head_1141_ = crate::leanh::lean_ctor_get(v_x_1137_, 0);
        crate::leanh::lean_inc(v_head_1141_);
        v_tail_1142_ = crate::leanh::lean_ctor_get(v_x_1137_, 1);
        crate::leanh::lean_inc(v_tail_1142_);
        crate::leanh::lean_dec_ref_known(v_x_1137_, 2);
        v___x_1143_ = crate::leanh::lean_apply_4(
            v_h__2_1139_,
            v_x_1135_,
            v_x_1136_,
            v_head_1141_,
            v_tail_1142_,
        );
        return v___x_1143_;
    }
}
pub unsafe fn l_List_foldrM___redArg___lam__0(
    mut v_f_1144_: *mut crate::leanh::LeanObject,
    mut v_s_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = crate::leanh::lean_apply_2(v_f_1144_, v_a_1146_, v_s_1145_);
    return v___x_1147_;
}
pub unsafe fn l_List_foldrM___redArg(
    mut v_inst_1148_: *mut crate::leanh::LeanObject,
    mut v_f_1149_: *mut crate::leanh::LeanObject,
    mut v_init_1150_: *mut crate::leanh::LeanObject,
    mut v_l_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1152_ = crate::leanh::lean_alloc_closure(
        l_List_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1152_, 0, v_f_1149_);
    v___x_1153_ = l_List_reverse___redArg(v_l_1151_);
    v___x_1154_ = l_List_foldlM___redArg(v_inst_1148_, v___f_1152_, v_init_1150_, v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn l_List_foldrM(
    mut v_m_1155_: *mut crate::leanh::LeanObject,
    mut v_inst_1156_: *mut crate::leanh::LeanObject,
    mut v_s_1157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1158_: *mut crate::leanh::LeanObject,
    mut v_f_1159_: *mut crate::leanh::LeanObject,
    mut v_init_1160_: *mut crate::leanh::LeanObject,
    mut v_l_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1162_ = crate::leanh::lean_alloc_closure(
        l_List_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1162_, 0, v_f_1159_);
    v___x_1163_ = l_List_reverse___redArg(v_l_1161_);
    v___x_1164_ = l_List_foldlM___redArg(v_inst_1156_, v___f_1162_, v_init_1160_, v___x_1163_);
    return v___x_1164_;
}
pub unsafe fn l_List_firstM___redArg(
    mut v_inst_1165_: *mut crate::leanh::LeanObject,
    mut v_f_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1167_) == 0 {
        let mut v_failure_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1166_);
        v_failure_1168_ = crate::leanh::lean_ctor_get(v_inst_1165_, 1);
        crate::leanh::lean_inc(v_failure_1168_);
        crate::leanh::lean_dec_ref(v_inst_1165_);
        v___x_1169_ = crate::leanh::lean_apply_1(v_failure_1168_, crate::leanh::lean_box(0));
        return v___x_1169_;
    } else {
        let mut v_head_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_orElse_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1170_ = crate::leanh::lean_ctor_get(v_x_1167_, 0);
        crate::leanh::lean_inc(v_head_1170_);
        v_tail_1171_ = crate::leanh::lean_ctor_get(v_x_1167_, 1);
        crate::leanh::lean_inc(v_tail_1171_);
        crate::leanh::lean_dec_ref_known(v_x_1167_, 2);
        v_orElse_1172_ = crate::leanh::lean_ctor_get(v_inst_1165_, 2);
        crate::leanh::lean_inc(v_orElse_1172_);
        crate::leanh::lean_inc(v_f_1166_);
        v___f_1173_ = crate::leanh::lean_alloc_closure(
            l_List_firstM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1173_, 0, v_inst_1165_);
        crate::leanh::lean_closure_set(v___f_1173_, 1, v_f_1166_);
        crate::leanh::lean_closure_set(v___f_1173_, 2, v_tail_1171_);
        v___x_1174_ = crate::leanh::lean_apply_1(v_f_1166_, v_head_1170_);
        v___x_1175_ = crate::leanh::lean_apply_3(
            v_orElse_1172_,
            crate::leanh::lean_box(0),
            v___x_1174_,
            v___f_1173_,
        );
        return v___x_1175_;
    }
}
pub unsafe fn l_List_firstM___redArg___lam__0(
    mut v_inst_1176_: *mut crate::leanh::LeanObject,
    mut v_f_1177_: *mut crate::leanh::LeanObject,
    mut v_tail_1178_: *mut crate::leanh::LeanObject,
    mut v_x_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_List_firstM___redArg(v_inst_1176_, v_f_1177_, v_tail_1178_);
    return v___x_1180_;
}
pub unsafe fn l_List_firstM(
    mut v_m_1181_: *mut crate::leanh::LeanObject,
    mut v_inst_1182_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1183_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1184_: *mut crate::leanh::LeanObject,
    mut v_f_1185_: *mut crate::leanh::LeanObject,
    mut v_x_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_List_firstM___redArg(v_inst_1182_, v_f_1185_, v_x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_List_anyM___redArg___lam__0___boxed(
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
    mut v_p_1189_: *mut crate::leanh::LeanObject,
    mut v_tail_1190_: *mut crate::leanh::LeanObject,
    mut v_toPure_1191_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_73__boxed_1193_: u8 = 0;
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_73__boxed_1193_ = (crate::leanh::lean_unbox(v_____do__lift_1192_) as u8);
    v_res_1194_ = l_List_anyM___redArg___lam__0(
        v_inst_1188_,
        v_p_1189_,
        v_tail_1190_,
        v_toPure_1191_,
        v_____do__lift_73__boxed_1193_,
    );
    return v_res_1194_;
}
pub unsafe fn l_List_anyM___redArg(
    mut v_inst_1195_: *mut crate::leanh::LeanObject,
    mut v_p_1196_: *mut crate::leanh::LeanObject,
    mut v_x_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1197_) == 0 {
        let mut v_toApplicative_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: u8 = 0;
        let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1198_ = crate::leanh::lean_ctor_get(v_inst_1195_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1198_);
        crate::leanh::lean_dec(v_p_1196_);
        crate::leanh::lean_dec_ref(v_inst_1195_);
        v_toPure_1199_ = crate::leanh::lean_ctor_get(v_toApplicative_1198_, 1);
        crate::leanh::lean_inc(v_toPure_1199_);
        crate::leanh::lean_dec_ref(v_toApplicative_1198_);
        v___x_1200_ = 0;
        v___x_1201_ = crate::leanh::lean_box((v___x_1200_) as usize);
        v___x_1202_ =
            crate::leanh::lean_apply_2(v_toPure_1199_, crate::leanh::lean_box(0), v___x_1201_);
        return v___x_1202_;
    } else {
        let mut v_toApplicative_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1203_ = crate::leanh::lean_ctor_get(v_inst_1195_, 0);
        v_toBind_1204_ = crate::leanh::lean_ctor_get(v_inst_1195_, 1);
        crate::leanh::lean_inc(v_toBind_1204_);
        v_toPure_1205_ = crate::leanh::lean_ctor_get(v_toApplicative_1203_, 1);
        crate::leanh::lean_inc(v_toPure_1205_);
        v_head_1206_ = crate::leanh::lean_ctor_get(v_x_1197_, 0);
        crate::leanh::lean_inc(v_head_1206_);
        v_tail_1207_ = crate::leanh::lean_ctor_get(v_x_1197_, 1);
        crate::leanh::lean_inc(v_tail_1207_);
        crate::leanh::lean_dec_ref_known(v_x_1197_, 2);
        crate::leanh::lean_inc(v_p_1196_);
        v___f_1208_ = crate::leanh::lean_alloc_closure(
            l_List_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1208_, 0, v_inst_1195_);
        crate::leanh::lean_closure_set(v___f_1208_, 1, v_p_1196_);
        crate::leanh::lean_closure_set(v___f_1208_, 2, v_tail_1207_);
        crate::leanh::lean_closure_set(v___f_1208_, 3, v_toPure_1205_);
        v___x_1209_ = crate::leanh::lean_apply_1(v_p_1196_, v_head_1206_);
        v___x_1210_ = crate::leanh::lean_apply_4(
            v_toBind_1204_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1209_,
            v___f_1208_,
        );
        return v___x_1210_;
    }
}
pub unsafe fn l_List_anyM___redArg___lam__0(
    mut v_inst_1211_: *mut crate::leanh::LeanObject,
    mut v_p_1212_: *mut crate::leanh::LeanObject,
    mut v_tail_1213_: *mut crate::leanh::LeanObject,
    mut v_toPure_1214_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1215_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1215_ == 0 {
        let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1214_);
        v___x_1216_ = l_List_anyM___redArg(v_inst_1211_, v_p_1212_, v_tail_1213_);
        return v___x_1216_;
    } else {
        let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_1213_);
        crate::leanh::lean_dec(v_p_1212_);
        crate::leanh::lean_dec_ref(v_inst_1211_);
        v___x_1217_ = crate::leanh::lean_box((v_____do__lift_1215_) as usize);
        v___x_1218_ =
            crate::leanh::lean_apply_2(v_toPure_1214_, crate::leanh::lean_box(0), v___x_1217_);
        return v___x_1218_;
    }
}
pub unsafe fn l_List_anyM(
    mut v_m_1219_: *mut crate::leanh::LeanObject,
    mut v_inst_1220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1221_: *mut crate::leanh::LeanObject,
    mut v_p_1222_: *mut crate::leanh::LeanObject,
    mut v_x_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_List_anyM___redArg(v_inst_1220_, v_p_1222_, v_x_1223_);
    return v___x_1224_;
}
pub unsafe fn l_List_allM___redArg___lam__0___boxed(
    mut v_toPure_1225_: *mut crate::leanh::LeanObject,
    mut v_inst_1226_: *mut crate::leanh::LeanObject,
    mut v_p_1227_: *mut crate::leanh::LeanObject,
    mut v_tail_1228_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_73__boxed_1230_: u8 = 0;
    let mut v_res_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_73__boxed_1230_ = (crate::leanh::lean_unbox(v_____do__lift_1229_) as u8);
    v_res_1231_ = l_List_allM___redArg___lam__0(
        v_toPure_1225_,
        v_inst_1226_,
        v_p_1227_,
        v_tail_1228_,
        v_____do__lift_73__boxed_1230_,
    );
    return v_res_1231_;
}
pub unsafe fn l_List_allM___redArg(
    mut v_inst_1232_: *mut crate::leanh::LeanObject,
    mut v_p_1233_: *mut crate::leanh::LeanObject,
    mut v_x_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1234_) == 0 {
        let mut v_toApplicative_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: u8 = 0;
        let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1235_ = crate::leanh::lean_ctor_get(v_inst_1232_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1235_);
        crate::leanh::lean_dec(v_p_1233_);
        crate::leanh::lean_dec_ref(v_inst_1232_);
        v_toPure_1236_ = crate::leanh::lean_ctor_get(v_toApplicative_1235_, 1);
        crate::leanh::lean_inc(v_toPure_1236_);
        crate::leanh::lean_dec_ref(v_toApplicative_1235_);
        v___x_1237_ = 1;
        v___x_1238_ = crate::leanh::lean_box((v___x_1237_) as usize);
        v___x_1239_ =
            crate::leanh::lean_apply_2(v_toPure_1236_, crate::leanh::lean_box(0), v___x_1238_);
        return v___x_1239_;
    } else {
        let mut v_toApplicative_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1240_ = crate::leanh::lean_ctor_get(v_inst_1232_, 0);
        v_toBind_1241_ = crate::leanh::lean_ctor_get(v_inst_1232_, 1);
        crate::leanh::lean_inc(v_toBind_1241_);
        v_toPure_1242_ = crate::leanh::lean_ctor_get(v_toApplicative_1240_, 1);
        crate::leanh::lean_inc(v_toPure_1242_);
        v_head_1243_ = crate::leanh::lean_ctor_get(v_x_1234_, 0);
        crate::leanh::lean_inc(v_head_1243_);
        v_tail_1244_ = crate::leanh::lean_ctor_get(v_x_1234_, 1);
        crate::leanh::lean_inc(v_tail_1244_);
        crate::leanh::lean_dec_ref_known(v_x_1234_, 2);
        crate::leanh::lean_inc(v_p_1233_);
        v___f_1245_ = crate::leanh::lean_alloc_closure(
            l_List_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1245_, 0, v_toPure_1242_);
        crate::leanh::lean_closure_set(v___f_1245_, 1, v_inst_1232_);
        crate::leanh::lean_closure_set(v___f_1245_, 2, v_p_1233_);
        crate::leanh::lean_closure_set(v___f_1245_, 3, v_tail_1244_);
        v___x_1246_ = crate::leanh::lean_apply_1(v_p_1233_, v_head_1243_);
        v___x_1247_ = crate::leanh::lean_apply_4(
            v_toBind_1241_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1246_,
            v___f_1245_,
        );
        return v___x_1247_;
    }
}
pub unsafe fn l_List_allM___redArg___lam__0(
    mut v_toPure_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_p_1250_: *mut crate::leanh::LeanObject,
    mut v_tail_1251_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1252_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1252_ == 0 {
        let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_1251_);
        crate::leanh::lean_dec(v_p_1250_);
        crate::leanh::lean_dec_ref(v_inst_1249_);
        v___x_1253_ = crate::leanh::lean_box((v_____do__lift_1252_) as usize);
        v___x_1254_ =
            crate::leanh::lean_apply_2(v_toPure_1248_, crate::leanh::lean_box(0), v___x_1253_);
        return v___x_1254_;
    } else {
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1248_);
        v___x_1255_ = l_List_allM___redArg(v_inst_1249_, v_p_1250_, v_tail_1251_);
        return v___x_1255_;
    }
}
pub unsafe fn l_List_allM(
    mut v_m_1256_: *mut crate::leanh::LeanObject,
    mut v_inst_1257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1258_: *mut crate::leanh::LeanObject,
    mut v_p_1259_: *mut crate::leanh::LeanObject,
    mut v_x_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_List_allM___redArg(v_inst_1257_, v_p_1259_, v_x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_List_findM_x3f___redArg___lam__0___boxed(
    mut v_inst_1262_: *mut crate::leanh::LeanObject,
    mut v_p_1263_: *mut crate::leanh::LeanObject,
    mut v_tail_1264_: *mut crate::leanh::LeanObject,
    mut v_head_1265_: *mut crate::leanh::LeanObject,
    mut v_toPure_1266_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_76__boxed_1268_: u8 = 0;
    let mut v_res_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_76__boxed_1268_ = (crate::leanh::lean_unbox(v_____do__lift_1267_) as u8);
    v_res_1269_ = l_List_findM_x3f___redArg___lam__0(
        v_inst_1262_,
        v_p_1263_,
        v_tail_1264_,
        v_head_1265_,
        v_toPure_1266_,
        v_____do__lift_76__boxed_1268_,
    );
    return v_res_1269_;
}
pub unsafe fn l_List_findM_x3f___redArg(
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
    mut v_p_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1272_) == 0 {
        let mut v_toApplicative_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1273_ = crate::leanh::lean_ctor_get(v_inst_1270_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1273_);
        crate::leanh::lean_dec(v_p_1271_);
        crate::leanh::lean_dec_ref(v_inst_1270_);
        v_toPure_1274_ = crate::leanh::lean_ctor_get(v_toApplicative_1273_, 1);
        crate::leanh::lean_inc(v_toPure_1274_);
        crate::leanh::lean_dec_ref(v_toApplicative_1273_);
        v___x_1275_ = crate::leanh::lean_box(0);
        v___x_1276_ =
            crate::leanh::lean_apply_2(v_toPure_1274_, crate::leanh::lean_box(0), v___x_1275_);
        return v___x_1276_;
    } else {
        let mut v_toApplicative_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1277_ = crate::leanh::lean_ctor_get(v_inst_1270_, 0);
        v_toBind_1278_ = crate::leanh::lean_ctor_get(v_inst_1270_, 1);
        crate::leanh::lean_inc(v_toBind_1278_);
        v_toPure_1279_ = crate::leanh::lean_ctor_get(v_toApplicative_1277_, 1);
        crate::leanh::lean_inc(v_toPure_1279_);
        v_head_1280_ = crate::leanh::lean_ctor_get(v_x_1272_, 0);
        crate::leanh::lean_inc_n(v_head_1280_, 2);
        v_tail_1281_ = crate::leanh::lean_ctor_get(v_x_1272_, 1);
        crate::leanh::lean_inc(v_tail_1281_);
        crate::leanh::lean_dec_ref_known(v_x_1272_, 2);
        crate::leanh::lean_inc(v_p_1271_);
        v___f_1282_ = crate::leanh::lean_alloc_closure(
            l_List_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_1282_, 0, v_inst_1270_);
        crate::leanh::lean_closure_set(v___f_1282_, 1, v_p_1271_);
        crate::leanh::lean_closure_set(v___f_1282_, 2, v_tail_1281_);
        crate::leanh::lean_closure_set(v___f_1282_, 3, v_head_1280_);
        crate::leanh::lean_closure_set(v___f_1282_, 4, v_toPure_1279_);
        v___x_1283_ = crate::leanh::lean_apply_1(v_p_1271_, v_head_1280_);
        v___x_1284_ = crate::leanh::lean_apply_4(
            v_toBind_1278_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1283_,
            v___f_1282_,
        );
        return v___x_1284_;
    }
}
pub unsafe fn l_List_findM_x3f___redArg___lam__0(
    mut v_inst_1285_: *mut crate::leanh::LeanObject,
    mut v_p_1286_: *mut crate::leanh::LeanObject,
    mut v_tail_1287_: *mut crate::leanh::LeanObject,
    mut v_head_1288_: *mut crate::leanh::LeanObject,
    mut v_toPure_1289_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1290_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1290_ == 0 {
        let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1289_);
        crate::leanh::lean_dec(v_head_1288_);
        v___x_1291_ = l_List_findM_x3f___redArg(v_inst_1285_, v_p_1286_, v_tail_1287_);
        return v___x_1291_;
    } else {
        let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_1287_);
        crate::leanh::lean_dec(v_p_1286_);
        crate::leanh::lean_dec_ref(v_inst_1285_);
        v___x_1292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1292_, 0, v_head_1288_);
        v___x_1293_ =
            crate::leanh::lean_apply_2(v_toPure_1289_, crate::leanh::lean_box(0), v___x_1292_);
        return v___x_1293_;
    }
}
pub unsafe fn l_List_findM_x3f(
    mut v_m_1294_: *mut crate::leanh::LeanObject,
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1296_: *mut crate::leanh::LeanObject,
    mut v_p_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_List_findM_x3f___redArg(v_inst_1295_, v_p_1297_, v_x_1298_);
    return v___x_1299_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v_h__1_1301_: *mut crate::leanh::LeanObject,
    mut v_h__2_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1300_) == 0 {
        let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1302_);
        v___x_1303_ = crate::leanh::lean_box(0);
        v___x_1304_ = crate::leanh::lean_apply_1(v_h__1_1301_, v___x_1303_);
        return v___x_1304_;
    } else {
        let mut v_head_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1301_);
        v_head_1305_ = crate::leanh::lean_ctor_get(v_x_1300_, 0);
        crate::leanh::lean_inc(v_head_1305_);
        v_tail_1306_ = crate::leanh::lean_ctor_get(v_x_1300_, 1);
        crate::leanh::lean_inc(v_tail_1306_);
        crate::leanh::lean_dec_ref_known(v_x_1300_, 2);
        v___x_1307_ = crate::leanh::lean_apply_2(v_h__2_1302_, v_head_1305_, v_tail_1306_);
        return v___x_1307_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter(
    mut v_00_u03b1_1308_: *mut crate::leanh::LeanObject,
    mut v_motive_1309_: *mut crate::leanh::LeanObject,
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v_h__1_1311_: *mut crate::leanh::LeanObject,
    mut v_h__2_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1310_) == 0 {
        let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1312_);
        v___x_1313_ = crate::leanh::lean_box(0);
        v___x_1314_ = crate::leanh::lean_apply_1(v_h__1_1311_, v___x_1313_);
        return v___x_1314_;
    } else {
        let mut v_head_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1311_);
        v_head_1315_ = crate::leanh::lean_ctor_get(v_x_1310_, 0);
        crate::leanh::lean_inc(v_head_1315_);
        v_tail_1316_ = crate::leanh::lean_ctor_get(v_x_1310_, 1);
        crate::leanh::lean_inc(v_tail_1316_);
        crate::leanh::lean_dec_ref_known(v_x_1310_, 2);
        v___x_1317_ = crate::leanh::lean_apply_2(v_h__2_1312_, v_head_1315_, v_tail_1316_);
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_1318_: u8,
    mut v_h__1_1319_: *mut crate::leanh::LeanObject,
    mut v_h__2_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1318_ == 0 {
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1319_);
        v___x_1321_ = crate::leanh::lean_box(0);
        v___x_1322_ = crate::leanh::lean_apply_1(v_h__2_1320_, v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1320_);
        v___x_1323_ = crate::leanh::lean_box(0);
        v___x_1324_ = crate::leanh::lean_apply_1(v_h__1_1319_, v___x_1323_);
        return v___x_1324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_1325_: *mut crate::leanh::LeanObject,
    mut v_h__1_1326_: *mut crate::leanh::LeanObject,
    mut v_h__2_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_26__boxed_1328_: u8 = 0;
    let mut v_res_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_1328_ = (crate::leanh::lean_unbox(v_____do__lift_1325_) as u8);
    v_res_1329_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_1328_,
        v_h__1_1326_,
        v_h__2_1327_,
    );
    return v_res_1329_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(
    mut v_motive_1330_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1331_: u8,
    mut v_h__1_1332_: *mut crate::leanh::LeanObject,
    mut v_h__2_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1331_ == 0 {
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1332_);
        v___x_1334_ = crate::leanh::lean_box(0);
        v___x_1335_ = crate::leanh::lean_apply_1(v_h__2_1333_, v___x_1334_);
        return v___x_1335_;
    } else {
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1333_);
        v___x_1336_ = crate::leanh::lean_box(0);
        v___x_1337_ = crate::leanh::lean_apply_1(v_h__1_1332_, v___x_1336_);
        return v___x_1337_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_1338_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1339_: *mut crate::leanh::LeanObject,
    mut v_h__1_1340_: *mut crate::leanh::LeanObject,
    mut v_h__2_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_37__boxed_1342_: u8 = 0;
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_1342_ = (crate::leanh::lean_unbox(v_____do__lift_1339_) as u8);
    v_res_1343_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(
        v_motive_1338_,
        v_____do__lift_37__boxed_1342_,
        v_h__1_1340_,
        v_h__2_1341_,
    );
    return v_res_1343_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(
    mut v_x_1344_: u8,
    mut v_h__1_1345_: *mut crate::leanh::LeanObject,
    mut v_h__2_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1344_ == 0 {
        let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1345_);
        v___x_1347_ = crate::leanh::lean_box(0);
        v___x_1348_ = crate::leanh::lean_apply_1(v_h__2_1346_, v___x_1347_);
        return v___x_1348_;
    } else {
        let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1346_);
        v___x_1349_ = crate::leanh::lean_box(0);
        v___x_1350_ = crate::leanh::lean_apply_1(v_h__1_1345_, v___x_1349_);
        return v___x_1350_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1351_: *mut crate::leanh::LeanObject,
    mut v_h__1_1352_: *mut crate::leanh::LeanObject,
    mut v_h__2_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1354_: u8 = 0;
    let mut v_res_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1354_ = (crate::leanh::lean_unbox(v_x_1351_) as u8);
    v_res_1355_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_1354_,
        v_h__1_1352_,
        v_h__2_1353_,
    );
    return v_res_1355_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(
    mut v_motive_1356_: *mut crate::leanh::LeanObject,
    mut v_x_1357_: u8,
    mut v_h__1_1358_: *mut crate::leanh::LeanObject,
    mut v_h__2_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1357_ == 0 {
        let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1358_);
        v___x_1360_ = crate::leanh::lean_box(0);
        v___x_1361_ = crate::leanh::lean_apply_1(v_h__2_1359_, v___x_1360_);
        return v___x_1361_;
    } else {
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1359_);
        v___x_1362_ = crate::leanh::lean_box(0);
        v___x_1363_ = crate::leanh::lean_apply_1(v_h__1_1358_, v___x_1362_);
        return v___x_1363_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1364_: *mut crate::leanh::LeanObject,
    mut v_x_1365_: *mut crate::leanh::LeanObject,
    mut v_h__1_1366_: *mut crate::leanh::LeanObject,
    mut v_h__2_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1368_ = (crate::leanh::lean_unbox(v_x_1365_) as u8);
    v_res_1369_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(
        v_motive_1364_,
        v_x_37__boxed_1368_,
        v_h__1_1366_,
        v_h__2_1367_,
    );
    return v_res_1369_;
}
pub unsafe fn l_List_findSomeM_x3f___redArg(
    mut v_inst_1370_: *mut crate::leanh::LeanObject,
    mut v_f_1371_: *mut crate::leanh::LeanObject,
    mut v_x_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1372_) == 0 {
        let mut v_toApplicative_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1373_ = crate::leanh::lean_ctor_get(v_inst_1370_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1373_);
        crate::leanh::lean_dec(v_f_1371_);
        crate::leanh::lean_dec_ref(v_inst_1370_);
        v_toPure_1374_ = crate::leanh::lean_ctor_get(v_toApplicative_1373_, 1);
        crate::leanh::lean_inc(v_toPure_1374_);
        crate::leanh::lean_dec_ref(v_toApplicative_1373_);
        v___x_1375_ = crate::leanh::lean_box(0);
        v___x_1376_ =
            crate::leanh::lean_apply_2(v_toPure_1374_, crate::leanh::lean_box(0), v___x_1375_);
        return v___x_1376_;
    } else {
        let mut v_toApplicative_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1377_ = crate::leanh::lean_ctor_get(v_inst_1370_, 0);
        v_toBind_1378_ = crate::leanh::lean_ctor_get(v_inst_1370_, 1);
        crate::leanh::lean_inc(v_toBind_1378_);
        v_toPure_1379_ = crate::leanh::lean_ctor_get(v_toApplicative_1377_, 1);
        crate::leanh::lean_inc(v_toPure_1379_);
        v_head_1380_ = crate::leanh::lean_ctor_get(v_x_1372_, 0);
        crate::leanh::lean_inc(v_head_1380_);
        v_tail_1381_ = crate::leanh::lean_ctor_get(v_x_1372_, 1);
        crate::leanh::lean_inc(v_tail_1381_);
        crate::leanh::lean_dec_ref_known(v_x_1372_, 2);
        crate::leanh::lean_inc(v_f_1371_);
        v___f_1382_ = crate::leanh::lean_alloc_closure(
            l_List_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1382_, 0, v_inst_1370_);
        crate::leanh::lean_closure_set(v___f_1382_, 1, v_f_1371_);
        crate::leanh::lean_closure_set(v___f_1382_, 2, v_tail_1381_);
        crate::leanh::lean_closure_set(v___f_1382_, 3, v_toPure_1379_);
        v___x_1383_ = crate::leanh::lean_apply_1(v_f_1371_, v_head_1380_);
        v___x_1384_ = crate::leanh::lean_apply_4(
            v_toBind_1378_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1383_,
            v___f_1382_,
        );
        return v___x_1384_;
    }
}
pub unsafe fn l_List_findSomeM_x3f___redArg___lam__0(
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
    mut v_f_1386_: *mut crate::leanh::LeanObject,
    mut v_tail_1387_: *mut crate::leanh::LeanObject,
    mut v_toPure_1388_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1389_) == 0 {
        let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1388_);
        v___x_1390_ = l_List_findSomeM_x3f___redArg(v_inst_1385_, v_f_1386_, v_tail_1387_);
        return v___x_1390_;
    } else {
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_1387_);
        crate::leanh::lean_dec(v_f_1386_);
        crate::leanh::lean_dec_ref(v_inst_1385_);
        v___x_1391_ = crate::leanh::lean_apply_2(
            v_toPure_1388_,
            crate::leanh::lean_box(0),
            v_____do__lift_1389_,
        );
        return v___x_1391_;
    }
}
pub unsafe fn l_List_findSomeM_x3f(
    mut v_m_1392_: *mut crate::leanh::LeanObject,
    mut v_inst_1393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1394_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1395_: *mut crate::leanh::LeanObject,
    mut v_f_1396_: *mut crate::leanh::LeanObject,
    mut v_x_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_List_findSomeM_x3f___redArg(v_inst_1393_, v_f_1396_, v_x_1397_);
    return v___x_1398_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_h__1_1400_: *mut crate::leanh::LeanObject,
    mut v_h__2_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1399_) == 0 {
        let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1401_);
        v___x_1402_ = crate::leanh::lean_box(0);
        v___x_1403_ = crate::leanh::lean_apply_1(v_h__1_1400_, v___x_1402_);
        return v___x_1403_;
    } else {
        let mut v_head_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1400_);
        v_head_1404_ = crate::leanh::lean_ctor_get(v_x_1399_, 0);
        crate::leanh::lean_inc(v_head_1404_);
        v_tail_1405_ = crate::leanh::lean_ctor_get(v_x_1399_, 1);
        crate::leanh::lean_inc(v_tail_1405_);
        crate::leanh::lean_dec_ref_known(v_x_1399_, 2);
        v___x_1406_ = crate::leanh::lean_apply_2(v_h__2_1401_, v_head_1404_, v_tail_1405_);
        return v___x_1406_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_1407_: *mut crate::leanh::LeanObject,
    mut v_motive_1408_: *mut crate::leanh::LeanObject,
    mut v_x_1409_: *mut crate::leanh::LeanObject,
    mut v_h__1_1410_: *mut crate::leanh::LeanObject,
    mut v_h__2_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1409_) == 0 {
        let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1411_);
        v___x_1412_ = crate::leanh::lean_box(0);
        v___x_1413_ = crate::leanh::lean_apply_1(v_h__1_1410_, v___x_1412_);
        return v___x_1413_;
    } else {
        let mut v_head_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1410_);
        v_head_1414_ = crate::leanh::lean_ctor_get(v_x_1409_, 0);
        crate::leanh::lean_inc(v_head_1414_);
        v_tail_1415_ = crate::leanh::lean_ctor_get(v_x_1409_, 1);
        crate::leanh::lean_inc(v_tail_1415_);
        crate::leanh::lean_dec_ref_known(v_x_1409_, 2);
        v___x_1416_ = crate::leanh::lean_apply_2(v_h__2_1411_, v_head_1414_, v_tail_1415_);
        return v___x_1416_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_1417_: *mut crate::leanh::LeanObject,
    mut v_h__1_1418_: *mut crate::leanh::LeanObject,
    mut v_h__2_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1417_) == 0 {
        let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1418_);
        v___x_1420_ = crate::leanh::lean_box(0);
        v___x_1421_ = crate::leanh::lean_apply_1(v_h__2_1419_, v___x_1420_);
        return v___x_1421_;
    } else {
        let mut v_val_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1419_);
        v_val_1422_ = crate::leanh::lean_ctor_get(v_____do__lift_1417_, 0);
        crate::leanh::lean_inc(v_val_1422_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1417_, 1);
        v___x_1423_ = crate::leanh::lean_apply_1(v_h__1_1418_, v_val_1422_);
        return v___x_1423_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_1424_: *mut crate::leanh::LeanObject,
    mut v_motive_1425_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1426_: *mut crate::leanh::LeanObject,
    mut v_h__1_1427_: *mut crate::leanh::LeanObject,
    mut v_h__2_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1426_) == 0 {
        let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1427_);
        v___x_1429_ = crate::leanh::lean_box(0);
        v___x_1430_ = crate::leanh::lean_apply_1(v_h__2_1428_, v___x_1429_);
        return v___x_1430_;
    } else {
        let mut v_val_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1428_);
        v_val_1431_ = crate::leanh::lean_ctor_get(v_____do__lift_1426_, 0);
        crate::leanh::lean_inc(v_val_1431_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1426_, 1);
        v___x_1432_ = crate::leanh::lean_apply_1(v_h__1_1427_, v_val_1431_);
        return v___x_1432_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_1433_: *mut crate::leanh::LeanObject,
    mut v_h__1_1434_: *mut crate::leanh::LeanObject,
    mut v_h__2_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1433_) == 0 {
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1435_);
        v___x_1436_ = crate::leanh::lean_box(0);
        v___x_1437_ = crate::leanh::lean_apply_1(v_h__1_1434_, v___x_1436_);
        return v___x_1437_;
    } else {
        let mut v_head_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1434_);
        v_head_1438_ = crate::leanh::lean_ctor_get(v_x_1433_, 0);
        crate::leanh::lean_inc(v_head_1438_);
        v_tail_1439_ = crate::leanh::lean_ctor_get(v_x_1433_, 1);
        crate::leanh::lean_inc(v_tail_1439_);
        crate::leanh::lean_dec_ref_known(v_x_1433_, 2);
        v___x_1440_ = crate::leanh::lean_apply_2(v_h__2_1435_, v_head_1438_, v_tail_1439_);
        return v___x_1440_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_1441_: *mut crate::leanh::LeanObject,
    mut v_motive_1442_: *mut crate::leanh::LeanObject,
    mut v_x_1443_: *mut crate::leanh::LeanObject,
    mut v_h__1_1444_: *mut crate::leanh::LeanObject,
    mut v_h__2_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1443_) == 0 {
        let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1445_);
        v___x_1446_ = crate::leanh::lean_box(0);
        v___x_1447_ = crate::leanh::lean_apply_1(v_h__1_1444_, v___x_1446_);
        return v___x_1447_;
    } else {
        let mut v_head_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1444_);
        v_head_1448_ = crate::leanh::lean_ctor_get(v_x_1443_, 0);
        crate::leanh::lean_inc(v_head_1448_);
        v_tail_1449_ = crate::leanh::lean_ctor_get(v_x_1443_, 1);
        crate::leanh::lean_inc(v_tail_1449_);
        crate::leanh::lean_dec_ref_known(v_x_1443_, 2);
        v___x_1450_ = crate::leanh::lean_apply_2(v_h__2_1445_, v_head_1448_, v_tail_1449_);
        return v___x_1450_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_1451_: *mut crate::leanh::LeanObject,
    mut v_h__1_1452_: *mut crate::leanh::LeanObject,
    mut v_h__2_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1451_) == 0 {
        let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1452_);
        v___x_1454_ = crate::leanh::lean_box(0);
        v___x_1455_ = crate::leanh::lean_apply_1(v_h__2_1453_, v___x_1454_);
        return v___x_1455_;
    } else {
        let mut v_val_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1453_);
        v_val_1456_ = crate::leanh::lean_ctor_get(v_x_1451_, 0);
        crate::leanh::lean_inc(v_val_1456_);
        crate::leanh::lean_dec_ref_known(v_x_1451_, 1);
        v___x_1457_ = crate::leanh::lean_apply_1(v_h__1_1452_, v_val_1456_);
        return v___x_1457_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_1458_: *mut crate::leanh::LeanObject,
    mut v_motive_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_h__1_1461_: *mut crate::leanh::LeanObject,
    mut v_h__2_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1460_) == 0 {
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1461_);
        v___x_1463_ = crate::leanh::lean_box(0);
        v___x_1464_ = crate::leanh::lean_apply_1(v_h__2_1462_, v___x_1463_);
        return v___x_1464_;
    } else {
        let mut v_val_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1462_);
        v_val_1465_ = crate::leanh::lean_ctor_get(v_x_1460_, 0);
        crate::leanh::lean_inc(v_val_1465_);
        crate::leanh::lean_dec_ref_known(v_x_1460_, 1);
        v___x_1466_ = crate::leanh::lean_apply_1(v_h__1_1461_, v_val_1465_);
        return v___x_1466_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___lam__0___boxed(
    mut v_toPure_1467_: *mut crate::leanh::LeanObject,
    mut v_inst_1468_: *mut crate::leanh::LeanObject,
    mut v_f_1469_: *mut crate::leanh::LeanObject,
    mut v_tail_1470_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_List_forIn_x27_loop___redArg___lam__0(
        v_toPure_1467_,
        v_inst_1468_,
        v_f_1469_,
        v_tail_1470_,
        v_____do__lift_1471_,
    );
    crate::leanh::lean_dec(v_tail_1470_);
    return v_res_1472_;
}
pub unsafe fn l_List_forIn_x27_loop___redArg(
    mut v_inst_1473_: *mut crate::leanh::LeanObject,
    mut v_f_1474_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1475_: *mut crate::leanh::LeanObject,
    mut v_b_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_as_x27_1475_) == 0 {
        let mut v_toApplicative_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1477_ = crate::leanh::lean_ctor_get(v_inst_1473_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1477_);
        crate::leanh::lean_dec(v_f_1474_);
        crate::leanh::lean_dec_ref(v_inst_1473_);
        v_toPure_1478_ = crate::leanh::lean_ctor_get(v_toApplicative_1477_, 1);
        crate::leanh::lean_inc(v_toPure_1478_);
        crate::leanh::lean_dec_ref(v_toApplicative_1477_);
        v___x_1479_ =
            crate::leanh::lean_apply_2(v_toPure_1478_, crate::leanh::lean_box(0), v_b_1476_);
        return v___x_1479_;
    } else {
        let mut v_toApplicative_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1480_ = crate::leanh::lean_ctor_get(v_inst_1473_, 0);
        v_toBind_1481_ = crate::leanh::lean_ctor_get(v_inst_1473_, 1);
        crate::leanh::lean_inc(v_toBind_1481_);
        v_toPure_1482_ = crate::leanh::lean_ctor_get(v_toApplicative_1480_, 1);
        crate::leanh::lean_inc(v_toPure_1482_);
        v_head_1483_ = crate::leanh::lean_ctor_get(v_as_x27_1475_, 0);
        v_tail_1484_ = crate::leanh::lean_ctor_get(v_as_x27_1475_, 1);
        crate::leanh::lean_inc(v_tail_1484_);
        crate::leanh::lean_inc(v_f_1474_);
        v___f_1485_ = crate::leanh::lean_alloc_closure(
            l_List_forIn_x27_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1485_, 0, v_toPure_1482_);
        crate::leanh::lean_closure_set(v___f_1485_, 1, v_inst_1473_);
        crate::leanh::lean_closure_set(v___f_1485_, 2, v_f_1474_);
        crate::leanh::lean_closure_set(v___f_1485_, 3, v_tail_1484_);
        crate::leanh::lean_inc(v_head_1483_);
        v___x_1486_ = crate::leanh::lean_apply_3(
            v_f_1474_,
            v_head_1483_,
            crate::leanh::lean_box(0),
            v_b_1476_,
        );
        v___x_1487_ = crate::leanh::lean_apply_4(
            v_toBind_1481_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1486_,
            v___f_1485_,
        );
        return v___x_1487_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___lam__0(
    mut v_toPure_1488_: *mut crate::leanh::LeanObject,
    mut v_inst_1489_: *mut crate::leanh::LeanObject,
    mut v_f_1490_: *mut crate::leanh::LeanObject,
    mut v_tail_1491_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1492_) == 0 {
        let mut v_a_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1490_);
        crate::leanh::lean_dec_ref(v_inst_1489_);
        v_a_1493_ = crate::leanh::lean_ctor_get(v_____do__lift_1492_, 0);
        crate::leanh::lean_inc(v_a_1493_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1492_, 1);
        v___x_1494_ =
            crate::leanh::lean_apply_2(v_toPure_1488_, crate::leanh::lean_box(0), v_a_1493_);
        return v___x_1494_;
    } else {
        let mut v_a_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1488_);
        v_a_1495_ = crate::leanh::lean_ctor_get(v_____do__lift_1492_, 0);
        crate::leanh::lean_inc(v_a_1495_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1492_, 1);
        v___x_1496_ =
            l_List_forIn_x27_loop___redArg(v_inst_1489_, v_f_1490_, v_tail_1491_, v_a_1495_);
        return v___x_1496_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___boxed(
    mut v_inst_1497_: *mut crate::leanh::LeanObject,
    mut v_f_1498_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1499_: *mut crate::leanh::LeanObject,
    mut v_b_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ =
        l_List_forIn_x27_loop___redArg(v_inst_1497_, v_f_1498_, v_as_x27_1499_, v_b_1500_);
    crate::leanh::lean_dec(v_as_x27_1499_);
    return v_res_1501_;
}
pub unsafe fn l_List_forIn_x27_loop(
    mut v_00_u03b1_1502_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1503_: *mut crate::leanh::LeanObject,
    mut v_m_1504_: *mut crate::leanh::LeanObject,
    mut v_inst_1505_: *mut crate::leanh::LeanObject,
    mut v_as_1506_: *mut crate::leanh::LeanObject,
    mut v_f_1507_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1508_: *mut crate::leanh::LeanObject,
    mut v_b_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ =
        l_List_forIn_x27_loop___redArg(v_inst_1505_, v_f_1507_, v_as_x27_1508_, v_b_1509_);
    return v___x_1511_;
}
pub unsafe fn l_List_forIn_x27_loop___boxed(
    mut v_00_u03b1_1512_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1513_: *mut crate::leanh::LeanObject,
    mut v_m_1514_: *mut crate::leanh::LeanObject,
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
    mut v_as_1516_: *mut crate::leanh::LeanObject,
    mut v_f_1517_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1518_: *mut crate::leanh::LeanObject,
    mut v_b_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1521_ = l_List_forIn_x27_loop(
        v_00_u03b1_1512_,
        v_00_u03b2_1513_,
        v_m_1514_,
        v_inst_1515_,
        v_as_1516_,
        v_f_1517_,
        v_as_x27_1518_,
        v_b_1519_,
        v_a_1520_,
    );
    crate::leanh::lean_dec(v_as_x27_1518_);
    crate::leanh::lean_dec(v_as_1516_);
    return v_res_1521_;
}
pub unsafe fn l_List_forIn_x27___redArg(
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
    mut v_as_1523_: *mut crate::leanh::LeanObject,
    mut v_init_1524_: *mut crate::leanh::LeanObject,
    mut v_f_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = l_List_forIn_x27_loop___redArg(v_inst_1522_, v_f_1525_, v_as_1523_, v_init_1524_);
    return v___x_1526_;
}
pub unsafe fn l_List_forIn_x27___redArg___boxed(
    mut v_inst_1527_: *mut crate::leanh::LeanObject,
    mut v_as_1528_: *mut crate::leanh::LeanObject,
    mut v_init_1529_: *mut crate::leanh::LeanObject,
    mut v_f_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_List_forIn_x27___redArg(v_inst_1527_, v_as_1528_, v_init_1529_, v_f_1530_);
    crate::leanh::lean_dec(v_as_1528_);
    return v_res_1531_;
}
pub unsafe fn l_List_forIn_x27(
    mut v_00_u03b1_1532_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1533_: *mut crate::leanh::LeanObject,
    mut v_m_1534_: *mut crate::leanh::LeanObject,
    mut v_inst_1535_: *mut crate::leanh::LeanObject,
    mut v_as_1536_: *mut crate::leanh::LeanObject,
    mut v_init_1537_: *mut crate::leanh::LeanObject,
    mut v_f_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_List_forIn_x27_loop___redArg(v_inst_1535_, v_f_1538_, v_as_1536_, v_init_1537_);
    return v___x_1539_;
}
pub unsafe fn l_List_forIn_x27___boxed(
    mut v_00_u03b1_1540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1541_: *mut crate::leanh::LeanObject,
    mut v_m_1542_: *mut crate::leanh::LeanObject,
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
    mut v_as_1544_: *mut crate::leanh::LeanObject,
    mut v_init_1545_: *mut crate::leanh::LeanObject,
    mut v_f_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_List_forIn_x27(
        v_00_u03b1_1540_,
        v_00_u03b2_1541_,
        v_m_1542_,
        v_inst_1543_,
        v_as_1544_,
        v_init_1545_,
        v_f_1546_,
    );
    crate::leanh::lean_dec(v_as_1544_);
    return v_res_1547_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_inst_1548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1553_ =
        l_List_forIn_x27_loop___redArg(v_inst_1548_, v___y_1552_, v___y_1550_, v___y_1551_);
    return v___x_1553_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(
    mut v_inst_1554_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
        v_inst_1554_,
        v_00_u03b2_1555_,
        v___y_1556_,
        v___y_1557_,
        v___y_1558_,
    );
    crate::leanh::lean_dec(v___y_1556_);
    return v_res_1559_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1561_ = crate::leanh::lean_alloc_closure(
        l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1561_, 0, v_inst_1560_);
    return v___f_1561_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad(
    mut v_m_1562_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1563_: *mut crate::leanh::LeanObject,
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1565_ = crate::leanh::lean_alloc_closure(
        l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1565_, 0, v_inst_1564_);
    return v___f_1565_;
}
pub unsafe fn l_List_instForMOfMonad___redArg(
    mut v_inst_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = crate::leanh::lean_alloc_closure(l_List_forM as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_1567_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1567_, 1, v_inst_1566_);
    crate::leanh::lean_closure_set(v___x_1567_, 2, crate::leanh::lean_box(0));
    return v___x_1567_;
}
pub unsafe fn l_List_instForMOfMonad(
    mut v_m_1568_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1569_: *mut crate::leanh::LeanObject,
    mut v_inst_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1571_ = crate::leanh::lean_alloc_closure(l_List_forM as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_1571_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1571_, 1, v_inst_1570_);
    crate::leanh::lean_closure_set(v___x_1571_, 2, crate::leanh::lean_box(0));
    return v___x_1571_;
}
pub unsafe fn l_List_instFunctor___lam__0(
    mut v_00_u03b1_1572_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1576_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1576_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1576_, 2, v___y_1574_);
    v___x_1577_ = crate::leanh::lean_box(0);
    v___x_1578_ = l_List_mapTR_loop___redArg(v___x_1576_, v___y_1575_, v___x_1577_);
    return v___x_1578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Control(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Control(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Control(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Control(builtin);
}
