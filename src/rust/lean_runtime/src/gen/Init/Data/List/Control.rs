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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub static l_List_mapA___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_mapA___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_mapA___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_mapA___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_zipWithM___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_List_zipWithM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_zipWithM___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_instFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_List_instFunctor___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_mapTR as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_List_instFunctor___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_instFunctor___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_instFunctor___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_List_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__2_value) as *mut LeanObject;
pub static mut l_List_instFunctor: *mut LeanObject =
    core::ptr::addr_of!(l_List_instFunctor___closed__2_value) as *mut LeanObject;
pub unsafe fn l_List_mapM_loop___redArg(
    mut v_inst_793_: *mut LeanObject,
    mut v_f_794_: *mut LeanObject,
    mut v_x_795_: *mut LeanObject,
    mut v_x_796_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_795_) == 0 {
        let mut v_toApplicative_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_797_ = lean_ctor_get(v_inst_793_, 0);
        lean_inc_ref(v_toApplicative_797_);
        lean_dec(v_f_794_);
        lean_dec_ref(v_inst_793_);
        v_toPure_798_ = lean_ctor_get(v_toApplicative_797_, 1);
        lean_inc(v_toPure_798_);
        lean_dec_ref(v_toApplicative_797_);
        v___x_799_ = l_List_reverse___redArg(v_x_796_);
        v___x_800_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_799_);
        return v___x_800_;
    } else {
        let mut v_toBind_801_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_802_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_801_ = lean_ctor_get(v_inst_793_, 1);
        lean_inc(v_toBind_801_);
        v_head_802_ = lean_ctor_get(v_x_795_, 0);
        lean_inc(v_head_802_);
        v_tail_803_ = lean_ctor_get(v_x_795_, 1);
        lean_inc(v_tail_803_);
        lean_dec_ref_known(v_x_795_, 2);
        lean_inc(v_f_794_);
        v___f_804_ = lean_alloc_closure(
            l_List_mapM_loop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_804_, 0, v_x_796_);
        lean_closure_set(v___f_804_, 1, v_inst_793_);
        lean_closure_set(v___f_804_, 2, v_f_794_);
        lean_closure_set(v___f_804_, 3, v_tail_803_);
        v___x_805_ = lean_apply_1(v_f_794_, v_head_802_);
        v___x_806_ = lean_apply_4(
            v_toBind_801_,
            lean_box(0),
            lean_box(0),
            v___x_805_,
            v___f_804_,
        );
        return v___x_806_;
    }
}
pub unsafe fn l_List_mapM_loop___redArg___lam__0(
    mut v_x_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_f_809_: *mut LeanObject,
    mut v_tail_810_: *mut LeanObject,
    mut v_____do__lift_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_812_, 0, v_____do__lift_811_);
    lean_ctor_set(v___x_812_, 1, v_x_807_);
    v___x_813_ = l_List_mapM_loop___redArg(v_inst_808_, v_f_809_, v_tail_810_, v___x_812_);
    return v___x_813_;
}
pub unsafe fn l_List_mapM_loop(
    mut v_m_814_: *mut LeanObject,
    mut v_inst_815_: *mut LeanObject,
    mut v_00_u03b1_816_: *mut LeanObject,
    mut v_00_u03b2_817_: *mut LeanObject,
    mut v_f_818_: *mut LeanObject,
    mut v_x_819_: *mut LeanObject,
    mut v_x_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    v___x_821_ = l_List_mapM_loop___redArg(v_inst_815_, v_f_818_, v_x_819_, v_x_820_);
    return v___x_821_;
}
pub unsafe fn l_List_mapM___redArg(
    mut v_inst_822_: *mut LeanObject,
    mut v_f_823_: *mut LeanObject,
    mut v_as_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_825_ = lean_box(0);
    v___x_826_ = l_List_mapM_loop___redArg(v_inst_822_, v_f_823_, v_as_824_, v___x_825_);
    return v___x_826_;
}
pub unsafe fn l_List_mapM(
    mut v_m_827_: *mut LeanObject,
    mut v_inst_828_: *mut LeanObject,
    mut v_00_u03b1_829_: *mut LeanObject,
    mut v_00_u03b2_830_: *mut LeanObject,
    mut v_f_831_: *mut LeanObject,
    mut v_as_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    v___x_833_ = lean_box(0);
    v___x_834_ = l_List_mapM_loop___redArg(v_inst_828_, v_f_831_, v_as_832_, v___x_833_);
    return v___x_834_;
}
pub unsafe fn l_List_mapA___redArg___lam__0(
    mut v_head_835_: *mut LeanObject,
    mut v_tail_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_837_, 0, v_head_835_);
    lean_ctor_set(v___x_837_, 1, v_tail_836_);
    return v___x_837_;
}
pub unsafe fn l_List_mapA___redArg(
    mut v_inst_839_: *mut LeanObject,
    mut v_f_840_: *mut LeanObject,
    mut v_x_841_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_841_) == 0 {
        let mut v_toPure_842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_840_);
        v_toPure_842_ = lean_ctor_get(v_inst_839_, 1);
        lean_inc(v_toPure_842_);
        lean_dec_ref(v_inst_839_);
        v___x_843_ = lean_box(0);
        v___x_844_ = lean_apply_2(v_toPure_842_, lean_box(0), v___x_843_);
        return v___x_844_;
    } else {
        let mut v_toFunctor_845_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toSeq_846_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_847_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_848_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_845_ = lean_ctor_get(v_inst_839_, 0);
        v_toSeq_846_ = lean_ctor_get(v_inst_839_, 2);
        lean_inc(v_toSeq_846_);
        v_head_847_ = lean_ctor_get(v_x_841_, 0);
        lean_inc(v_head_847_);
        v_tail_848_ = lean_ctor_get(v_x_841_, 1);
        lean_inc(v_tail_848_);
        lean_dec_ref_known(v_x_841_, 2);
        v_map_849_ = lean_ctor_get(v_toFunctor_845_, 0);
        lean_inc(v_map_849_);
        v___f_850_ = l_List_mapA___redArg___closed__0;
        lean_inc(v_f_840_);
        v___f_851_ = lean_alloc_closure(
            l_List_mapA___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_851_, 0, v_inst_839_);
        lean_closure_set(v___f_851_, 1, v_f_840_);
        lean_closure_set(v___f_851_, 2, v_tail_848_);
        v___x_852_ = lean_apply_1(v_f_840_, v_head_847_);
        v___x_853_ = lean_apply_4(v_map_849_, lean_box(0), lean_box(0), v___f_850_, v___x_852_);
        v___x_854_ = lean_apply_4(
            v_toSeq_846_,
            lean_box(0),
            lean_box(0),
            v___x_853_,
            v___f_851_,
        );
        return v___x_854_;
    }
}
pub unsafe fn l_List_mapA___redArg___lam__1(
    mut v_inst_855_: *mut LeanObject,
    mut v_f_856_: *mut LeanObject,
    mut v_tail_857_: *mut LeanObject,
    mut v_x_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = l_List_mapA___redArg(v_inst_855_, v_f_856_, v_tail_857_);
    return v___x_859_;
}
pub unsafe fn l_List_mapA(
    mut v_m_860_: *mut LeanObject,
    mut v_inst_861_: *mut LeanObject,
    mut v_00_u03b1_862_: *mut LeanObject,
    mut v_00_u03b2_863_: *mut LeanObject,
    mut v_f_864_: *mut LeanObject,
    mut v_x_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = l_List_mapA___redArg(v_inst_861_, v_f_864_, v_x_865_);
    return v___x_866_;
}
pub unsafe fn l_List_forM___redArg(
    mut v_inst_867_: *mut LeanObject,
    mut v_as_868_: *mut LeanObject,
    mut v_f_869_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_as_868_) == 0 {
        let mut v_toApplicative_870_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_870_ = lean_ctor_get(v_inst_867_, 0);
        lean_inc_ref(v_toApplicative_870_);
        lean_dec(v_f_869_);
        lean_dec_ref(v_inst_867_);
        v_toPure_871_ = lean_ctor_get(v_toApplicative_870_, 1);
        lean_inc(v_toPure_871_);
        lean_dec_ref(v_toApplicative_870_);
        v___x_872_ = lean_box(0);
        v___x_873_ = lean_apply_2(v_toPure_871_, lean_box(0), v___x_872_);
        return v___x_873_;
    } else {
        let mut v_toBind_874_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_875_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_874_ = lean_ctor_get(v_inst_867_, 1);
        lean_inc(v_toBind_874_);
        v_head_875_ = lean_ctor_get(v_as_868_, 0);
        lean_inc(v_head_875_);
        v_tail_876_ = lean_ctor_get(v_as_868_, 1);
        lean_inc(v_tail_876_);
        lean_dec_ref_known(v_as_868_, 2);
        lean_inc(v_f_869_);
        v___f_877_ = lean_alloc_closure(
            l_List_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_877_, 0, v_inst_867_);
        lean_closure_set(v___f_877_, 1, v_tail_876_);
        lean_closure_set(v___f_877_, 2, v_f_869_);
        v___x_878_ = lean_apply_1(v_f_869_, v_head_875_);
        v___x_879_ = lean_apply_4(
            v_toBind_874_,
            lean_box(0),
            lean_box(0),
            v___x_878_,
            v___f_877_,
        );
        return v___x_879_;
    }
}
pub unsafe fn l_List_forM___redArg___lam__0(
    mut v_inst_880_: *mut LeanObject,
    mut v_tail_881_: *mut LeanObject,
    mut v_f_882_: *mut LeanObject,
    mut v_____r_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = l_List_forM___redArg(v_inst_880_, v_tail_881_, v_f_882_);
    return v___x_884_;
}
pub unsafe fn l_List_forM(
    mut v_m_885_: *mut LeanObject,
    mut v_inst_886_: *mut LeanObject,
    mut v_00_u03b1_887_: *mut LeanObject,
    mut v_as_888_: *mut LeanObject,
    mut v_f_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = l_List_forM___redArg(v_inst_886_, v_as_888_, v_f_889_);
    return v___x_890_;
}
pub unsafe fn l_List_forA___redArg(
    mut v_inst_891_: *mut LeanObject,
    mut v_as_892_: *mut LeanObject,
    mut v_f_893_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_as_892_) == 0 {
        let mut v_toPure_894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_893_);
        v_toPure_894_ = lean_ctor_get(v_inst_891_, 1);
        lean_inc(v_toPure_894_);
        lean_dec_ref(v_inst_891_);
        v___x_895_ = lean_box(0);
        v___x_896_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_895_);
        return v___x_896_;
    } else {
        let mut v_toSeqRight_897_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_898_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
        v_toSeqRight_897_ = lean_ctor_get(v_inst_891_, 4);
        lean_inc(v_toSeqRight_897_);
        v_head_898_ = lean_ctor_get(v_as_892_, 0);
        lean_inc(v_head_898_);
        v_tail_899_ = lean_ctor_get(v_as_892_, 1);
        lean_inc(v_tail_899_);
        lean_dec_ref_known(v_as_892_, 2);
        lean_inc(v_f_893_);
        v___f_900_ = lean_alloc_closure(
            l_List_forA___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_900_, 0, v_inst_891_);
        lean_closure_set(v___f_900_, 1, v_tail_899_);
        lean_closure_set(v___f_900_, 2, v_f_893_);
        v___x_901_ = lean_apply_1(v_f_893_, v_head_898_);
        v___x_902_ = lean_apply_4(
            v_toSeqRight_897_,
            lean_box(0),
            lean_box(0),
            v___x_901_,
            v___f_900_,
        );
        return v___x_902_;
    }
}
pub unsafe fn l_List_forA___redArg___lam__0(
    mut v_inst_903_: *mut LeanObject,
    mut v_tail_904_: *mut LeanObject,
    mut v_f_905_: *mut LeanObject,
    mut v_x_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = l_List_forA___redArg(v_inst_903_, v_tail_904_, v_f_905_);
    return v___x_907_;
}
pub unsafe fn l_List_forA(
    mut v_m_908_: *mut LeanObject,
    mut v_inst_909_: *mut LeanObject,
    mut v_00_u03b1_910_: *mut LeanObject,
    mut v_as_911_: *mut LeanObject,
    mut v_f_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = l_List_forA___redArg(v_inst_909_, v_as_911_, v_f_912_);
    return v___x_913_;
}
pub unsafe fn l_List_zipWithM_loop___redArg(
    mut v_inst_914_: *mut LeanObject,
    mut v_f_915_: *mut LeanObject,
    mut v_x_916_: *mut LeanObject,
    mut v_x_917_: *mut LeanObject,
    mut v_x_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_919_ = lean_ctor_get(v_inst_914_, 0);
                v_toBind_920_ = lean_ctor_get(v_inst_914_, 1);
                lean_inc(v_toBind_920_);
                v_toPure_921_ = lean_ctor_get(v_toApplicative_919_, 1);
                if lean_obj_tag(v_x_916_) == 1 {
                    if lean_obj_tag(v_x_917_) == 1 {
                        v_head_926_ = lean_ctor_get(v_x_916_, 0);
                        lean_inc(v_head_926_);
                        v_tail_927_ = lean_ctor_get(v_x_916_, 1);
                        lean_inc(v_tail_927_);
                        lean_dec_ref_known(v_x_916_, 2);
                        v_head_928_ = lean_ctor_get(v_x_917_, 0);
                        lean_inc(v_head_928_);
                        v_tail_929_ = lean_ctor_get(v_x_917_, 1);
                        lean_inc(v_tail_929_);
                        lean_dec_ref_known(v_x_917_, 2);
                        lean_inc(v_f_915_);
                        v___f_930_ = lean_alloc_closure(
                            l_List_zipWithM_loop___redArg___lam__0 as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        lean_closure_set(v___f_930_, 0, v_x_918_);
                        lean_closure_set(v___f_930_, 1, v_inst_914_);
                        lean_closure_set(v___f_930_, 2, v_f_915_);
                        lean_closure_set(v___f_930_, 3, v_tail_927_);
                        lean_closure_set(v___f_930_, 4, v_tail_929_);
                        v___x_931_ = lean_apply_2(v_f_915_, v_head_926_, v_head_928_);
                        v___x_932_ = lean_apply_4(
                            v_toBind_920_,
                            lean_box(0),
                            lean_box(0),
                            v___x_931_,
                            v___f_930_,
                        );
                        return v___x_932_;
                    } else {
                        lean_inc(v_toPure_921_);
                        lean_dec_ref_known(v_x_916_, 2);
                        lean_dec(v_toBind_920_);
                        lean_dec(v_x_917_);
                        lean_dec(v_f_915_);
                        lean_dec_ref(v_inst_914_);
                        v_acc_923_ = v_x_918_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_toPure_921_);
                    lean_dec(v_toBind_920_);
                    lean_dec(v_x_917_);
                    lean_dec(v_x_916_);
                    lean_dec(v_f_915_);
                    lean_dec_ref(v_inst_914_);
                    v_acc_923_ = v_x_918_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_924_ = lean_array_to_list(v_acc_923_);
                v___x_925_ = lean_apply_2(v_toPure_921_, lean_box(0), v___x_924_);
                return v___x_925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithM_loop___redArg___lam__0(
    mut v_x_933_: *mut LeanObject,
    mut v_inst_934_: *mut LeanObject,
    mut v_f_935_: *mut LeanObject,
    mut v_tail_936_: *mut LeanObject,
    mut v_tail_937_: *mut LeanObject,
    mut v_____do__lift_938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_939_ = lean_array_push(v_x_933_, v_____do__lift_938_);
    v___x_940_ =
        l_List_zipWithM_loop___redArg(v_inst_934_, v_f_935_, v_tail_936_, v_tail_937_, v___x_939_);
    return v___x_940_;
}
pub unsafe fn l_List_zipWithM_loop(
    mut v_m_941_: *mut LeanObject,
    mut v_inst_942_: *mut LeanObject,
    mut v_00_u03b1_943_: *mut LeanObject,
    mut v_00_u03b2_944_: *mut LeanObject,
    mut v_00_u03b3_945_: *mut LeanObject,
    mut v_f_946_: *mut LeanObject,
    mut v_x_947_: *mut LeanObject,
    mut v_x_948_: *mut LeanObject,
    mut v_x_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_950_ = l_List_zipWithM_loop___redArg(v_inst_942_, v_f_946_, v_x_947_, v_x_948_, v_x_949_);
    return v___x_950_;
}
pub unsafe fn l_List_zipWithM___redArg(
    mut v_inst_953_: *mut LeanObject,
    mut v_f_954_: *mut LeanObject,
    mut v_as_955_: *mut LeanObject,
    mut v_bs_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    v___x_957_ = l_List_zipWithM___redArg___closed__0;
    v___x_958_ =
        l_List_zipWithM_loop___redArg(v_inst_953_, v_f_954_, v_as_955_, v_bs_956_, v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_List_zipWithM(
    mut v_m_959_: *mut LeanObject,
    mut v_inst_960_: *mut LeanObject,
    mut v_00_u03b1_961_: *mut LeanObject,
    mut v_00_u03b2_962_: *mut LeanObject,
    mut v_00_u03b3_963_: *mut LeanObject,
    mut v_f_964_: *mut LeanObject,
    mut v_as_965_: *mut LeanObject,
    mut v_bs_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = l_List_zipWithM___redArg___closed__0;
    v___x_968_ =
        l_List_zipWithM_loop___redArg(v_inst_960_, v_f_964_, v_as_965_, v_bs_966_, v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_List_filterAuxM___redArg___lam__0___boxed(
    mut v_inst_969_: *mut LeanObject,
    mut v_f_970_: *mut LeanObject,
    mut v_tail_971_: *mut LeanObject,
    mut v_x_972_: *mut LeanObject,
    mut v_head_973_: *mut LeanObject,
    mut v_b_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_975_: u8 = 0;
    let mut v_res_976_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_975_ = (lean_unbox(v_b_974_) as u8);
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
    mut v_inst_977_: *mut LeanObject,
    mut v_f_978_: *mut LeanObject,
    mut v_x_979_: *mut LeanObject,
    mut v_x_980_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_979_) == 0 {
        let mut v_toApplicative_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_981_ = lean_ctor_get(v_inst_977_, 0);
        lean_inc_ref(v_toApplicative_981_);
        lean_dec(v_f_978_);
        lean_dec_ref(v_inst_977_);
        v_toPure_982_ = lean_ctor_get(v_toApplicative_981_, 1);
        lean_inc(v_toPure_982_);
        lean_dec_ref(v_toApplicative_981_);
        v___x_983_ = lean_apply_2(v_toPure_982_, lean_box(0), v_x_980_);
        return v___x_983_;
    } else {
        let mut v_toBind_984_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_985_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_984_ = lean_ctor_get(v_inst_977_, 1);
        lean_inc(v_toBind_984_);
        v_head_985_ = lean_ctor_get(v_x_979_, 0);
        lean_inc_n(v_head_985_, 2);
        v_tail_986_ = lean_ctor_get(v_x_979_, 1);
        lean_inc(v_tail_986_);
        lean_dec_ref_known(v_x_979_, 2);
        lean_inc(v_f_978_);
        v___f_987_ = lean_alloc_closure(
            l_List_filterAuxM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_987_, 0, v_inst_977_);
        lean_closure_set(v___f_987_, 1, v_f_978_);
        lean_closure_set(v___f_987_, 2, v_tail_986_);
        lean_closure_set(v___f_987_, 3, v_x_980_);
        lean_closure_set(v___f_987_, 4, v_head_985_);
        v___x_988_ = lean_apply_1(v_f_978_, v_head_985_);
        v___x_989_ = lean_apply_4(
            v_toBind_984_,
            lean_box(0),
            lean_box(0),
            v___x_988_,
            v___f_987_,
        );
        return v___x_989_;
    }
}
pub unsafe fn l_List_filterAuxM___redArg___lam__0(
    mut v_inst_990_: *mut LeanObject,
    mut v_f_991_: *mut LeanObject,
    mut v_tail_992_: *mut LeanObject,
    mut v_x_993_: *mut LeanObject,
    mut v_head_994_: *mut LeanObject,
    mut v_b_995_: u8,
) -> *mut LeanObject {
    if v_b_995_ == 0 {
        let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_head_994_);
        v___x_996_ = l_List_filterAuxM___redArg(v_inst_990_, v_f_991_, v_tail_992_, v_x_993_);
        return v___x_996_;
    } else {
        let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
        v___x_997_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_997_, 0, v_head_994_);
        lean_ctor_set(v___x_997_, 1, v_x_993_);
        v___x_998_ = l_List_filterAuxM___redArg(v_inst_990_, v_f_991_, v_tail_992_, v___x_997_);
        return v___x_998_;
    }
}
pub unsafe fn l_List_filterAuxM(
    mut v_m_999_: *mut LeanObject,
    mut v_inst_1000_: *mut LeanObject,
    mut v_00_u03b1_1001_: *mut LeanObject,
    mut v_f_1002_: *mut LeanObject,
    mut v_x_1003_: *mut LeanObject,
    mut v_x_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1005_ = l_List_filterAuxM___redArg(v_inst_1000_, v_f_1002_, v_x_1003_, v_x_1004_);
    return v___x_1005_;
}
pub unsafe fn l_List_filterM___redArg___lam__0(
    mut v_toPure_1006_: *mut LeanObject,
    mut v_as_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1008_ = l_List_reverse___redArg(v_as_1007_);
    v___x_1009_ = lean_apply_2(v_toPure_1006_, lean_box(0), v___x_1008_);
    return v___x_1009_;
}
pub unsafe fn l_List_filterM___redArg(
    mut v_inst_1010_: *mut LeanObject,
    mut v_p_1011_: *mut LeanObject,
    mut v_as_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1013_ = lean_ctor_get(v_inst_1010_, 0);
    v_toBind_1014_ = lean_ctor_get(v_inst_1010_, 1);
    lean_inc(v_toBind_1014_);
    v_toPure_1015_ = lean_ctor_get(v_toApplicative_1013_, 1);
    lean_inc(v_toPure_1015_);
    v___x_1016_ = lean_box(0);
    v___x_1017_ = l_List_filterAuxM___redArg(v_inst_1010_, v_p_1011_, v_as_1012_, v___x_1016_);
    v___f_1018_ = lean_alloc_closure(
        l_List_filterM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1018_, 0, v_toPure_1015_);
    v___x_1019_ = lean_apply_4(
        v_toBind_1014_,
        lean_box(0),
        lean_box(0),
        v___x_1017_,
        v___f_1018_,
    );
    return v___x_1019_;
}
pub unsafe fn l_List_filterM(
    mut v_m_1020_: *mut LeanObject,
    mut v_inst_1021_: *mut LeanObject,
    mut v_00_u03b1_1022_: *mut LeanObject,
    mut v_p_1023_: *mut LeanObject,
    mut v_as_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1025_ = lean_ctor_get(v_inst_1021_, 0);
    v_toBind_1026_ = lean_ctor_get(v_inst_1021_, 1);
    lean_inc(v_toBind_1026_);
    v_toPure_1027_ = lean_ctor_get(v_toApplicative_1025_, 1);
    lean_inc(v_toPure_1027_);
    v___x_1028_ = lean_box(0);
    v___x_1029_ = l_List_filterAuxM___redArg(v_inst_1021_, v_p_1023_, v_as_1024_, v___x_1028_);
    v___f_1030_ = lean_alloc_closure(
        l_List_filterM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1030_, 0, v_toPure_1027_);
    v___x_1031_ = lean_apply_4(
        v_toBind_1026_,
        lean_box(0),
        lean_box(0),
        v___x_1029_,
        v___f_1030_,
    );
    return v___x_1031_;
}
pub unsafe fn l_List_filterRevM___redArg(
    mut v_inst_1032_: *mut LeanObject,
    mut v_p_1033_: *mut LeanObject,
    mut v_as_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = l_List_reverse___redArg(v_as_1034_);
    v___x_1036_ = lean_box(0);
    v___x_1037_ = l_List_filterAuxM___redArg(v_inst_1032_, v_p_1033_, v___x_1035_, v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_List_filterRevM(
    mut v_m_1038_: *mut LeanObject,
    mut v_inst_1039_: *mut LeanObject,
    mut v_00_u03b1_1040_: *mut LeanObject,
    mut v_p_1041_: *mut LeanObject,
    mut v_as_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_List_reverse___redArg(v_as_1042_);
    v___x_1044_ = lean_box(0);
    v___x_1045_ = l_List_filterAuxM___redArg(v_inst_1039_, v_p_1041_, v___x_1043_, v___x_1044_);
    return v___x_1045_;
}
pub unsafe fn l_List_filterMapM_loop___redArg___lam__0___boxed(
    mut v_inst_1046_: *mut LeanObject,
    mut v_f_1047_: *mut LeanObject,
    mut v_tail_1048_: *mut LeanObject,
    mut v_x_1049_: *mut LeanObject,
    mut v_____do__lift_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1051_: *mut LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_List_filterMapM_loop___redArg___lam__0(
        v_inst_1046_,
        v_f_1047_,
        v_tail_1048_,
        v_x_1049_,
        v_____do__lift_1050_,
    );
    lean_dec(v_____do__lift_1050_);
    return v_res_1051_;
}
pub unsafe fn l_List_filterMapM_loop___redArg(
    mut v_inst_1052_: *mut LeanObject,
    mut v_f_1053_: *mut LeanObject,
    mut v_x_1054_: *mut LeanObject,
    mut v_x_1055_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1054_) == 0 {
        let mut v_toApplicative_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1056_ = lean_ctor_get(v_inst_1052_, 0);
        lean_inc_ref(v_toApplicative_1056_);
        lean_dec(v_f_1053_);
        lean_dec_ref(v_inst_1052_);
        v_toPure_1057_ = lean_ctor_get(v_toApplicative_1056_, 1);
        lean_inc(v_toPure_1057_);
        lean_dec_ref(v_toApplicative_1056_);
        v___x_1058_ = l_List_reverse___redArg(v_x_1055_);
        v___x_1059_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1058_);
        return v___x_1059_;
    } else {
        let mut v_toBind_1060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1060_ = lean_ctor_get(v_inst_1052_, 1);
        lean_inc(v_toBind_1060_);
        v_head_1061_ = lean_ctor_get(v_x_1054_, 0);
        lean_inc(v_head_1061_);
        v_tail_1062_ = lean_ctor_get(v_x_1054_, 1);
        lean_inc(v_tail_1062_);
        lean_dec_ref_known(v_x_1054_, 2);
        lean_inc(v_f_1053_);
        v___f_1063_ = lean_alloc_closure(
            l_List_filterMapM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1063_, 0, v_inst_1052_);
        lean_closure_set(v___f_1063_, 1, v_f_1053_);
        lean_closure_set(v___f_1063_, 2, v_tail_1062_);
        lean_closure_set(v___f_1063_, 3, v_x_1055_);
        v___x_1064_ = lean_apply_1(v_f_1053_, v_head_1061_);
        v___x_1065_ = lean_apply_4(
            v_toBind_1060_,
            lean_box(0),
            lean_box(0),
            v___x_1064_,
            v___f_1063_,
        );
        return v___x_1065_;
    }
}
pub unsafe fn l_List_filterMapM_loop___redArg___lam__0(
    mut v_inst_1066_: *mut LeanObject,
    mut v_f_1067_: *mut LeanObject,
    mut v_tail_1068_: *mut LeanObject,
    mut v_x_1069_: *mut LeanObject,
    mut v_____do__lift_1070_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1070_) == 0 {
        let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
        v___x_1071_ =
            l_List_filterMapM_loop___redArg(v_inst_1066_, v_f_1067_, v_tail_1068_, v_x_1069_);
        return v___x_1071_;
    } else {
        let mut v_val_1072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
        v_val_1072_ = lean_ctor_get(v_____do__lift_1070_, 0);
        lean_inc(v_val_1072_);
        v___x_1073_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1073_, 0, v_val_1072_);
        lean_ctor_set(v___x_1073_, 1, v_x_1069_);
        v___x_1074_ =
            l_List_filterMapM_loop___redArg(v_inst_1066_, v_f_1067_, v_tail_1068_, v___x_1073_);
        return v___x_1074_;
    }
}
pub unsafe fn l_List_filterMapM_loop(
    mut v_m_1075_: *mut LeanObject,
    mut v_inst_1076_: *mut LeanObject,
    mut v_00_u03b1_1077_: *mut LeanObject,
    mut v_00_u03b2_1078_: *mut LeanObject,
    mut v_f_1079_: *mut LeanObject,
    mut v_x_1080_: *mut LeanObject,
    mut v_x_1081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_List_filterMapM_loop___redArg(v_inst_1076_, v_f_1079_, v_x_1080_, v_x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_List_filterMapM___redArg(
    mut v_inst_1083_: *mut LeanObject,
    mut v_f_1084_: *mut LeanObject,
    mut v_as_1085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1086_ = lean_box(0);
    v___x_1087_ = l_List_filterMapM_loop___redArg(v_inst_1083_, v_f_1084_, v_as_1085_, v___x_1086_);
    return v___x_1087_;
}
pub unsafe fn l_List_filterMapM(
    mut v_m_1088_: *mut LeanObject,
    mut v_inst_1089_: *mut LeanObject,
    mut v_00_u03b1_1090_: *mut LeanObject,
    mut v_00_u03b2_1091_: *mut LeanObject,
    mut v_f_1092_: *mut LeanObject,
    mut v_as_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v___x_1094_ = lean_box(0);
    v___x_1095_ = l_List_filterMapM_loop___redArg(v_inst_1089_, v_f_1092_, v_as_1093_, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_List_foldlM___redArg(
    mut v_inst_1096_: *mut LeanObject,
    mut v_x_1097_: *mut LeanObject,
    mut v_x_1098_: *mut LeanObject,
    mut v_x_1099_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1099_) == 0 {
        let mut v_toApplicative_1100_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1100_ = lean_ctor_get(v_inst_1096_, 0);
        lean_inc_ref(v_toApplicative_1100_);
        lean_dec(v_x_1097_);
        lean_dec_ref(v_inst_1096_);
        v_toPure_1101_ = lean_ctor_get(v_toApplicative_1100_, 1);
        lean_inc(v_toPure_1101_);
        lean_dec_ref(v_toApplicative_1100_);
        v___x_1102_ = lean_apply_2(v_toPure_1101_, lean_box(0), v_x_1098_);
        return v___x_1102_;
    } else {
        let mut v_toBind_1103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1104_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1103_ = lean_ctor_get(v_inst_1096_, 1);
        lean_inc(v_toBind_1103_);
        v_head_1104_ = lean_ctor_get(v_x_1099_, 0);
        lean_inc(v_head_1104_);
        v_tail_1105_ = lean_ctor_get(v_x_1099_, 1);
        lean_inc(v_tail_1105_);
        lean_dec_ref_known(v_x_1099_, 2);
        lean_inc(v_x_1097_);
        v___f_1106_ = lean_alloc_closure(
            l_List_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1106_, 0, v_inst_1096_);
        lean_closure_set(v___f_1106_, 1, v_x_1097_);
        lean_closure_set(v___f_1106_, 2, v_tail_1105_);
        v___x_1107_ = lean_apply_2(v_x_1097_, v_x_1098_, v_head_1104_);
        v___x_1108_ = lean_apply_4(
            v_toBind_1103_,
            lean_box(0),
            lean_box(0),
            v___x_1107_,
            v___f_1106_,
        );
        return v___x_1108_;
    }
}
pub unsafe fn l_List_foldlM___redArg___lam__0(
    mut v_inst_1109_: *mut LeanObject,
    mut v_x_1110_: *mut LeanObject,
    mut v_tail_1111_: *mut LeanObject,
    mut v_s_x27_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v___x_1113_ = l_List_foldlM___redArg(v_inst_1109_, v_x_1110_, v_s_x27_1112_, v_tail_1111_);
    return v___x_1113_;
}
pub unsafe fn l_List_foldlM(
    mut v_m_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_s_1116_: *mut LeanObject,
    mut v_00_u03b1_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
    mut v_x_1119_: *mut LeanObject,
    mut v_x_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_List_foldlM___redArg(v_inst_1115_, v_x_1118_, v_x_1119_, v_x_1120_);
    return v___x_1121_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter___redArg(
    mut v_x_1122_: *mut LeanObject,
    mut v_x_1123_: *mut LeanObject,
    mut v_x_1124_: *mut LeanObject,
    mut v_h__1_1125_: *mut LeanObject,
    mut v_h__2_1126_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1124_) == 0 {
        let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1126_);
        v___x_1127_ = lean_apply_2(v_h__1_1125_, v_x_1122_, v_x_1123_);
        return v___x_1127_;
    } else {
        let mut v_head_1128_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1125_);
        v_head_1128_ = lean_ctor_get(v_x_1124_, 0);
        lean_inc(v_head_1128_);
        v_tail_1129_ = lean_ctor_get(v_x_1124_, 1);
        lean_inc(v_tail_1129_);
        lean_dec_ref_known(v_x_1124_, 2);
        v___x_1130_ = lean_apply_4(
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
    mut v_m_1131_: *mut LeanObject,
    mut v_s_1132_: *mut LeanObject,
    mut v_00_u03b1_1133_: *mut LeanObject,
    mut v_motive_1134_: *mut LeanObject,
    mut v_x_1135_: *mut LeanObject,
    mut v_x_1136_: *mut LeanObject,
    mut v_x_1137_: *mut LeanObject,
    mut v_h__1_1138_: *mut LeanObject,
    mut v_h__2_1139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1137_) == 0 {
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1139_);
        v___x_1140_ = lean_apply_2(v_h__1_1138_, v_x_1135_, v_x_1136_);
        return v___x_1140_;
    } else {
        let mut v_head_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1138_);
        v_head_1141_ = lean_ctor_get(v_x_1137_, 0);
        lean_inc(v_head_1141_);
        v_tail_1142_ = lean_ctor_get(v_x_1137_, 1);
        lean_inc(v_tail_1142_);
        lean_dec_ref_known(v_x_1137_, 2);
        v___x_1143_ = lean_apply_4(
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
    mut v_f_1144_: *mut LeanObject,
    mut v_s_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    v___x_1147_ = lean_apply_2(v_f_1144_, v_a_1146_, v_s_1145_);
    return v___x_1147_;
}
pub unsafe fn l_List_foldrM___redArg(
    mut v_inst_1148_: *mut LeanObject,
    mut v_f_1149_: *mut LeanObject,
    mut v_init_1150_: *mut LeanObject,
    mut v_l_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___f_1152_ = lean_alloc_closure(
        l_List_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1152_, 0, v_f_1149_);
    v___x_1153_ = l_List_reverse___redArg(v_l_1151_);
    v___x_1154_ = l_List_foldlM___redArg(v_inst_1148_, v___f_1152_, v_init_1150_, v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn l_List_foldrM(
    mut v_m_1155_: *mut LeanObject,
    mut v_inst_1156_: *mut LeanObject,
    mut v_s_1157_: *mut LeanObject,
    mut v_00_u03b1_1158_: *mut LeanObject,
    mut v_f_1159_: *mut LeanObject,
    mut v_init_1160_: *mut LeanObject,
    mut v_l_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___f_1162_ = lean_alloc_closure(
        l_List_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1162_, 0, v_f_1159_);
    v___x_1163_ = l_List_reverse___redArg(v_l_1161_);
    v___x_1164_ = l_List_foldlM___redArg(v_inst_1156_, v___f_1162_, v_init_1160_, v___x_1163_);
    return v___x_1164_;
}
pub unsafe fn l_List_firstM___redArg(
    mut v_inst_1165_: *mut LeanObject,
    mut v_f_1166_: *mut LeanObject,
    mut v_x_1167_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1167_) == 0 {
        let mut v_failure_1168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1166_);
        v_failure_1168_ = lean_ctor_get(v_inst_1165_, 1);
        lean_inc(v_failure_1168_);
        lean_dec_ref(v_inst_1165_);
        v___x_1169_ = lean_apply_1(v_failure_1168_, lean_box(0));
        return v___x_1169_;
    } else {
        let mut v_head_1170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_orElse_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        v_head_1170_ = lean_ctor_get(v_x_1167_, 0);
        lean_inc(v_head_1170_);
        v_tail_1171_ = lean_ctor_get(v_x_1167_, 1);
        lean_inc(v_tail_1171_);
        lean_dec_ref_known(v_x_1167_, 2);
        v_orElse_1172_ = lean_ctor_get(v_inst_1165_, 2);
        lean_inc(v_orElse_1172_);
        lean_inc(v_f_1166_);
        v___f_1173_ = lean_alloc_closure(
            l_List_firstM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1173_, 0, v_inst_1165_);
        lean_closure_set(v___f_1173_, 1, v_f_1166_);
        lean_closure_set(v___f_1173_, 2, v_tail_1171_);
        v___x_1174_ = lean_apply_1(v_f_1166_, v_head_1170_);
        v___x_1175_ = lean_apply_3(v_orElse_1172_, lean_box(0), v___x_1174_, v___f_1173_);
        return v___x_1175_;
    }
}
pub unsafe fn l_List_firstM___redArg___lam__0(
    mut v_inst_1176_: *mut LeanObject,
    mut v_f_1177_: *mut LeanObject,
    mut v_tail_1178_: *mut LeanObject,
    mut v_x_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_List_firstM___redArg(v_inst_1176_, v_f_1177_, v_tail_1178_);
    return v___x_1180_;
}
pub unsafe fn l_List_firstM(
    mut v_m_1181_: *mut LeanObject,
    mut v_inst_1182_: *mut LeanObject,
    mut v_00_u03b1_1183_: *mut LeanObject,
    mut v_00_u03b2_1184_: *mut LeanObject,
    mut v_f_1185_: *mut LeanObject,
    mut v_x_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_List_firstM___redArg(v_inst_1182_, v_f_1185_, v_x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_List_anyM___redArg___lam__0___boxed(
    mut v_inst_1188_: *mut LeanObject,
    mut v_p_1189_: *mut LeanObject,
    mut v_tail_1190_: *mut LeanObject,
    mut v_toPure_1191_: *mut LeanObject,
    mut v_____do__lift_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_73__boxed_1193_: u8 = 0;
    let mut v_res_1194_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_73__boxed_1193_ = (lean_unbox(v_____do__lift_1192_) as u8);
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
    mut v_inst_1195_: *mut LeanObject,
    mut v_p_1196_: *mut LeanObject,
    mut v_x_1197_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1197_) == 0 {
        let mut v_toApplicative_1198_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: u8 = 0;
        let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1198_ = lean_ctor_get(v_inst_1195_, 0);
        lean_inc_ref(v_toApplicative_1198_);
        lean_dec(v_p_1196_);
        lean_dec_ref(v_inst_1195_);
        v_toPure_1199_ = lean_ctor_get(v_toApplicative_1198_, 1);
        lean_inc(v_toPure_1199_);
        lean_dec_ref(v_toApplicative_1198_);
        v___x_1200_ = 0;
        v___x_1201_ = lean_box((v___x_1200_) as usize);
        v___x_1202_ = lean_apply_2(v_toPure_1199_, lean_box(0), v___x_1201_);
        return v___x_1202_;
    } else {
        let mut v_toApplicative_1203_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1204_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1205_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1206_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1203_ = lean_ctor_get(v_inst_1195_, 0);
        v_toBind_1204_ = lean_ctor_get(v_inst_1195_, 1);
        lean_inc(v_toBind_1204_);
        v_toPure_1205_ = lean_ctor_get(v_toApplicative_1203_, 1);
        lean_inc(v_toPure_1205_);
        v_head_1206_ = lean_ctor_get(v_x_1197_, 0);
        lean_inc(v_head_1206_);
        v_tail_1207_ = lean_ctor_get(v_x_1197_, 1);
        lean_inc(v_tail_1207_);
        lean_dec_ref_known(v_x_1197_, 2);
        lean_inc(v_p_1196_);
        v___f_1208_ = lean_alloc_closure(
            l_List_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1208_, 0, v_inst_1195_);
        lean_closure_set(v___f_1208_, 1, v_p_1196_);
        lean_closure_set(v___f_1208_, 2, v_tail_1207_);
        lean_closure_set(v___f_1208_, 3, v_toPure_1205_);
        v___x_1209_ = lean_apply_1(v_p_1196_, v_head_1206_);
        v___x_1210_ = lean_apply_4(
            v_toBind_1204_,
            lean_box(0),
            lean_box(0),
            v___x_1209_,
            v___f_1208_,
        );
        return v___x_1210_;
    }
}
pub unsafe fn l_List_anyM___redArg___lam__0(
    mut v_inst_1211_: *mut LeanObject,
    mut v_p_1212_: *mut LeanObject,
    mut v_tail_1213_: *mut LeanObject,
    mut v_toPure_1214_: *mut LeanObject,
    mut v_____do__lift_1215_: u8,
) -> *mut LeanObject {
    if v_____do__lift_1215_ == 0 {
        let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1214_);
        v___x_1216_ = l_List_anyM___redArg(v_inst_1211_, v_p_1212_, v_tail_1213_);
        return v___x_1216_;
    } else {
        let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_1213_);
        lean_dec(v_p_1212_);
        lean_dec_ref(v_inst_1211_);
        v___x_1217_ = lean_box((v_____do__lift_1215_) as usize);
        v___x_1218_ = lean_apply_2(v_toPure_1214_, lean_box(0), v___x_1217_);
        return v___x_1218_;
    }
}
pub unsafe fn l_List_anyM(
    mut v_m_1219_: *mut LeanObject,
    mut v_inst_1220_: *mut LeanObject,
    mut v_00_u03b1_1221_: *mut LeanObject,
    mut v_p_1222_: *mut LeanObject,
    mut v_x_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_List_anyM___redArg(v_inst_1220_, v_p_1222_, v_x_1223_);
    return v___x_1224_;
}
pub unsafe fn l_List_allM___redArg___lam__0___boxed(
    mut v_toPure_1225_: *mut LeanObject,
    mut v_inst_1226_: *mut LeanObject,
    mut v_p_1227_: *mut LeanObject,
    mut v_tail_1228_: *mut LeanObject,
    mut v_____do__lift_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_73__boxed_1230_: u8 = 0;
    let mut v_res_1231_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_73__boxed_1230_ = (lean_unbox(v_____do__lift_1229_) as u8);
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
    mut v_inst_1232_: *mut LeanObject,
    mut v_p_1233_: *mut LeanObject,
    mut v_x_1234_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1234_) == 0 {
        let mut v_toApplicative_1235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: u8 = 0;
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1235_ = lean_ctor_get(v_inst_1232_, 0);
        lean_inc_ref(v_toApplicative_1235_);
        lean_dec(v_p_1233_);
        lean_dec_ref(v_inst_1232_);
        v_toPure_1236_ = lean_ctor_get(v_toApplicative_1235_, 1);
        lean_inc(v_toPure_1236_);
        lean_dec_ref(v_toApplicative_1235_);
        v___x_1237_ = 1;
        v___x_1238_ = lean_box((v___x_1237_) as usize);
        v___x_1239_ = lean_apply_2(v_toPure_1236_, lean_box(0), v___x_1238_);
        return v___x_1239_;
    } else {
        let mut v_toApplicative_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1241_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1242_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1243_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1240_ = lean_ctor_get(v_inst_1232_, 0);
        v_toBind_1241_ = lean_ctor_get(v_inst_1232_, 1);
        lean_inc(v_toBind_1241_);
        v_toPure_1242_ = lean_ctor_get(v_toApplicative_1240_, 1);
        lean_inc(v_toPure_1242_);
        v_head_1243_ = lean_ctor_get(v_x_1234_, 0);
        lean_inc(v_head_1243_);
        v_tail_1244_ = lean_ctor_get(v_x_1234_, 1);
        lean_inc(v_tail_1244_);
        lean_dec_ref_known(v_x_1234_, 2);
        lean_inc(v_p_1233_);
        v___f_1245_ = lean_alloc_closure(
            l_List_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1245_, 0, v_toPure_1242_);
        lean_closure_set(v___f_1245_, 1, v_inst_1232_);
        lean_closure_set(v___f_1245_, 2, v_p_1233_);
        lean_closure_set(v___f_1245_, 3, v_tail_1244_);
        v___x_1246_ = lean_apply_1(v_p_1233_, v_head_1243_);
        v___x_1247_ = lean_apply_4(
            v_toBind_1241_,
            lean_box(0),
            lean_box(0),
            v___x_1246_,
            v___f_1245_,
        );
        return v___x_1247_;
    }
}
pub unsafe fn l_List_allM___redArg___lam__0(
    mut v_toPure_1248_: *mut LeanObject,
    mut v_inst_1249_: *mut LeanObject,
    mut v_p_1250_: *mut LeanObject,
    mut v_tail_1251_: *mut LeanObject,
    mut v_____do__lift_1252_: u8,
) -> *mut LeanObject {
    if v_____do__lift_1252_ == 0 {
        let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_1251_);
        lean_dec(v_p_1250_);
        lean_dec_ref(v_inst_1249_);
        v___x_1253_ = lean_box((v_____do__lift_1252_) as usize);
        v___x_1254_ = lean_apply_2(v_toPure_1248_, lean_box(0), v___x_1253_);
        return v___x_1254_;
    } else {
        let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1248_);
        v___x_1255_ = l_List_allM___redArg(v_inst_1249_, v_p_1250_, v_tail_1251_);
        return v___x_1255_;
    }
}
pub unsafe fn l_List_allM(
    mut v_m_1256_: *mut LeanObject,
    mut v_inst_1257_: *mut LeanObject,
    mut v_00_u03b1_1258_: *mut LeanObject,
    mut v_p_1259_: *mut LeanObject,
    mut v_x_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_List_allM___redArg(v_inst_1257_, v_p_1259_, v_x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_List_findM_x3f___redArg___lam__0___boxed(
    mut v_inst_1262_: *mut LeanObject,
    mut v_p_1263_: *mut LeanObject,
    mut v_tail_1264_: *mut LeanObject,
    mut v_head_1265_: *mut LeanObject,
    mut v_toPure_1266_: *mut LeanObject,
    mut v_____do__lift_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_76__boxed_1268_: u8 = 0;
    let mut v_res_1269_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_76__boxed_1268_ = (lean_unbox(v_____do__lift_1267_) as u8);
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
    mut v_inst_1270_: *mut LeanObject,
    mut v_p_1271_: *mut LeanObject,
    mut v_x_1272_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1272_) == 0 {
        let mut v_toApplicative_1273_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1273_ = lean_ctor_get(v_inst_1270_, 0);
        lean_inc_ref(v_toApplicative_1273_);
        lean_dec(v_p_1271_);
        lean_dec_ref(v_inst_1270_);
        v_toPure_1274_ = lean_ctor_get(v_toApplicative_1273_, 1);
        lean_inc(v_toPure_1274_);
        lean_dec_ref(v_toApplicative_1273_);
        v___x_1275_ = lean_box(0);
        v___x_1276_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1275_);
        return v___x_1276_;
    } else {
        let mut v_toApplicative_1277_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1278_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1279_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1280_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1277_ = lean_ctor_get(v_inst_1270_, 0);
        v_toBind_1278_ = lean_ctor_get(v_inst_1270_, 1);
        lean_inc(v_toBind_1278_);
        v_toPure_1279_ = lean_ctor_get(v_toApplicative_1277_, 1);
        lean_inc(v_toPure_1279_);
        v_head_1280_ = lean_ctor_get(v_x_1272_, 0);
        lean_inc_n(v_head_1280_, 2);
        v_tail_1281_ = lean_ctor_get(v_x_1272_, 1);
        lean_inc(v_tail_1281_);
        lean_dec_ref_known(v_x_1272_, 2);
        lean_inc(v_p_1271_);
        v___f_1282_ = lean_alloc_closure(
            l_List_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_1282_, 0, v_inst_1270_);
        lean_closure_set(v___f_1282_, 1, v_p_1271_);
        lean_closure_set(v___f_1282_, 2, v_tail_1281_);
        lean_closure_set(v___f_1282_, 3, v_head_1280_);
        lean_closure_set(v___f_1282_, 4, v_toPure_1279_);
        v___x_1283_ = lean_apply_1(v_p_1271_, v_head_1280_);
        v___x_1284_ = lean_apply_4(
            v_toBind_1278_,
            lean_box(0),
            lean_box(0),
            v___x_1283_,
            v___f_1282_,
        );
        return v___x_1284_;
    }
}
pub unsafe fn l_List_findM_x3f___redArg___lam__0(
    mut v_inst_1285_: *mut LeanObject,
    mut v_p_1286_: *mut LeanObject,
    mut v_tail_1287_: *mut LeanObject,
    mut v_head_1288_: *mut LeanObject,
    mut v_toPure_1289_: *mut LeanObject,
    mut v_____do__lift_1290_: u8,
) -> *mut LeanObject {
    if v_____do__lift_1290_ == 0 {
        let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1289_);
        lean_dec(v_head_1288_);
        v___x_1291_ = l_List_findM_x3f___redArg(v_inst_1285_, v_p_1286_, v_tail_1287_);
        return v___x_1291_;
    } else {
        let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_1287_);
        lean_dec(v_p_1286_);
        lean_dec_ref(v_inst_1285_);
        v___x_1292_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1292_, 0, v_head_1288_);
        v___x_1293_ = lean_apply_2(v_toPure_1289_, lean_box(0), v___x_1292_);
        return v___x_1293_;
    }
}
pub unsafe fn l_List_findM_x3f(
    mut v_m_1294_: *mut LeanObject,
    mut v_inst_1295_: *mut LeanObject,
    mut v_00_u03b1_1296_: *mut LeanObject,
    mut v_p_1297_: *mut LeanObject,
    mut v_x_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_List_findM_x3f___redArg(v_inst_1295_, v_p_1297_, v_x_1298_);
    return v___x_1299_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(
    mut v_x_1300_: *mut LeanObject,
    mut v_h__1_1301_: *mut LeanObject,
    mut v_h__2_1302_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1300_) == 0 {
        let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1302_);
        v___x_1303_ = lean_box(0);
        v___x_1304_ = lean_apply_1(v_h__1_1301_, v___x_1303_);
        return v___x_1304_;
    } else {
        let mut v_head_1305_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1301_);
        v_head_1305_ = lean_ctor_get(v_x_1300_, 0);
        lean_inc(v_head_1305_);
        v_tail_1306_ = lean_ctor_get(v_x_1300_, 1);
        lean_inc(v_tail_1306_);
        lean_dec_ref_known(v_x_1300_, 2);
        v___x_1307_ = lean_apply_2(v_h__2_1302_, v_head_1305_, v_tail_1306_);
        return v___x_1307_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter(
    mut v_00_u03b1_1308_: *mut LeanObject,
    mut v_motive_1309_: *mut LeanObject,
    mut v_x_1310_: *mut LeanObject,
    mut v_h__1_1311_: *mut LeanObject,
    mut v_h__2_1312_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1310_) == 0 {
        let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1312_);
        v___x_1313_ = lean_box(0);
        v___x_1314_ = lean_apply_1(v_h__1_1311_, v___x_1313_);
        return v___x_1314_;
    } else {
        let mut v_head_1315_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1311_);
        v_head_1315_ = lean_ctor_get(v_x_1310_, 0);
        lean_inc(v_head_1315_);
        v_tail_1316_ = lean_ctor_get(v_x_1310_, 1);
        lean_inc(v_tail_1316_);
        lean_dec_ref_known(v_x_1310_, 2);
        v___x_1317_ = lean_apply_2(v_h__2_1312_, v_head_1315_, v_tail_1316_);
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_1318_: u8,
    mut v_h__1_1319_: *mut LeanObject,
    mut v_h__2_1320_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_1318_ == 0 {
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1319_);
        v___x_1321_ = lean_box(0);
        v___x_1322_ = lean_apply_1(v_h__2_1320_, v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1320_);
        v___x_1323_ = lean_box(0);
        v___x_1324_ = lean_apply_1(v_h__1_1319_, v___x_1323_);
        return v___x_1324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_1325_: *mut LeanObject,
    mut v_h__1_1326_: *mut LeanObject,
    mut v_h__2_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_26__boxed_1328_: u8 = 0;
    let mut v_res_1329_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_1328_ = (lean_unbox(v_____do__lift_1325_) as u8);
    v_res_1329_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_1328_,
        v_h__1_1326_,
        v_h__2_1327_,
    );
    return v_res_1329_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(
    mut v_motive_1330_: *mut LeanObject,
    mut v_____do__lift_1331_: u8,
    mut v_h__1_1332_: *mut LeanObject,
    mut v_h__2_1333_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_1331_ == 0 {
        let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1332_);
        v___x_1334_ = lean_box(0);
        v___x_1335_ = lean_apply_1(v_h__2_1333_, v___x_1334_);
        return v___x_1335_;
    } else {
        let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1333_);
        v___x_1336_ = lean_box(0);
        v___x_1337_ = lean_apply_1(v_h__1_1332_, v___x_1336_);
        return v___x_1337_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_1338_: *mut LeanObject,
    mut v_____do__lift_1339_: *mut LeanObject,
    mut v_h__1_1340_: *mut LeanObject,
    mut v_h__2_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_37__boxed_1342_: u8 = 0;
    let mut v_res_1343_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_1342_ = (lean_unbox(v_____do__lift_1339_) as u8);
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
    mut v_h__1_1345_: *mut LeanObject,
    mut v_h__2_1346_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1344_ == 0 {
        let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1345_);
        v___x_1347_ = lean_box(0);
        v___x_1348_ = lean_apply_1(v_h__2_1346_, v___x_1347_);
        return v___x_1348_;
    } else {
        let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1346_);
        v___x_1349_ = lean_box(0);
        v___x_1350_ = lean_apply_1(v_h__1_1345_, v___x_1349_);
        return v___x_1350_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1351_: *mut LeanObject,
    mut v_h__1_1352_: *mut LeanObject,
    mut v_h__2_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1354_: u8 = 0;
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1354_ = (lean_unbox(v_x_1351_) as u8);
    v_res_1355_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_1354_,
        v_h__1_1352_,
        v_h__2_1353_,
    );
    return v_res_1355_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(
    mut v_motive_1356_: *mut LeanObject,
    mut v_x_1357_: u8,
    mut v_h__1_1358_: *mut LeanObject,
    mut v_h__2_1359_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1357_ == 0 {
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1358_);
        v___x_1360_ = lean_box(0);
        v___x_1361_ = lean_apply_1(v_h__2_1359_, v___x_1360_);
        return v___x_1361_;
    } else {
        let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1359_);
        v___x_1362_ = lean_box(0);
        v___x_1363_ = lean_apply_1(v_h__1_1358_, v___x_1362_);
        return v___x_1363_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1364_: *mut LeanObject,
    mut v_x_1365_: *mut LeanObject,
    mut v_h__1_1366_: *mut LeanObject,
    mut v_h__2_1367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1368_ = (lean_unbox(v_x_1365_) as u8);
    v_res_1369_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(
        v_motive_1364_,
        v_x_37__boxed_1368_,
        v_h__1_1366_,
        v_h__2_1367_,
    );
    return v_res_1369_;
}
pub unsafe fn l_List_findSomeM_x3f___redArg(
    mut v_inst_1370_: *mut LeanObject,
    mut v_f_1371_: *mut LeanObject,
    mut v_x_1372_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1372_) == 0 {
        let mut v_toApplicative_1373_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1373_ = lean_ctor_get(v_inst_1370_, 0);
        lean_inc_ref(v_toApplicative_1373_);
        lean_dec(v_f_1371_);
        lean_dec_ref(v_inst_1370_);
        v_toPure_1374_ = lean_ctor_get(v_toApplicative_1373_, 1);
        lean_inc(v_toPure_1374_);
        lean_dec_ref(v_toApplicative_1373_);
        v___x_1375_ = lean_box(0);
        v___x_1376_ = lean_apply_2(v_toPure_1374_, lean_box(0), v___x_1375_);
        return v___x_1376_;
    } else {
        let mut v_toApplicative_1377_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1378_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1380_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1377_ = lean_ctor_get(v_inst_1370_, 0);
        v_toBind_1378_ = lean_ctor_get(v_inst_1370_, 1);
        lean_inc(v_toBind_1378_);
        v_toPure_1379_ = lean_ctor_get(v_toApplicative_1377_, 1);
        lean_inc(v_toPure_1379_);
        v_head_1380_ = lean_ctor_get(v_x_1372_, 0);
        lean_inc(v_head_1380_);
        v_tail_1381_ = lean_ctor_get(v_x_1372_, 1);
        lean_inc(v_tail_1381_);
        lean_dec_ref_known(v_x_1372_, 2);
        lean_inc(v_f_1371_);
        v___f_1382_ = lean_alloc_closure(
            l_List_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1382_, 0, v_inst_1370_);
        lean_closure_set(v___f_1382_, 1, v_f_1371_);
        lean_closure_set(v___f_1382_, 2, v_tail_1381_);
        lean_closure_set(v___f_1382_, 3, v_toPure_1379_);
        v___x_1383_ = lean_apply_1(v_f_1371_, v_head_1380_);
        v___x_1384_ = lean_apply_4(
            v_toBind_1378_,
            lean_box(0),
            lean_box(0),
            v___x_1383_,
            v___f_1382_,
        );
        return v___x_1384_;
    }
}
pub unsafe fn l_List_findSomeM_x3f___redArg___lam__0(
    mut v_inst_1385_: *mut LeanObject,
    mut v_f_1386_: *mut LeanObject,
    mut v_tail_1387_: *mut LeanObject,
    mut v_toPure_1388_: *mut LeanObject,
    mut v_____do__lift_1389_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1389_) == 0 {
        let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1388_);
        v___x_1390_ = l_List_findSomeM_x3f___redArg(v_inst_1385_, v_f_1386_, v_tail_1387_);
        return v___x_1390_;
    } else {
        let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_1387_);
        lean_dec(v_f_1386_);
        lean_dec_ref(v_inst_1385_);
        v___x_1391_ = lean_apply_2(v_toPure_1388_, lean_box(0), v_____do__lift_1389_);
        return v___x_1391_;
    }
}
pub unsafe fn l_List_findSomeM_x3f(
    mut v_m_1392_: *mut LeanObject,
    mut v_inst_1393_: *mut LeanObject,
    mut v_00_u03b1_1394_: *mut LeanObject,
    mut v_00_u03b2_1395_: *mut LeanObject,
    mut v_f_1396_: *mut LeanObject,
    mut v_x_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_List_findSomeM_x3f___redArg(v_inst_1393_, v_f_1396_, v_x_1397_);
    return v___x_1398_;
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(
    mut v_x_1399_: *mut LeanObject,
    mut v_h__1_1400_: *mut LeanObject,
    mut v_h__2_1401_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1399_) == 0 {
        let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1401_);
        v___x_1402_ = lean_box(0);
        v___x_1403_ = lean_apply_1(v_h__1_1400_, v___x_1402_);
        return v___x_1403_;
    } else {
        let mut v_head_1404_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1400_);
        v_head_1404_ = lean_ctor_get(v_x_1399_, 0);
        lean_inc(v_head_1404_);
        v_tail_1405_ = lean_ctor_get(v_x_1399_, 1);
        lean_inc(v_tail_1405_);
        lean_dec_ref_known(v_x_1399_, 2);
        v___x_1406_ = lean_apply_2(v_h__2_1401_, v_head_1404_, v_tail_1405_);
        return v___x_1406_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_1407_: *mut LeanObject,
    mut v_motive_1408_: *mut LeanObject,
    mut v_x_1409_: *mut LeanObject,
    mut v_h__1_1410_: *mut LeanObject,
    mut v_h__2_1411_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1409_) == 0 {
        let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1411_);
        v___x_1412_ = lean_box(0);
        v___x_1413_ = lean_apply_1(v_h__1_1410_, v___x_1412_);
        return v___x_1413_;
    } else {
        let mut v_head_1414_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1410_);
        v_head_1414_ = lean_ctor_get(v_x_1409_, 0);
        lean_inc(v_head_1414_);
        v_tail_1415_ = lean_ctor_get(v_x_1409_, 1);
        lean_inc(v_tail_1415_);
        lean_dec_ref_known(v_x_1409_, 2);
        v___x_1416_ = lean_apply_2(v_h__2_1411_, v_head_1414_, v_tail_1415_);
        return v___x_1416_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_1417_: *mut LeanObject,
    mut v_h__1_1418_: *mut LeanObject,
    mut v_h__2_1419_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1417_) == 0 {
        let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1418_);
        v___x_1420_ = lean_box(0);
        v___x_1421_ = lean_apply_1(v_h__2_1419_, v___x_1420_);
        return v___x_1421_;
    } else {
        let mut v_val_1422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1419_);
        v_val_1422_ = lean_ctor_get(v_____do__lift_1417_, 0);
        lean_inc(v_val_1422_);
        lean_dec_ref_known(v_____do__lift_1417_, 1);
        v___x_1423_ = lean_apply_1(v_h__1_1418_, v_val_1422_);
        return v___x_1423_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_1424_: *mut LeanObject,
    mut v_motive_1425_: *mut LeanObject,
    mut v_____do__lift_1426_: *mut LeanObject,
    mut v_h__1_1427_: *mut LeanObject,
    mut v_h__2_1428_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1426_) == 0 {
        let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1427_);
        v___x_1429_ = lean_box(0);
        v___x_1430_ = lean_apply_1(v_h__2_1428_, v___x_1429_);
        return v___x_1430_;
    } else {
        let mut v_val_1431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1428_);
        v_val_1431_ = lean_ctor_get(v_____do__lift_1426_, 0);
        lean_inc(v_val_1431_);
        lean_dec_ref_known(v_____do__lift_1426_, 1);
        v___x_1432_ = lean_apply_1(v_h__1_1427_, v_val_1431_);
        return v___x_1432_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_1433_: *mut LeanObject,
    mut v_h__1_1434_: *mut LeanObject,
    mut v_h__2_1435_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1433_) == 0 {
        let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1435_);
        v___x_1436_ = lean_box(0);
        v___x_1437_ = lean_apply_1(v_h__1_1434_, v___x_1436_);
        return v___x_1437_;
    } else {
        let mut v_head_1438_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1434_);
        v_head_1438_ = lean_ctor_get(v_x_1433_, 0);
        lean_inc(v_head_1438_);
        v_tail_1439_ = lean_ctor_get(v_x_1433_, 1);
        lean_inc(v_tail_1439_);
        lean_dec_ref_known(v_x_1433_, 2);
        v___x_1440_ = lean_apply_2(v_h__2_1435_, v_head_1438_, v_tail_1439_);
        return v___x_1440_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_1441_: *mut LeanObject,
    mut v_motive_1442_: *mut LeanObject,
    mut v_x_1443_: *mut LeanObject,
    mut v_h__1_1444_: *mut LeanObject,
    mut v_h__2_1445_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1443_) == 0 {
        let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1445_);
        v___x_1446_ = lean_box(0);
        v___x_1447_ = lean_apply_1(v_h__1_1444_, v___x_1446_);
        return v___x_1447_;
    } else {
        let mut v_head_1448_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1444_);
        v_head_1448_ = lean_ctor_get(v_x_1443_, 0);
        lean_inc(v_head_1448_);
        v_tail_1449_ = lean_ctor_get(v_x_1443_, 1);
        lean_inc(v_tail_1449_);
        lean_dec_ref_known(v_x_1443_, 2);
        v___x_1450_ = lean_apply_2(v_h__2_1445_, v_head_1448_, v_tail_1449_);
        return v___x_1450_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_1451_: *mut LeanObject,
    mut v_h__1_1452_: *mut LeanObject,
    mut v_h__2_1453_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1451_) == 0 {
        let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1452_);
        v___x_1454_ = lean_box(0);
        v___x_1455_ = lean_apply_1(v_h__2_1453_, v___x_1454_);
        return v___x_1455_;
    } else {
        let mut v_val_1456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1453_);
        v_val_1456_ = lean_ctor_get(v_x_1451_, 0);
        lean_inc(v_val_1456_);
        lean_dec_ref_known(v_x_1451_, 1);
        v___x_1457_ = lean_apply_1(v_h__1_1452_, v_val_1456_);
        return v___x_1457_;
    }
}
pub unsafe fn l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_1458_: *mut LeanObject,
    mut v_motive_1459_: *mut LeanObject,
    mut v_x_1460_: *mut LeanObject,
    mut v_h__1_1461_: *mut LeanObject,
    mut v_h__2_1462_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1460_) == 0 {
        let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1461_);
        v___x_1463_ = lean_box(0);
        v___x_1464_ = lean_apply_1(v_h__2_1462_, v___x_1463_);
        return v___x_1464_;
    } else {
        let mut v_val_1465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1462_);
        v_val_1465_ = lean_ctor_get(v_x_1460_, 0);
        lean_inc(v_val_1465_);
        lean_dec_ref_known(v_x_1460_, 1);
        v___x_1466_ = lean_apply_1(v_h__1_1461_, v_val_1465_);
        return v___x_1466_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___lam__0___boxed(
    mut v_toPure_1467_: *mut LeanObject,
    mut v_inst_1468_: *mut LeanObject,
    mut v_f_1469_: *mut LeanObject,
    mut v_tail_1470_: *mut LeanObject,
    mut v_____do__lift_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1472_: *mut LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_List_forIn_x27_loop___redArg___lam__0(
        v_toPure_1467_,
        v_inst_1468_,
        v_f_1469_,
        v_tail_1470_,
        v_____do__lift_1471_,
    );
    lean_dec(v_tail_1470_);
    return v_res_1472_;
}
pub unsafe fn l_List_forIn_x27_loop___redArg(
    mut v_inst_1473_: *mut LeanObject,
    mut v_f_1474_: *mut LeanObject,
    mut v_as_x27_1475_: *mut LeanObject,
    mut v_b_1476_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_as_x27_1475_) == 0 {
        let mut v_toApplicative_1477_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1477_ = lean_ctor_get(v_inst_1473_, 0);
        lean_inc_ref(v_toApplicative_1477_);
        lean_dec(v_f_1474_);
        lean_dec_ref(v_inst_1473_);
        v_toPure_1478_ = lean_ctor_get(v_toApplicative_1477_, 1);
        lean_inc(v_toPure_1478_);
        lean_dec_ref(v_toApplicative_1477_);
        v___x_1479_ = lean_apply_2(v_toPure_1478_, lean_box(0), v_b_1476_);
        return v___x_1479_;
    } else {
        let mut v_toApplicative_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1481_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1483_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1480_ = lean_ctor_get(v_inst_1473_, 0);
        v_toBind_1481_ = lean_ctor_get(v_inst_1473_, 1);
        lean_inc(v_toBind_1481_);
        v_toPure_1482_ = lean_ctor_get(v_toApplicative_1480_, 1);
        lean_inc(v_toPure_1482_);
        v_head_1483_ = lean_ctor_get(v_as_x27_1475_, 0);
        v_tail_1484_ = lean_ctor_get(v_as_x27_1475_, 1);
        lean_inc(v_tail_1484_);
        lean_inc(v_f_1474_);
        v___f_1485_ = lean_alloc_closure(
            l_List_forIn_x27_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1485_, 0, v_toPure_1482_);
        lean_closure_set(v___f_1485_, 1, v_inst_1473_);
        lean_closure_set(v___f_1485_, 2, v_f_1474_);
        lean_closure_set(v___f_1485_, 3, v_tail_1484_);
        lean_inc(v_head_1483_);
        v___x_1486_ = lean_apply_3(v_f_1474_, v_head_1483_, lean_box(0), v_b_1476_);
        v___x_1487_ = lean_apply_4(
            v_toBind_1481_,
            lean_box(0),
            lean_box(0),
            v___x_1486_,
            v___f_1485_,
        );
        return v___x_1487_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___lam__0(
    mut v_toPure_1488_: *mut LeanObject,
    mut v_inst_1489_: *mut LeanObject,
    mut v_f_1490_: *mut LeanObject,
    mut v_tail_1491_: *mut LeanObject,
    mut v_____do__lift_1492_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1492_) == 0 {
        let mut v_a_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1490_);
        lean_dec_ref(v_inst_1489_);
        v_a_1493_ = lean_ctor_get(v_____do__lift_1492_, 0);
        lean_inc(v_a_1493_);
        lean_dec_ref_known(v_____do__lift_1492_, 1);
        v___x_1494_ = lean_apply_2(v_toPure_1488_, lean_box(0), v_a_1493_);
        return v___x_1494_;
    } else {
        let mut v_a_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1488_);
        v_a_1495_ = lean_ctor_get(v_____do__lift_1492_, 0);
        lean_inc(v_a_1495_);
        lean_dec_ref_known(v_____do__lift_1492_, 1);
        v___x_1496_ =
            l_List_forIn_x27_loop___redArg(v_inst_1489_, v_f_1490_, v_tail_1491_, v_a_1495_);
        return v___x_1496_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___redArg___boxed(
    mut v_inst_1497_: *mut LeanObject,
    mut v_f_1498_: *mut LeanObject,
    mut v_as_x27_1499_: *mut LeanObject,
    mut v_b_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ =
        l_List_forIn_x27_loop___redArg(v_inst_1497_, v_f_1498_, v_as_x27_1499_, v_b_1500_);
    lean_dec(v_as_x27_1499_);
    return v_res_1501_;
}
pub unsafe fn l_List_forIn_x27_loop(
    mut v_00_u03b1_1502_: *mut LeanObject,
    mut v_00_u03b2_1503_: *mut LeanObject,
    mut v_m_1504_: *mut LeanObject,
    mut v_inst_1505_: *mut LeanObject,
    mut v_as_1506_: *mut LeanObject,
    mut v_f_1507_: *mut LeanObject,
    mut v_as_x27_1508_: *mut LeanObject,
    mut v_b_1509_: *mut LeanObject,
    mut v_a_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    v___x_1511_ =
        l_List_forIn_x27_loop___redArg(v_inst_1505_, v_f_1507_, v_as_x27_1508_, v_b_1509_);
    return v___x_1511_;
}
pub unsafe fn l_List_forIn_x27_loop___boxed(
    mut v_00_u03b1_1512_: *mut LeanObject,
    mut v_00_u03b2_1513_: *mut LeanObject,
    mut v_m_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
    mut v_as_1516_: *mut LeanObject,
    mut v_f_1517_: *mut LeanObject,
    mut v_as_x27_1518_: *mut LeanObject,
    mut v_b_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1521_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_as_x27_1518_);
    lean_dec(v_as_1516_);
    return v_res_1521_;
}
pub unsafe fn l_List_forIn_x27___redArg(
    mut v_inst_1522_: *mut LeanObject,
    mut v_as_1523_: *mut LeanObject,
    mut v_init_1524_: *mut LeanObject,
    mut v_f_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    v___x_1526_ = l_List_forIn_x27_loop___redArg(v_inst_1522_, v_f_1525_, v_as_1523_, v_init_1524_);
    return v___x_1526_;
}
pub unsafe fn l_List_forIn_x27___redArg___boxed(
    mut v_inst_1527_: *mut LeanObject,
    mut v_as_1528_: *mut LeanObject,
    mut v_init_1529_: *mut LeanObject,
    mut v_f_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1531_: *mut LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_List_forIn_x27___redArg(v_inst_1527_, v_as_1528_, v_init_1529_, v_f_1530_);
    lean_dec(v_as_1528_);
    return v_res_1531_;
}
pub unsafe fn l_List_forIn_x27(
    mut v_00_u03b1_1532_: *mut LeanObject,
    mut v_00_u03b2_1533_: *mut LeanObject,
    mut v_m_1534_: *mut LeanObject,
    mut v_inst_1535_: *mut LeanObject,
    mut v_as_1536_: *mut LeanObject,
    mut v_init_1537_: *mut LeanObject,
    mut v_f_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_List_forIn_x27_loop___redArg(v_inst_1535_, v_f_1538_, v_as_1536_, v_init_1537_);
    return v___x_1539_;
}
pub unsafe fn l_List_forIn_x27___boxed(
    mut v_00_u03b1_1540_: *mut LeanObject,
    mut v_00_u03b2_1541_: *mut LeanObject,
    mut v_m_1542_: *mut LeanObject,
    mut v_inst_1543_: *mut LeanObject,
    mut v_as_1544_: *mut LeanObject,
    mut v_init_1545_: *mut LeanObject,
    mut v_f_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1547_: *mut LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_List_forIn_x27(
        v_00_u03b1_1540_,
        v_00_u03b2_1541_,
        v_m_1542_,
        v_inst_1543_,
        v_as_1544_,
        v_init_1545_,
        v_f_1546_,
    );
    lean_dec(v_as_1544_);
    return v_res_1547_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_inst_1548_: *mut LeanObject,
    mut v_00_u03b2_1549_: *mut LeanObject,
    mut v___y_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1553_ =
        l_List_forIn_x27_loop___redArg(v_inst_1548_, v___y_1552_, v___y_1550_, v___y_1551_);
    return v___x_1553_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(
    mut v_inst_1554_: *mut LeanObject,
    mut v_00_u03b2_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1559_: *mut LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
        v_inst_1554_,
        v_00_u03b2_1555_,
        v___y_1556_,
        v___y_1557_,
        v___y_1558_,
    );
    lean_dec(v___y_1556_);
    return v_res_1559_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(
    mut v_inst_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1561_: *mut LeanObject = core::ptr::null_mut();
    v___f_1561_ = lean_alloc_closure(
        l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1561_, 0, v_inst_1560_);
    return v___f_1561_;
}
pub unsafe fn l_List_instForIn_x27InferInstanceMembershipOfMonad(
    mut v_m_1562_: *mut LeanObject,
    mut v_00_u03b1_1563_: *mut LeanObject,
    mut v_inst_1564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1565_: *mut LeanObject = core::ptr::null_mut();
    v___f_1565_ = lean_alloc_closure(
        l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1565_, 0, v_inst_1564_);
    return v___f_1565_;
}
pub unsafe fn l_List_instForMOfMonad___redArg(
    mut v_inst_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1567_ = lean_alloc_closure(l_List_forM as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1567_, 0, lean_box(0));
    lean_closure_set(v___x_1567_, 1, v_inst_1566_);
    lean_closure_set(v___x_1567_, 2, lean_box(0));
    return v___x_1567_;
}
pub unsafe fn l_List_instForMOfMonad(
    mut v_m_1568_: *mut LeanObject,
    mut v_00_u03b1_1569_: *mut LeanObject,
    mut v_inst_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1571_ = lean_alloc_closure(l_List_forM as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1571_, 0, lean_box(0));
    lean_closure_set(v___x_1571_, 1, v_inst_1570_);
    lean_closure_set(v___x_1571_, 2, lean_box(0));
    return v___x_1571_;
}
pub unsafe fn l_List_instFunctor___lam__0(
    mut v_00_u03b1_1572_: *mut LeanObject,
    mut v_00_u03b2_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1576_, 0, lean_box(0));
    lean_closure_set(v___x_1576_, 1, lean_box(0));
    lean_closure_set(v___x_1576_, 2, v___y_1574_);
    v___x_1577_ = lean_box(0);
    v___x_1578_ = l_List_mapTR_loop___redArg(v___x_1576_, v___y_1575_, v___x_1577_);
    return v___x_1578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Control(builtin);
}
