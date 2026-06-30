// Lean compiler output
// Module: Init.Control.StateRef
// Imports: Init.System.ST Init.Control.Reader
use crate::r#gen::Init::Control::Reader::{
    initialize_Init_Control_Reader, runtime_initialize_Init_Control_Reader,
};
use crate::r#gen::Init::System::ST::{
    initialize_Init_System_ST, l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed,
    l_ST_Prim_Ref_set___boxed, l_ST_Prim_mkRef___boxed, runtime_initialize_Init_System_ST,
};
pub static l_StateRefT_x27_instMonadLift___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadLift___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadLift___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_StateRefT_x27_instMonadFunctor___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadFunctor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadFunctor___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value:
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
    m_fun: l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__1_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__3___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_StateRefT_x27_run___redArg___lam__0(
    mut v_a_784_: *mut leanh::LeanObject,
    mut v_toPure_785_: *mut leanh::LeanObject,
    mut v_s_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_787_, 0, v_a_784_);
    leanh::lean_ctor_set(v___x_787_, 1, v_s_786_);
    v___x_788_ = leanh::lean_apply_2(v_toPure_785_, leanh::lean_box(0), v___x_787_);
    return v___x_788_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__1(
    mut v_toPure_789_: *mut leanh::LeanObject,
    mut v_ref_790_: *mut leanh::LeanObject,
    mut v_inst_791_: *mut leanh::LeanObject,
    mut v_toBind_792_: *mut leanh::LeanObject,
    mut v_a_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_794_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_794_, 0, v_a_793_);
    leanh::lean_closure_set(v___f_794_, 1, v_toPure_789_);
    v___x_795_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_795_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_795_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_795_, 2, v_ref_790_);
    v___x_796_ = leanh::lean_apply_2(v_inst_791_, leanh::lean_box(0), v___x_795_);
    v___x_797_ = leanh::lean_apply_4(
        v_toBind_792_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_796_,
        v___f_794_,
    );
    return v___x_797_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__2(
    mut v_toPure_798_: *mut leanh::LeanObject,
    mut v_inst_799_: *mut leanh::LeanObject,
    mut v_toBind_800_: *mut leanh::LeanObject,
    mut v_x_801_: *mut leanh::LeanObject,
    mut v_ref_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_800_);
    leanh::lean_inc(v_ref_802_);
    v___f_803_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_803_, 0, v_toPure_798_);
    leanh::lean_closure_set(v___f_803_, 1, v_ref_802_);
    leanh::lean_closure_set(v___f_803_, 2, v_inst_799_);
    leanh::lean_closure_set(v___f_803_, 3, v_toBind_800_);
    v___x_804_ = leanh::lean_apply_1(v_x_801_, v_ref_802_);
    v___x_805_ = leanh::lean_apply_4(
        v_toBind_800_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_804_,
        v___f_803_,
    );
    return v___x_805_;
}
pub unsafe fn l_StateRefT_x27_run___redArg(
    mut v_inst_806_: *mut leanh::LeanObject,
    mut v_inst_807_: *mut leanh::LeanObject,
    mut v_x_808_: *mut leanh::LeanObject,
    mut v_s_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_810_ = leanh::lean_ctor_get(v_inst_806_, 0);
    leanh::lean_inc_ref(v_toApplicative_810_);
    v_toBind_811_ = leanh::lean_ctor_get(v_inst_806_, 1);
    leanh::lean_inc_n(v_toBind_811_, 2);
    leanh::lean_dec_ref(v_inst_806_);
    v_toPure_812_ = leanh::lean_ctor_get(v_toApplicative_810_, 1);
    leanh::lean_inc(v_toPure_812_);
    leanh::lean_dec_ref(v_toApplicative_810_);
    v___x_813_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_813_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_813_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_813_, 2, v_s_809_);
    leanh::lean_inc(v_inst_807_);
    v___x_814_ = leanh::lean_apply_2(v_inst_807_, leanh::lean_box(0), v___x_813_);
    v___f_815_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_815_, 0, v_toPure_812_);
    leanh::lean_closure_set(v___f_815_, 1, v_inst_807_);
    leanh::lean_closure_set(v___f_815_, 2, v_toBind_811_);
    leanh::lean_closure_set(v___f_815_, 3, v_x_808_);
    v___x_816_ = leanh::lean_apply_4(
        v_toBind_811_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_814_,
        v___f_815_,
    );
    return v___x_816_;
}
pub unsafe fn l_StateRefT_x27_run(
    mut v_00_u03c9_817_: *mut leanh::LeanObject,
    mut v_00_u03c3_818_: *mut leanh::LeanObject,
    mut v_m_819_: *mut leanh::LeanObject,
    mut v_inst_820_: *mut leanh::LeanObject,
    mut v_inst_821_: *mut leanh::LeanObject,
    mut v_00_u03b1_822_: *mut leanh::LeanObject,
    mut v_x_823_: *mut leanh::LeanObject,
    mut v_s_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_825_ = leanh::lean_ctor_get(v_inst_820_, 0);
    leanh::lean_inc_ref(v_toApplicative_825_);
    v_toBind_826_ = leanh::lean_ctor_get(v_inst_820_, 1);
    leanh::lean_inc_n(v_toBind_826_, 2);
    leanh::lean_dec_ref(v_inst_820_);
    v_toPure_827_ = leanh::lean_ctor_get(v_toApplicative_825_, 1);
    leanh::lean_inc(v_toPure_827_);
    leanh::lean_dec_ref(v_toApplicative_825_);
    v___x_828_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_828_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_828_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_828_, 2, v_s_824_);
    leanh::lean_inc(v_inst_821_);
    v___x_829_ = leanh::lean_apply_2(v_inst_821_, leanh::lean_box(0), v___x_828_);
    v___f_830_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_830_, 0, v_toPure_827_);
    leanh::lean_closure_set(v___f_830_, 1, v_inst_821_);
    leanh::lean_closure_set(v___f_830_, 2, v_toBind_826_);
    leanh::lean_closure_set(v___f_830_, 3, v_x_823_);
    v___x_831_ = leanh::lean_apply_4(
        v_toBind_826_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_829_,
        v___f_830_,
    );
    return v___x_831_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg___lam__0(
    mut v_toPure_832_: *mut leanh::LeanObject,
    mut v_____x_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_834_ = leanh::lean_ctor_get(v_____x_833_, 0);
    leanh::lean_inc(v_fst_834_);
    leanh::lean_dec_ref(v_____x_833_);
    v___x_835_ = leanh::lean_apply_2(v_toPure_832_, leanh::lean_box(0), v_fst_834_);
    return v___x_835_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg(
    mut v_inst_836_: *mut leanh::LeanObject,
    mut v_inst_837_: *mut leanh::LeanObject,
    mut v_x_838_: *mut leanh::LeanObject,
    mut v_s_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_840_ = leanh::lean_ctor_get(v_inst_836_, 0);
    leanh::lean_inc_ref(v_toApplicative_840_);
    v_toBind_841_ = leanh::lean_ctor_get(v_inst_836_, 1);
    leanh::lean_inc_n(v_toBind_841_, 3);
    leanh::lean_dec_ref(v_inst_836_);
    v_toPure_842_ = leanh::lean_ctor_get(v_toApplicative_840_, 1);
    leanh::lean_inc_n(v_toPure_842_, 2);
    leanh::lean_dec_ref(v_toApplicative_840_);
    v___x_843_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_843_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_843_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_843_, 2, v_s_839_);
    leanh::lean_inc(v_inst_837_);
    v___x_844_ = leanh::lean_apply_2(v_inst_837_, leanh::lean_box(0), v___x_843_);
    v___f_845_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_845_, 0, v_toPure_842_);
    v___f_846_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_846_, 0, v_toPure_842_);
    leanh::lean_closure_set(v___f_846_, 1, v_inst_837_);
    leanh::lean_closure_set(v___f_846_, 2, v_toBind_841_);
    leanh::lean_closure_set(v___f_846_, 3, v_x_838_);
    v___x_847_ = leanh::lean_apply_4(
        v_toBind_841_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_844_,
        v___f_846_,
    );
    v___x_848_ = leanh::lean_apply_4(
        v_toBind_841_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_847_,
        v___f_845_,
    );
    return v___x_848_;
}
pub unsafe fn l_StateRefT_x27_run_x27(
    mut v_00_u03c9_849_: *mut leanh::LeanObject,
    mut v_00_u03c3_850_: *mut leanh::LeanObject,
    mut v_m_851_: *mut leanh::LeanObject,
    mut v_inst_852_: *mut leanh::LeanObject,
    mut v_inst_853_: *mut leanh::LeanObject,
    mut v_00_u03b1_854_: *mut leanh::LeanObject,
    mut v_x_855_: *mut leanh::LeanObject,
    mut v_s_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_857_ = leanh::lean_ctor_get(v_inst_852_, 0);
    leanh::lean_inc_ref(v_toApplicative_857_);
    v_toBind_858_ = leanh::lean_ctor_get(v_inst_852_, 1);
    leanh::lean_inc_n(v_toBind_858_, 3);
    leanh::lean_dec_ref(v_inst_852_);
    v_toPure_859_ = leanh::lean_ctor_get(v_toApplicative_857_, 1);
    leanh::lean_inc_n(v_toPure_859_, 2);
    leanh::lean_dec_ref(v_toApplicative_857_);
    v___x_860_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_860_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_860_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_860_, 2, v_s_856_);
    leanh::lean_inc(v_inst_853_);
    v___x_861_ = leanh::lean_apply_2(v_inst_853_, leanh::lean_box(0), v___x_860_);
    v___f_862_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_862_, 0, v_toPure_859_);
    v___f_863_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_863_, 0, v_toPure_859_);
    leanh::lean_closure_set(v___f_863_, 1, v_inst_853_);
    leanh::lean_closure_set(v___f_863_, 2, v_toBind_858_);
    leanh::lean_closure_set(v___f_863_, 3, v_x_855_);
    v___x_864_ = leanh::lean_apply_4(
        v_toBind_858_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_861_,
        v___f_863_,
    );
    v___x_865_ = leanh::lean_apply_4(
        v_toBind_858_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_864_,
        v___f_862_,
    );
    return v___x_865_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg(
    mut v_x_866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_866_);
    return v_x_866_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg___boxed(
    mut v_x_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_868_ = l_StateRefT_x27_lift___redArg(v_x_867_);
    leanh::lean_dec(v_x_867_);
    return v_res_868_;
}
pub unsafe fn l_StateRefT_x27_lift(
    mut v_00_u03c9_869_: *mut leanh::LeanObject,
    mut v_00_u03c3_870_: *mut leanh::LeanObject,
    mut v_m_871_: *mut leanh::LeanObject,
    mut v_00_u03b1_872_: *mut leanh::LeanObject,
    mut v_x_873_: *mut leanh::LeanObject,
    mut v_x_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_873_);
    return v_x_873_;
}
pub unsafe fn l_StateRefT_x27_lift___boxed(
    mut v_00_u03c9_875_: *mut leanh::LeanObject,
    mut v_00_u03c3_876_: *mut leanh::LeanObject,
    mut v_m_877_: *mut leanh::LeanObject,
    mut v_00_u03b1_878_: *mut leanh::LeanObject,
    mut v_x_879_: *mut leanh::LeanObject,
    mut v_x_880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_StateRefT_x27_lift(
        v_00_u03c9_875_,
        v_00_u03c3_876_,
        v_m_877_,
        v_00_u03b1_878_,
        v_x_879_,
        v_x_880_,
    );
    leanh::lean_dec(v_x_880_);
    leanh::lean_dec(v_x_879_);
    return v_res_881_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg(
    mut v_inst_882_: *mut leanh::LeanObject,
    mut v_f_883_: *mut leanh::LeanObject,
    mut v_x_884_: *mut leanh::LeanObject,
    mut v_r_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_886_ = leanh::lean_ctor_get(v_inst_882_, 0);
    leanh::lean_inc_ref(v_toApplicative_886_);
    leanh::lean_dec_ref(v_inst_882_);
    v_toFunctor_887_ = leanh::lean_ctor_get(v_toApplicative_886_, 0);
    leanh::lean_inc_ref(v_toFunctor_887_);
    leanh::lean_dec_ref(v_toApplicative_886_);
    v_map_888_ = leanh::lean_ctor_get(v_toFunctor_887_, 0);
    leanh::lean_inc(v_map_888_);
    leanh::lean_dec_ref(v_toFunctor_887_);
    leanh::lean_inc(v_r_885_);
    v___x_889_ = leanh::lean_apply_1(v_x_884_, v_r_885_);
    v___x_890_ = leanh::lean_apply_4(
        v_map_888_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_883_,
        v___x_889_,
    );
    return v___x_890_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg___boxed(
    mut v_inst_891_: *mut leanh::LeanObject,
    mut v_f_892_: *mut leanh::LeanObject,
    mut v_x_893_: *mut leanh::LeanObject,
    mut v_r_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ =
        l_StateRefT_x27_instMonad___aux__1___redArg(v_inst_891_, v_f_892_, v_x_893_, v_r_894_);
    leanh::lean_dec(v_r_894_);
    return v_res_895_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1(
    mut v_00_u03c9_896_: *mut leanh::LeanObject,
    mut v_00_u03c3_897_: *mut leanh::LeanObject,
    mut v_m_898_: *mut leanh::LeanObject,
    mut v_inst_899_: *mut leanh::LeanObject,
    mut v_00_u03b1_900_: *mut leanh::LeanObject,
    mut v_00_u03b2_901_: *mut leanh::LeanObject,
    mut v_f_902_: *mut leanh::LeanObject,
    mut v_x_903_: *mut leanh::LeanObject,
    mut v_r_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_905_ = leanh::lean_ctor_get(v_inst_899_, 0);
    leanh::lean_inc_ref(v_toApplicative_905_);
    leanh::lean_dec_ref(v_inst_899_);
    v_toFunctor_906_ = leanh::lean_ctor_get(v_toApplicative_905_, 0);
    leanh::lean_inc_ref(v_toFunctor_906_);
    leanh::lean_dec_ref(v_toApplicative_905_);
    v_map_907_ = leanh::lean_ctor_get(v_toFunctor_906_, 0);
    leanh::lean_inc(v_map_907_);
    leanh::lean_dec_ref(v_toFunctor_906_);
    leanh::lean_inc(v_r_904_);
    v___x_908_ = leanh::lean_apply_1(v_x_903_, v_r_904_);
    v___x_909_ = leanh::lean_apply_4(
        v_map_907_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_902_,
        v___x_908_,
    );
    return v___x_909_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___boxed(
    mut v_00_u03c9_910_: *mut leanh::LeanObject,
    mut v_00_u03c3_911_: *mut leanh::LeanObject,
    mut v_m_912_: *mut leanh::LeanObject,
    mut v_inst_913_: *mut leanh::LeanObject,
    mut v_00_u03b1_914_: *mut leanh::LeanObject,
    mut v_00_u03b2_915_: *mut leanh::LeanObject,
    mut v_f_916_: *mut leanh::LeanObject,
    mut v_x_917_: *mut leanh::LeanObject,
    mut v_r_918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_919_ = l_StateRefT_x27_instMonad___aux__1(
        v_00_u03c9_910_,
        v_00_u03c3_911_,
        v_m_912_,
        v_inst_913_,
        v_00_u03b1_914_,
        v_00_u03b2_915_,
        v_f_916_,
        v_x_917_,
        v_r_918_,
    );
    leanh::lean_dec(v_r_918_);
    return v_res_919_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg(
    mut v_inst_920_: *mut leanh::LeanObject,
    mut v_a_921_: *mut leanh::LeanObject,
    mut v_x_922_: *mut leanh::LeanObject,
    mut v_r_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_924_ = leanh::lean_ctor_get(v_inst_920_, 0);
    leanh::lean_inc_ref(v_toApplicative_924_);
    leanh::lean_dec_ref(v_inst_920_);
    v_toFunctor_925_ = leanh::lean_ctor_get(v_toApplicative_924_, 0);
    leanh::lean_inc_ref(v_toFunctor_925_);
    leanh::lean_dec_ref(v_toApplicative_924_);
    v_mapConst_926_ = leanh::lean_ctor_get(v_toFunctor_925_, 1);
    leanh::lean_inc(v_mapConst_926_);
    leanh::lean_dec_ref(v_toFunctor_925_);
    leanh::lean_inc(v_r_923_);
    v___x_927_ = leanh::lean_apply_1(v_x_922_, v_r_923_);
    v___x_928_ = leanh::lean_apply_4(
        v_mapConst_926_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_921_,
        v___x_927_,
    );
    return v___x_928_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg___boxed(
    mut v_inst_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_x_931_: *mut leanh::LeanObject,
    mut v_r_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ =
        l_StateRefT_x27_instMonad___aux__3___redArg(v_inst_929_, v_a_930_, v_x_931_, v_r_932_);
    leanh::lean_dec(v_r_932_);
    return v_res_933_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3(
    mut v_00_u03c9_934_: *mut leanh::LeanObject,
    mut v_00_u03c3_935_: *mut leanh::LeanObject,
    mut v_m_936_: *mut leanh::LeanObject,
    mut v_inst_937_: *mut leanh::LeanObject,
    mut v_00_u03b1_938_: *mut leanh::LeanObject,
    mut v_00_u03b2_939_: *mut leanh::LeanObject,
    mut v_a_940_: *mut leanh::LeanObject,
    mut v_x_941_: *mut leanh::LeanObject,
    mut v_r_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_943_ = leanh::lean_ctor_get(v_inst_937_, 0);
    leanh::lean_inc_ref(v_toApplicative_943_);
    leanh::lean_dec_ref(v_inst_937_);
    v_toFunctor_944_ = leanh::lean_ctor_get(v_toApplicative_943_, 0);
    leanh::lean_inc_ref(v_toFunctor_944_);
    leanh::lean_dec_ref(v_toApplicative_943_);
    v_mapConst_945_ = leanh::lean_ctor_get(v_toFunctor_944_, 1);
    leanh::lean_inc(v_mapConst_945_);
    leanh::lean_dec_ref(v_toFunctor_944_);
    leanh::lean_inc(v_r_942_);
    v___x_946_ = leanh::lean_apply_1(v_x_941_, v_r_942_);
    v___x_947_ = leanh::lean_apply_4(
        v_mapConst_945_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_940_,
        v___x_946_,
    );
    return v___x_947_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___boxed(
    mut v_00_u03c9_948_: *mut leanh::LeanObject,
    mut v_00_u03c3_949_: *mut leanh::LeanObject,
    mut v_m_950_: *mut leanh::LeanObject,
    mut v_inst_951_: *mut leanh::LeanObject,
    mut v_00_u03b1_952_: *mut leanh::LeanObject,
    mut v_00_u03b2_953_: *mut leanh::LeanObject,
    mut v_a_954_: *mut leanh::LeanObject,
    mut v_x_955_: *mut leanh::LeanObject,
    mut v_r_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_StateRefT_x27_instMonad___aux__3(
        v_00_u03c9_948_,
        v_00_u03c3_949_,
        v_m_950_,
        v_inst_951_,
        v_00_u03b1_952_,
        v_00_u03b2_953_,
        v_a_954_,
        v_x_955_,
        v_r_956_,
    );
    leanh::lean_dec(v_r_956_);
    return v_res_957_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___redArg(
    mut v_inst_958_: *mut leanh::LeanObject,
    mut v_a_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_960_ = leanh::lean_ctor_get(v_inst_958_, 0);
    leanh::lean_inc_ref(v_toApplicative_960_);
    leanh::lean_dec_ref(v_inst_958_);
    v_toPure_961_ = leanh::lean_ctor_get(v_toApplicative_960_, 1);
    leanh::lean_inc(v_toPure_961_);
    leanh::lean_dec_ref(v_toApplicative_960_);
    v___x_962_ = leanh::lean_apply_2(v_toPure_961_, leanh::lean_box(0), v_a_959_);
    return v___x_962_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5(
    mut v_00_u03c9_963_: *mut leanh::LeanObject,
    mut v_00_u03c3_964_: *mut leanh::LeanObject,
    mut v_m_965_: *mut leanh::LeanObject,
    mut v_inst_966_: *mut leanh::LeanObject,
    mut v_00_u03b1_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_970_ = leanh::lean_ctor_get(v_inst_966_, 0);
    leanh::lean_inc_ref(v_toApplicative_970_);
    leanh::lean_dec_ref(v_inst_966_);
    v_toPure_971_ = leanh::lean_ctor_get(v_toApplicative_970_, 1);
    leanh::lean_inc(v_toPure_971_);
    leanh::lean_dec_ref(v_toApplicative_970_);
    v___x_972_ = leanh::lean_apply_2(v_toPure_971_, leanh::lean_box(0), v_a_968_);
    return v___x_972_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___boxed(
    mut v_00_u03c9_973_: *mut leanh::LeanObject,
    mut v_00_u03c3_974_: *mut leanh::LeanObject,
    mut v_m_975_: *mut leanh::LeanObject,
    mut v_inst_976_: *mut leanh::LeanObject,
    mut v_00_u03b1_977_: *mut leanh::LeanObject,
    mut v_a_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_StateRefT_x27_instMonad___aux__5(
        v_00_u03c9_973_,
        v_00_u03c3_974_,
        v_m_975_,
        v_inst_976_,
        v_00_u03b1_977_,
        v_a_978_,
        v_a_979_,
    );
    leanh::lean_dec(v_a_979_);
    return v_res_980_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(
    mut v_x_981_: *mut leanh::LeanObject,
    mut v_r_982_: *mut leanh::LeanObject,
    mut v_x_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = leanh::lean_box(0);
    leanh::lean_inc(v_r_982_);
    v___x_985_ = leanh::lean_apply_2(v_x_981_, v___x_984_, v_r_982_);
    return v___x_985_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_x_986_: *mut leanh::LeanObject,
    mut v_r_987_: *mut leanh::LeanObject,
    mut v_x_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(v_x_986_, v_r_987_, v_x_988_);
    leanh::lean_dec(v_r_987_);
    return v_res_989_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg(
    mut v_inst_990_: *mut leanh::LeanObject,
    mut v_f_991_: *mut leanh::LeanObject,
    mut v_x_992_: *mut leanh::LeanObject,
    mut v_r_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_994_ = leanh::lean_ctor_get(v_inst_990_, 0);
    leanh::lean_inc_ref(v_toApplicative_994_);
    leanh::lean_dec_ref(v_inst_990_);
    v_toSeq_995_ = leanh::lean_ctor_get(v_toApplicative_994_, 2);
    leanh::lean_inc(v_toSeq_995_);
    leanh::lean_dec_ref(v_toApplicative_994_);
    leanh::lean_inc_n(v_r_993_, 2);
    v___f_996_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_996_, 0, v_x_992_);
    leanh::lean_closure_set(v___f_996_, 1, v_r_993_);
    v___x_997_ = leanh::lean_apply_1(v_f_991_, v_r_993_);
    v___x_998_ = leanh::lean_apply_4(
        v_toSeq_995_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_997_,
        v___f_996_,
    );
    return v___x_998_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___boxed(
    mut v_inst_999_: *mut leanh::LeanObject,
    mut v_f_1000_: *mut leanh::LeanObject,
    mut v_x_1001_: *mut leanh::LeanObject,
    mut v_r_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ =
        l_StateRefT_x27_instMonad___aux__7___redArg(v_inst_999_, v_f_1000_, v_x_1001_, v_r_1002_);
    leanh::lean_dec(v_r_1002_);
    return v_res_1003_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7(
    mut v_00_u03c9_1004_: *mut leanh::LeanObject,
    mut v_00_u03c3_1005_: *mut leanh::LeanObject,
    mut v_m_1006_: *mut leanh::LeanObject,
    mut v_inst_1007_: *mut leanh::LeanObject,
    mut v_00_u03b1_1008_: *mut leanh::LeanObject,
    mut v_00_u03b2_1009_: *mut leanh::LeanObject,
    mut v_f_1010_: *mut leanh::LeanObject,
    mut v_x_1011_: *mut leanh::LeanObject,
    mut v_r_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1013_ = leanh::lean_ctor_get(v_inst_1007_, 0);
    leanh::lean_inc_ref(v_toApplicative_1013_);
    leanh::lean_dec_ref(v_inst_1007_);
    v_toSeq_1014_ = leanh::lean_ctor_get(v_toApplicative_1013_, 2);
    leanh::lean_inc(v_toSeq_1014_);
    leanh::lean_dec_ref(v_toApplicative_1013_);
    leanh::lean_inc_n(v_r_1012_, 2);
    v___f_1015_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1015_, 0, v_x_1011_);
    leanh::lean_closure_set(v___f_1015_, 1, v_r_1012_);
    v___x_1016_ = leanh::lean_apply_1(v_f_1010_, v_r_1012_);
    v___x_1017_ = leanh::lean_apply_4(
        v_toSeq_1014_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1016_,
        v___f_1015_,
    );
    return v___x_1017_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___boxed(
    mut v_00_u03c9_1018_: *mut leanh::LeanObject,
    mut v_00_u03c3_1019_: *mut leanh::LeanObject,
    mut v_m_1020_: *mut leanh::LeanObject,
    mut v_inst_1021_: *mut leanh::LeanObject,
    mut v_00_u03b1_1022_: *mut leanh::LeanObject,
    mut v_00_u03b2_1023_: *mut leanh::LeanObject,
    mut v_f_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: *mut leanh::LeanObject,
    mut v_r_1026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_StateRefT_x27_instMonad___aux__7(
        v_00_u03c9_1018_,
        v_00_u03c3_1019_,
        v_m_1020_,
        v_inst_1021_,
        v_00_u03b1_1022_,
        v_00_u03b2_1023_,
        v_f_1024_,
        v_x_1025_,
        v_r_1026_,
    );
    leanh::lean_dec(v_r_1026_);
    return v_res_1027_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(
    mut v_b_1028_: *mut leanh::LeanObject,
    mut v_r_1029_: *mut leanh::LeanObject,
    mut v_x_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = leanh::lean_box(0);
    leanh::lean_inc(v_r_1029_);
    v___x_1032_ = leanh::lean_apply_2(v_b_1028_, v___x_1031_, v_r_1029_);
    return v___x_1032_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed(
    mut v_b_1033_: *mut leanh::LeanObject,
    mut v_r_1034_: *mut leanh::LeanObject,
    mut v_x_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ =
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(v_b_1033_, v_r_1034_, v_x_1035_);
    leanh::lean_dec(v_r_1034_);
    return v_res_1036_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg(
    mut v_inst_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_b_1039_: *mut leanh::LeanObject,
    mut v_r_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1041_ = leanh::lean_ctor_get(v_inst_1037_, 0);
    leanh::lean_inc_ref(v_toApplicative_1041_);
    leanh::lean_dec_ref(v_inst_1037_);
    v_toSeqLeft_1042_ = leanh::lean_ctor_get(v_toApplicative_1041_, 3);
    leanh::lean_inc(v_toSeqLeft_1042_);
    leanh::lean_dec_ref(v_toApplicative_1041_);
    leanh::lean_inc_n(v_r_1040_, 2);
    v___f_1043_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1043_, 0, v_b_1039_);
    leanh::lean_closure_set(v___f_1043_, 1, v_r_1040_);
    v___x_1044_ = leanh::lean_apply_1(v_a_1038_, v_r_1040_);
    v___x_1045_ = leanh::lean_apply_4(
        v_toSeqLeft_1042_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1044_,
        v___f_1043_,
    );
    return v___x_1045_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___boxed(
    mut v_inst_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_b_1048_: *mut leanh::LeanObject,
    mut v_r_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ =
        l_StateRefT_x27_instMonad___aux__9___redArg(v_inst_1046_, v_a_1047_, v_b_1048_, v_r_1049_);
    leanh::lean_dec(v_r_1049_);
    return v_res_1050_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9(
    mut v_00_u03c9_1051_: *mut leanh::LeanObject,
    mut v_00_u03c3_1052_: *mut leanh::LeanObject,
    mut v_m_1053_: *mut leanh::LeanObject,
    mut v_inst_1054_: *mut leanh::LeanObject,
    mut v_00_u03b1_1055_: *mut leanh::LeanObject,
    mut v_00_u03b2_1056_: *mut leanh::LeanObject,
    mut v_a_1057_: *mut leanh::LeanObject,
    mut v_b_1058_: *mut leanh::LeanObject,
    mut v_r_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1060_ = leanh::lean_ctor_get(v_inst_1054_, 0);
    leanh::lean_inc_ref(v_toApplicative_1060_);
    leanh::lean_dec_ref(v_inst_1054_);
    v_toSeqLeft_1061_ = leanh::lean_ctor_get(v_toApplicative_1060_, 3);
    leanh::lean_inc(v_toSeqLeft_1061_);
    leanh::lean_dec_ref(v_toApplicative_1060_);
    leanh::lean_inc_n(v_r_1059_, 2);
    v___f_1062_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1062_, 0, v_b_1058_);
    leanh::lean_closure_set(v___f_1062_, 1, v_r_1059_);
    v___x_1063_ = leanh::lean_apply_1(v_a_1057_, v_r_1059_);
    v___x_1064_ = leanh::lean_apply_4(
        v_toSeqLeft_1061_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1063_,
        v___f_1062_,
    );
    return v___x_1064_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___boxed(
    mut v_00_u03c9_1065_: *mut leanh::LeanObject,
    mut v_00_u03c3_1066_: *mut leanh::LeanObject,
    mut v_m_1067_: *mut leanh::LeanObject,
    mut v_inst_1068_: *mut leanh::LeanObject,
    mut v_00_u03b1_1069_: *mut leanh::LeanObject,
    mut v_00_u03b2_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_b_1072_: *mut leanh::LeanObject,
    mut v_r_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_StateRefT_x27_instMonad___aux__9(
        v_00_u03c9_1065_,
        v_00_u03c3_1066_,
        v_m_1067_,
        v_inst_1068_,
        v_00_u03b1_1069_,
        v_00_u03b2_1070_,
        v_a_1071_,
        v_b_1072_,
        v_r_1073_,
    );
    leanh::lean_dec(v_r_1073_);
    return v_res_1074_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg(
    mut v_inst_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
    mut v_b_1077_: *mut leanh::LeanObject,
    mut v_r_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1079_ = leanh::lean_ctor_get(v_inst_1075_, 0);
    leanh::lean_inc_ref(v_toApplicative_1079_);
    leanh::lean_dec_ref(v_inst_1075_);
    v_toSeqRight_1080_ = leanh::lean_ctor_get(v_toApplicative_1079_, 4);
    leanh::lean_inc(v_toSeqRight_1080_);
    leanh::lean_dec_ref(v_toApplicative_1079_);
    leanh::lean_inc_n(v_r_1078_, 2);
    v___f_1081_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1081_, 0, v_b_1077_);
    leanh::lean_closure_set(v___f_1081_, 1, v_r_1078_);
    v___x_1082_ = leanh::lean_apply_1(v_a_1076_, v_r_1078_);
    v___x_1083_ = leanh::lean_apply_4(
        v_toSeqRight_1080_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1082_,
        v___f_1081_,
    );
    return v___x_1083_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg___boxed(
    mut v_inst_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_b_1086_: *mut leanh::LeanObject,
    mut v_r_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ =
        l_StateRefT_x27_instMonad___aux__11___redArg(v_inst_1084_, v_a_1085_, v_b_1086_, v_r_1087_);
    leanh::lean_dec(v_r_1087_);
    return v_res_1088_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11(
    mut v_00_u03c9_1089_: *mut leanh::LeanObject,
    mut v_00_u03c3_1090_: *mut leanh::LeanObject,
    mut v_m_1091_: *mut leanh::LeanObject,
    mut v_inst_1092_: *mut leanh::LeanObject,
    mut v_00_u03b1_1093_: *mut leanh::LeanObject,
    mut v_00_u03b2_1094_: *mut leanh::LeanObject,
    mut v_a_1095_: *mut leanh::LeanObject,
    mut v_b_1096_: *mut leanh::LeanObject,
    mut v_r_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = leanh::lean_ctor_get(v_inst_1092_, 0);
    leanh::lean_inc_ref(v_toApplicative_1098_);
    leanh::lean_dec_ref(v_inst_1092_);
    v_toSeqRight_1099_ = leanh::lean_ctor_get(v_toApplicative_1098_, 4);
    leanh::lean_inc(v_toSeqRight_1099_);
    leanh::lean_dec_ref(v_toApplicative_1098_);
    leanh::lean_inc_n(v_r_1097_, 2);
    v___f_1100_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1100_, 0, v_b_1096_);
    leanh::lean_closure_set(v___f_1100_, 1, v_r_1097_);
    v___x_1101_ = leanh::lean_apply_1(v_a_1095_, v_r_1097_);
    v___x_1102_ = leanh::lean_apply_4(
        v_toSeqRight_1099_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1101_,
        v___f_1100_,
    );
    return v___x_1102_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___boxed(
    mut v_00_u03c9_1103_: *mut leanh::LeanObject,
    mut v_00_u03c3_1104_: *mut leanh::LeanObject,
    mut v_m_1105_: *mut leanh::LeanObject,
    mut v_inst_1106_: *mut leanh::LeanObject,
    mut v_00_u03b1_1107_: *mut leanh::LeanObject,
    mut v_00_u03b2_1108_: *mut leanh::LeanObject,
    mut v_a_1109_: *mut leanh::LeanObject,
    mut v_b_1110_: *mut leanh::LeanObject,
    mut v_r_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1112_ = l_StateRefT_x27_instMonad___aux__11(
        v_00_u03c9_1103_,
        v_00_u03c3_1104_,
        v_m_1105_,
        v_inst_1106_,
        v_00_u03b1_1107_,
        v_00_u03b2_1108_,
        v_a_1109_,
        v_b_1110_,
        v_r_1111_,
    );
    leanh::lean_dec(v_r_1111_);
    return v_res_1112_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(
    mut v_f_1113_: *mut leanh::LeanObject,
    mut v_a_1114_: *mut leanh::LeanObject,
    mut v_a_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1114_);
    v___x_1116_ = leanh::lean_apply_2(v_f_1113_, v_a_1115_, v_a_1114_);
    return v___x_1116_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_f_1117_: *mut leanh::LeanObject,
    mut v_a_1118_: *mut leanh::LeanObject,
    mut v_a_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ =
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(v_f_1117_, v_a_1118_, v_a_1119_);
    leanh::lean_dec(v_a_1118_);
    return v_res_1120_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg(
    mut v_inst_1121_: *mut leanh::LeanObject,
    mut v_x_1122_: *mut leanh::LeanObject,
    mut v_f_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1125_ = leanh::lean_ctor_get(v_inst_1121_, 1);
    leanh::lean_inc(v_toBind_1125_);
    leanh::lean_dec_ref(v_inst_1121_);
    leanh::lean_inc_n(v_a_1124_, 2);
    v___f_1126_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1126_, 0, v_f_1123_);
    leanh::lean_closure_set(v___f_1126_, 1, v_a_1124_);
    v___x_1127_ = leanh::lean_apply_1(v_x_1122_, v_a_1124_);
    v___x_1128_ = leanh::lean_apply_4(
        v_toBind_1125_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1127_,
        v___f_1126_,
    );
    return v___x_1128_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___boxed(
    mut v_inst_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
    mut v_f_1131_: *mut leanh::LeanObject,
    mut v_a_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ =
        l_StateRefT_x27_instMonad___aux__13___redArg(v_inst_1129_, v_x_1130_, v_f_1131_, v_a_1132_);
    leanh::lean_dec(v_a_1132_);
    return v_res_1133_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13(
    mut v_00_u03c9_1134_: *mut leanh::LeanObject,
    mut v_00_u03c3_1135_: *mut leanh::LeanObject,
    mut v_m_1136_: *mut leanh::LeanObject,
    mut v_inst_1137_: *mut leanh::LeanObject,
    mut v_00_u03b1_1138_: *mut leanh::LeanObject,
    mut v_00_u03b2_1139_: *mut leanh::LeanObject,
    mut v_x_1140_: *mut leanh::LeanObject,
    mut v_f_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1143_ = leanh::lean_ctor_get(v_inst_1137_, 1);
    leanh::lean_inc(v_toBind_1143_);
    leanh::lean_dec_ref(v_inst_1137_);
    leanh::lean_inc_n(v_a_1142_, 2);
    v___f_1144_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1144_, 0, v_f_1141_);
    leanh::lean_closure_set(v___f_1144_, 1, v_a_1142_);
    v___x_1145_ = leanh::lean_apply_1(v_x_1140_, v_a_1142_);
    v___x_1146_ = leanh::lean_apply_4(
        v_toBind_1143_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1145_,
        v___f_1144_,
    );
    return v___x_1146_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___boxed(
    mut v_00_u03c9_1147_: *mut leanh::LeanObject,
    mut v_00_u03c3_1148_: *mut leanh::LeanObject,
    mut v_m_1149_: *mut leanh::LeanObject,
    mut v_inst_1150_: *mut leanh::LeanObject,
    mut v_00_u03b1_1151_: *mut leanh::LeanObject,
    mut v_00_u03b2_1152_: *mut leanh::LeanObject,
    mut v_x_1153_: *mut leanh::LeanObject,
    mut v_f_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_StateRefT_x27_instMonad___aux__13(
        v_00_u03c9_1147_,
        v_00_u03c3_1148_,
        v_m_1149_,
        v_inst_1150_,
        v_00_u03b1_1151_,
        v_00_u03b2_1152_,
        v_x_1153_,
        v_f_1154_,
        v_a_1155_,
    );
    leanh::lean_dec(v_a_1155_);
    return v_res_1156_;
}
pub unsafe fn l_StateRefT_x27_instMonad___redArg(
    mut v_inst_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1157_, 6);
    v___x_1158_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1158_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1158_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1158_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1158_, 3, v_inst_1157_);
    v___x_1159_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1159_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1159_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1159_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1159_, 3, v_inst_1157_);
    v___x_1160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    v___x_1161_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___x_1161_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1161_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1161_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1161_, 3, v_inst_1157_);
    v___x_1162_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1162_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1162_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1162_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1162_, 3, v_inst_1157_);
    v___x_1163_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1163_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1163_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1163_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1163_, 3, v_inst_1157_);
    v___x_1164_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1164_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1164_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1164_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1164_, 3, v_inst_1157_);
    v___x_1165_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1165_, 0, v___x_1160_);
    leanh::lean_ctor_set(v___x_1165_, 1, v___x_1161_);
    leanh::lean_ctor_set(v___x_1165_, 2, v___x_1162_);
    leanh::lean_ctor_set(v___x_1165_, 3, v___x_1163_);
    leanh::lean_ctor_set(v___x_1165_, 4, v___x_1164_);
    v___x_1166_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1166_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1166_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1166_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1166_, 3, v_inst_1157_);
    v___x_1167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1167_, 0, v___x_1165_);
    leanh::lean_ctor_set(v___x_1167_, 1, v___x_1166_);
    return v___x_1167_;
}
pub unsafe fn l_StateRefT_x27_instMonad(
    mut v_00_u03c9_1168_: *mut leanh::LeanObject,
    mut v_00_u03c3_1169_: *mut leanh::LeanObject,
    mut v_m_1170_: *mut leanh::LeanObject,
    mut v_inst_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_StateRefT_x27_instMonad___redArg(v_inst_1171_);
    return v___x_1172_;
}
pub unsafe fn l_StateRefT_x27_instMonadLift(
    mut v_00_u03c9_1174_: *mut leanh::LeanObject,
    mut v_00_u03c3_1175_: *mut leanh::LeanObject,
    mut v_m_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_StateRefT_x27_instMonadLift___closed__0;
    return v___x_1177_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg(
    mut v_f_1178_: *mut leanh::LeanObject,
    mut v_x_1179_: *mut leanh::LeanObject,
    mut v_ctx_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1180_);
    v___x_1181_ = leanh::lean_apply_1(v_x_1179_, v_ctx_1180_);
    v___x_1182_ = leanh::lean_apply_2(v_f_1178_, leanh::lean_box(0), v___x_1181_);
    return v___x_1182_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(
    mut v_f_1183_: *mut leanh::LeanObject,
    mut v_x_1184_: *mut leanh::LeanObject,
    mut v_ctx_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_1183_, v_x_1184_, v_ctx_1185_);
    leanh::lean_dec(v_ctx_1185_);
    return v_res_1186_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1(
    mut v_00_u03c9_1187_: *mut leanh::LeanObject,
    mut v_00_u03c3_1188_: *mut leanh::LeanObject,
    mut v_m_1189_: *mut leanh::LeanObject,
    mut v_00_u03b1_1190_: *mut leanh::LeanObject,
    mut v_f_1191_: *mut leanh::LeanObject,
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_ctx_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1193_);
    v___x_1194_ = leanh::lean_apply_1(v_x_1192_, v_ctx_1193_);
    v___x_1195_ = leanh::lean_apply_2(v_f_1191_, leanh::lean_box(0), v___x_1194_);
    return v___x_1195_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___boxed(
    mut v_00_u03c9_1196_: *mut leanh::LeanObject,
    mut v_00_u03c3_1197_: *mut leanh::LeanObject,
    mut v_m_1198_: *mut leanh::LeanObject,
    mut v_00_u03b1_1199_: *mut leanh::LeanObject,
    mut v_f_1200_: *mut leanh::LeanObject,
    mut v_x_1201_: *mut leanh::LeanObject,
    mut v_ctx_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_StateRefT_x27_instMonadFunctor___aux__1(
        v_00_u03c9_1196_,
        v_00_u03c3_1197_,
        v_m_1198_,
        v_00_u03b1_1199_,
        v_f_1200_,
        v_x_1201_,
        v_ctx_1202_,
    );
    leanh::lean_dec(v_ctx_1202_);
    return v_res_1203_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor(
    mut v_00_u03c9_1205_: *mut leanh::LeanObject,
    mut v_00_u03c3_1206_: *mut leanh::LeanObject,
    mut v_m_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_StateRefT_x27_instMonadFunctor___closed__0;
    return v___x_1208_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___redArg(
    mut v_inst_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_1210_ = leanh::lean_ctor_get(v_inst_1209_, 1);
    leanh::lean_inc(v_failure_1210_);
    leanh::lean_dec_ref(v_inst_1209_);
    v___x_1211_ = leanh::lean_apply_1(v_failure_1210_, leanh::lean_box(0));
    return v___x_1211_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1(
    mut v_00_u03c9_1212_: *mut leanh::LeanObject,
    mut v_00_u03c3_1213_: *mut leanh::LeanObject,
    mut v_m_1214_: *mut leanh::LeanObject,
    mut v_inst_1215_: *mut leanh::LeanObject,
    mut v_00_u03b1_1216_: *mut leanh::LeanObject,
    mut v_a_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_1218_ = leanh::lean_ctor_get(v_inst_1215_, 1);
    leanh::lean_inc(v_failure_1218_);
    leanh::lean_dec_ref(v_inst_1215_);
    v___x_1219_ = leanh::lean_apply_1(v_failure_1218_, leanh::lean_box(0));
    return v___x_1219_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed(
    mut v_00_u03c9_1220_: *mut leanh::LeanObject,
    mut v_00_u03c3_1221_: *mut leanh::LeanObject,
    mut v_m_1222_: *mut leanh::LeanObject,
    mut v_inst_1223_: *mut leanh::LeanObject,
    mut v_00_u03b1_1224_: *mut leanh::LeanObject,
    mut v_a_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_StateRefT_x27_instAlternativeOfMonad___aux__1(
        v_00_u03c9_1220_,
        v_00_u03c3_1221_,
        v_m_1222_,
        v_inst_1223_,
        v_00_u03b1_1224_,
        v_a_1225_,
    );
    leanh::lean_dec(v_a_1225_);
    return v_res_1226_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
    mut v_x_u2082_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_x_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = leanh::lean_box(0);
    leanh::lean_inc(v_a_1228_);
    v___x_1231_ = leanh::lean_apply_2(v_x_u2082_1227_, v___x_1230_, v_a_1228_);
    return v___x_1231_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_u2082_1232_: *mut leanh::LeanObject,
    mut v_a_1233_: *mut leanh::LeanObject,
    mut v_x_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
        v_x_u2082_1232_,
        v_a_1233_,
        v_x_1234_,
    );
    leanh::lean_dec(v_a_1233_);
    return v_res_1235_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
    mut v_inst_1236_: *mut leanh::LeanObject,
    mut v_x_u2081_1237_: *mut leanh::LeanObject,
    mut v_x_u2082_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1240_ = leanh::lean_ctor_get(v_inst_1236_, 2);
    leanh::lean_inc(v_orElse_1240_);
    leanh::lean_dec_ref(v_inst_1236_);
    leanh::lean_inc_n(v_a_1239_, 2);
    v___f_1241_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1241_, 0, v_x_u2082_1238_);
    leanh::lean_closure_set(v___f_1241_, 1, v_a_1239_);
    v___x_1242_ = leanh::lean_apply_1(v_x_u2081_1237_, v_a_1239_);
    v___x_1243_ = leanh::lean_apply_3(
        v_orElse_1240_,
        leanh::lean_box(0),
        v___x_1242_,
        v___f_1241_,
    );
    return v___x_1243_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___boxed(
    mut v_inst_1244_: *mut leanh::LeanObject,
    mut v_x_u2081_1245_: *mut leanh::LeanObject,
    mut v_x_u2082_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
        v_inst_1244_,
        v_x_u2081_1245_,
        v_x_u2082_1246_,
        v_a_1247_,
    );
    leanh::lean_dec(v_a_1247_);
    return v_res_1248_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3(
    mut v_00_u03c9_1249_: *mut leanh::LeanObject,
    mut v_00_u03c3_1250_: *mut leanh::LeanObject,
    mut v_m_1251_: *mut leanh::LeanObject,
    mut v_inst_1252_: *mut leanh::LeanObject,
    mut v_00_u03b1_1253_: *mut leanh::LeanObject,
    mut v_x_u2081_1254_: *mut leanh::LeanObject,
    mut v_x_u2082_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1257_ = leanh::lean_ctor_get(v_inst_1252_, 2);
    leanh::lean_inc(v_orElse_1257_);
    leanh::lean_dec_ref(v_inst_1252_);
    leanh::lean_inc_n(v_a_1256_, 2);
    v___f_1258_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1258_, 0, v_x_u2082_1255_);
    leanh::lean_closure_set(v___f_1258_, 1, v_a_1256_);
    v___x_1259_ = leanh::lean_apply_1(v_x_u2081_1254_, v_a_1256_);
    v___x_1260_ = leanh::lean_apply_3(
        v_orElse_1257_,
        leanh::lean_box(0),
        v___x_1259_,
        v___f_1258_,
    );
    return v___x_1260_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed(
    mut v_00_u03c9_1261_: *mut leanh::LeanObject,
    mut v_00_u03c3_1262_: *mut leanh::LeanObject,
    mut v_m_1263_: *mut leanh::LeanObject,
    mut v_inst_1264_: *mut leanh::LeanObject,
    mut v_00_u03b1_1265_: *mut leanh::LeanObject,
    mut v_x_u2081_1266_: *mut leanh::LeanObject,
    mut v_x_u2082_1267_: *mut leanh::LeanObject,
    mut v_a_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1269_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3(
        v_00_u03c9_1261_,
        v_00_u03c3_1262_,
        v_m_1263_,
        v_inst_1264_,
        v_00_u03b1_1265_,
        v_x_u2081_1266_,
        v_x_u2082_1267_,
        v_a_1268_,
    );
    leanh::lean_dec(v_a_1268_);
    return v_res_1269_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___redArg(
    mut v_inst_1270_: *mut leanh::LeanObject,
    mut v_inst_1271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_StateRefT_x27_instMonad___redArg(v_inst_1271_);
    v_toApplicative_1273_ = leanh::lean_ctor_get(v___x_1272_, 0);
    leanh::lean_inc_ref(v_toApplicative_1273_);
    leanh::lean_dec_ref(v___x_1272_);
    leanh::lean_inc_ref(v_inst_1270_);
    v___x_1274_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1274_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1274_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1274_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1274_, 3, v_inst_1270_);
    v___x_1275_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___x_1275_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1275_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1275_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1275_, 3, v_inst_1270_);
    v___x_1276_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1276_, 0, v_toApplicative_1273_);
    leanh::lean_ctor_set(v___x_1276_, 1, v___x_1274_);
    leanh::lean_ctor_set(v___x_1276_, 2, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad(
    mut v_00_u03c9_1277_: *mut leanh::LeanObject,
    mut v_00_u03c3_1278_: *mut leanh::LeanObject,
    mut v_m_1279_: *mut leanh::LeanObject,
    mut v_inst_1280_: *mut leanh::LeanObject,
    mut v_inst_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_1280_, v_inst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(
    mut v_x_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1283_);
    return v_x_1283_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(v_x_1284_);
    leanh::lean_dec(v_x_1284_);
    return v_res_1285_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
    mut v_inst_1287_: *mut leanh::LeanObject,
    mut v_inst_1288_: *mut leanh::LeanObject,
    mut v_x_1289_: *mut leanh::LeanObject,
    mut v_r_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1291_ = leanh::lean_ctor_get(v_inst_1287_, 0);
    leanh::lean_inc_ref(v_toApplicative_1291_);
    leanh::lean_dec_ref(v_inst_1287_);
    v_toFunctor_1292_ = leanh::lean_ctor_get(v_toApplicative_1291_, 0);
    leanh::lean_inc_ref(v_toFunctor_1292_);
    leanh::lean_dec_ref(v_toApplicative_1291_);
    v_map_1293_ = leanh::lean_ctor_get(v_toFunctor_1292_, 0);
    leanh::lean_inc(v_map_1293_);
    leanh::lean_dec_ref(v_toFunctor_1292_);
    v___f_1294_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    leanh::lean_inc(v_r_1290_);
    v___x_1295_ = leanh::lean_apply_1(v_x_1289_, v_r_1290_);
    v___x_1296_ = leanh::lean_apply_2(v_inst_1288_, leanh::lean_box(0), v___x_1295_);
    v___x_1297_ = leanh::lean_apply_4(
        v_map_1293_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1294_,
        v___x_1296_,
    );
    return v___x_1297_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___boxed(
    mut v_inst_1298_: *mut leanh::LeanObject,
    mut v_inst_1299_: *mut leanh::LeanObject,
    mut v_x_1300_: *mut leanh::LeanObject,
    mut v_r_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
        v_inst_1298_,
        v_inst_1299_,
        v_x_1300_,
        v_r_1301_,
    );
    leanh::lean_dec(v_r_1301_);
    return v_res_1302_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3(
    mut v_00_u03c9_1303_: *mut leanh::LeanObject,
    mut v_00_u03c3_1304_: *mut leanh::LeanObject,
    mut v_m_1305_: *mut leanh::LeanObject,
    mut v_inst_1306_: *mut leanh::LeanObject,
    mut v_inst_1307_: *mut leanh::LeanObject,
    mut v_00_u03b1_1308_: *mut leanh::LeanObject,
    mut v_x_1309_: *mut leanh::LeanObject,
    mut v_r_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1311_ = leanh::lean_ctor_get(v_inst_1306_, 0);
    leanh::lean_inc_ref(v_toApplicative_1311_);
    leanh::lean_dec_ref(v_inst_1306_);
    v_toFunctor_1312_ = leanh::lean_ctor_get(v_toApplicative_1311_, 0);
    leanh::lean_inc_ref(v_toFunctor_1312_);
    leanh::lean_dec_ref(v_toApplicative_1311_);
    v_map_1313_ = leanh::lean_ctor_get(v_toFunctor_1312_, 0);
    leanh::lean_inc(v_map_1313_);
    leanh::lean_dec_ref(v_toFunctor_1312_);
    v___f_1314_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    leanh::lean_inc(v_r_1310_);
    v___x_1315_ = leanh::lean_apply_1(v_x_1309_, v_r_1310_);
    v___x_1316_ = leanh::lean_apply_2(v_inst_1307_, leanh::lean_box(0), v___x_1315_);
    v___x_1317_ = leanh::lean_apply_4(
        v_map_1313_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1314_,
        v___x_1316_,
    );
    return v___x_1317_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed(
    mut v_00_u03c9_1318_: *mut leanh::LeanObject,
    mut v_00_u03c3_1319_: *mut leanh::LeanObject,
    mut v_m_1320_: *mut leanh::LeanObject,
    mut v_inst_1321_: *mut leanh::LeanObject,
    mut v_inst_1322_: *mut leanh::LeanObject,
    mut v_00_u03b1_1323_: *mut leanh::LeanObject,
    mut v_x_1324_: *mut leanh::LeanObject,
    mut v_r_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3(
        v_00_u03c9_1318_,
        v_00_u03c3_1319_,
        v_m_1320_,
        v_inst_1321_,
        v_inst_1322_,
        v_00_u03b1_1323_,
        v_x_1324_,
        v_r_1325_,
    );
    leanh::lean_dec(v_r_1325_);
    return v_res_1326_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___redArg(
    mut v_inst_1327_: *mut leanh::LeanObject,
    mut v_inst_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___x_1329_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1329_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1329_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1329_, 3, v_inst_1327_);
    leanh::lean_closure_set(v___x_1329_, 4, v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad(
    mut v_00_u03c9_1330_: *mut leanh::LeanObject,
    mut v_00_u03c3_1331_: *mut leanh::LeanObject,
    mut v_m_1332_: *mut leanh::LeanObject,
    mut v_inst_1333_: *mut leanh::LeanObject,
    mut v_inst_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___x_1335_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1335_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1335_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1335_, 3, v_inst_1333_);
    leanh::lean_closure_set(v___x_1335_, 4, v_inst_1334_);
    return v___x_1335_;
}
pub unsafe fn l_StateRefT_x27_get___redArg(
    mut v_inst_1336_: *mut leanh::LeanObject,
    mut v_ref_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1337_);
    v___x_1338_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1338_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1338_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1338_, 2, v_ref_1337_);
    v___x_1339_ = leanh::lean_apply_2(v_inst_1336_, leanh::lean_box(0), v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_StateRefT_x27_get___redArg___boxed(
    mut v_inst_1340_: *mut leanh::LeanObject,
    mut v_ref_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_StateRefT_x27_get___redArg(v_inst_1340_, v_ref_1341_);
    leanh::lean_dec(v_ref_1341_);
    return v_res_1342_;
}
pub unsafe fn l_StateRefT_x27_get(
    mut v_00_u03c9_1343_: *mut leanh::LeanObject,
    mut v_00_u03c3_1344_: *mut leanh::LeanObject,
    mut v_m_1345_: *mut leanh::LeanObject,
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_ref_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1347_);
    v___x_1348_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1348_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1348_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1348_, 2, v_ref_1347_);
    v___x_1349_ = leanh::lean_apply_2(v_inst_1346_, leanh::lean_box(0), v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_StateRefT_x27_get___boxed(
    mut v_00_u03c9_1350_: *mut leanh::LeanObject,
    mut v_00_u03c3_1351_: *mut leanh::LeanObject,
    mut v_m_1352_: *mut leanh::LeanObject,
    mut v_inst_1353_: *mut leanh::LeanObject,
    mut v_ref_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_StateRefT_x27_get(
        v_00_u03c9_1350_,
        v_00_u03c3_1351_,
        v_m_1352_,
        v_inst_1353_,
        v_ref_1354_,
    );
    leanh::lean_dec(v_ref_1354_);
    return v_res_1355_;
}
pub unsafe fn l_StateRefT_x27_set___redArg(
    mut v_inst_1356_: *mut leanh::LeanObject,
    mut v_s_1357_: *mut leanh::LeanObject,
    mut v_ref_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1358_);
    v___x_1359_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1359_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1359_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1359_, 2, v_ref_1358_);
    leanh::lean_closure_set(v___x_1359_, 3, v_s_1357_);
    v___x_1360_ = leanh::lean_apply_2(v_inst_1356_, leanh::lean_box(0), v___x_1359_);
    return v___x_1360_;
}
pub unsafe fn l_StateRefT_x27_set___redArg___boxed(
    mut v_inst_1361_: *mut leanh::LeanObject,
    mut v_s_1362_: *mut leanh::LeanObject,
    mut v_ref_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_StateRefT_x27_set___redArg(v_inst_1361_, v_s_1362_, v_ref_1363_);
    leanh::lean_dec(v_ref_1363_);
    return v_res_1364_;
}
pub unsafe fn l_StateRefT_x27_set(
    mut v_00_u03c9_1365_: *mut leanh::LeanObject,
    mut v_00_u03c3_1366_: *mut leanh::LeanObject,
    mut v_m_1367_: *mut leanh::LeanObject,
    mut v_inst_1368_: *mut leanh::LeanObject,
    mut v_s_1369_: *mut leanh::LeanObject,
    mut v_ref_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1370_);
    v___x_1371_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1371_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1371_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1371_, 2, v_ref_1370_);
    leanh::lean_closure_set(v___x_1371_, 3, v_s_1369_);
    v___x_1372_ = leanh::lean_apply_2(v_inst_1368_, leanh::lean_box(0), v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_StateRefT_x27_set___boxed(
    mut v_00_u03c9_1373_: *mut leanh::LeanObject,
    mut v_00_u03c3_1374_: *mut leanh::LeanObject,
    mut v_m_1375_: *mut leanh::LeanObject,
    mut v_inst_1376_: *mut leanh::LeanObject,
    mut v_s_1377_: *mut leanh::LeanObject,
    mut v_ref_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_StateRefT_x27_set(
        v_00_u03c9_1373_,
        v_00_u03c3_1374_,
        v_m_1375_,
        v_inst_1376_,
        v_s_1377_,
        v_ref_1378_,
    );
    leanh::lean_dec(v_ref_1378_);
    return v_res_1379_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg(
    mut v_inst_1380_: *mut leanh::LeanObject,
    mut v_f_1381_: *mut leanh::LeanObject,
    mut v_ref_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1382_);
    v___x_1383_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1383_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1383_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1383_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1383_, 3, v_ref_1382_);
    leanh::lean_closure_set(v___x_1383_, 4, v_f_1381_);
    v___x_1384_ = leanh::lean_apply_2(v_inst_1380_, leanh::lean_box(0), v___x_1383_);
    return v___x_1384_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg___boxed(
    mut v_inst_1385_: *mut leanh::LeanObject,
    mut v_f_1386_: *mut leanh::LeanObject,
    mut v_ref_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_StateRefT_x27_modifyGet___redArg(v_inst_1385_, v_f_1386_, v_ref_1387_);
    leanh::lean_dec(v_ref_1387_);
    return v_res_1388_;
}
pub unsafe fn l_StateRefT_x27_modifyGet(
    mut v_00_u03c9_1389_: *mut leanh::LeanObject,
    mut v_00_u03c3_1390_: *mut leanh::LeanObject,
    mut v_m_1391_: *mut leanh::LeanObject,
    mut v_00_u03b1_1392_: *mut leanh::LeanObject,
    mut v_inst_1393_: *mut leanh::LeanObject,
    mut v_f_1394_: *mut leanh::LeanObject,
    mut v_ref_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ref_1395_);
    v___x_1396_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1396_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1396_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1396_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1396_, 3, v_ref_1395_);
    leanh::lean_closure_set(v___x_1396_, 4, v_f_1394_);
    v___x_1397_ = leanh::lean_apply_2(v_inst_1393_, leanh::lean_box(0), v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___boxed(
    mut v_00_u03c9_1398_: *mut leanh::LeanObject,
    mut v_00_u03c3_1399_: *mut leanh::LeanObject,
    mut v_m_1400_: *mut leanh::LeanObject,
    mut v_00_u03b1_1401_: *mut leanh::LeanObject,
    mut v_inst_1402_: *mut leanh::LeanObject,
    mut v_f_1403_: *mut leanh::LeanObject,
    mut v_ref_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_StateRefT_x27_modifyGet(
        v_00_u03c9_1398_,
        v_00_u03c3_1399_,
        v_m_1400_,
        v_00_u03b1_1401_,
        v_inst_1402_,
        v_f_1403_,
        v_ref_1404_,
    );
    leanh::lean_dec(v_ref_1404_);
    return v_res_1405_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
    mut v_inst_1406_: *mut leanh::LeanObject,
    mut v_00_u03b1_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1409_);
    v___x_1410_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1410_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1410_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1410_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1410_, 3, v___y_1409_);
    leanh::lean_closure_set(v___x_1410_, 4, v___y_1408_);
    v___x_1411_ = leanh::lean_apply_2(v_inst_1406_, leanh::lean_box(0), v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(
    mut v_inst_1412_: *mut leanh::LeanObject,
    mut v_00_u03b1_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
        v_inst_1412_,
        v_00_u03b1_1413_,
        v___y_1414_,
        v___y_1415_,
    );
    leanh::lean_dec(v___y_1415_);
    return v_res_1416_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(
    mut v_inst_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_inst_1417_, 2);
    v___f_1418_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1418_, 0, v_inst_1417_);
    v___x_1419_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1419_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1419_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1419_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1419_, 3, v_inst_1417_);
    v___x_1420_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_set___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1420_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1420_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1420_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1420_, 3, v_inst_1417_);
    v___x_1421_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1421_, 0, v___x_1419_);
    leanh::lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    leanh::lean_ctor_set(v___x_1421_, 2, v___f_1418_);
    return v___x_1421_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(
    mut v_00_u03c9_1422_: *mut leanh::LeanObject,
    mut v_00_u03c3_1423_: *mut leanh::LeanObject,
    mut v_m_1424_: *mut leanh::LeanObject,
    mut v_inst_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_1425_);
    return v___x_1426_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_00_u03b1_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_1431_ = leanh::lean_ctor_get(v_inst_1427_, 0);
    leanh::lean_inc(v_throw_1431_);
    leanh::lean_dec_ref(v_inst_1427_);
    v___x_1432_ = leanh::lean_apply_2(v_throw_1431_, leanh::lean_box(0), v___y_1429_);
    return v___x_1432_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_00_u03b1_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
    mut v___y_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
        v_inst_1433_,
        v_00_u03b1_1434_,
        v___y_1435_,
        v___y_1436_,
    );
    leanh::lean_dec(v___y_1436_);
    return v_res_1437_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(
    mut v_c_1438_: *mut leanh::LeanObject,
    mut v_s_1439_: *mut leanh::LeanObject,
    mut v_e_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = leanh::lean_apply_2(v_c_1438_, v_e_1440_, v_s_1439_);
    return v___x_1441_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(
    mut v_inst_1442_: *mut leanh::LeanObject,
    mut v_00_u03b1_1443_: *mut leanh::LeanObject,
    mut v_x_1444_: *mut leanh::LeanObject,
    mut v_c_1445_: *mut leanh::LeanObject,
    mut v_s_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_1447_ = leanh::lean_ctor_get(v_inst_1442_, 1);
    leanh::lean_inc(v_tryCatch_1447_);
    leanh::lean_dec_ref(v_inst_1442_);
    leanh::lean_inc(v_s_1446_);
    v___f_1448_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1448_, 0, v_c_1445_);
    leanh::lean_closure_set(v___f_1448_, 1, v_s_1446_);
    v___x_1449_ = leanh::lean_apply_1(v_x_1444_, v_s_1446_);
    v___x_1450_ = leanh::lean_apply_3(
        v_tryCatch_1447_,
        leanh::lean_box(0),
        v___x_1449_,
        v___f_1448_,
    );
    return v___x_1450_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg(
    mut v_inst_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1451_);
    v___f_1452_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1452_, 0, v_inst_1451_);
    v___f_1453_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1453_, 0, v_inst_1451_);
    v___x_1454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1454_, 0, v___f_1452_);
    leanh::lean_ctor_set(v___x_1454_, 1, v___f_1453_);
    return v___x_1454_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf(
    mut v_00_u03c9_1455_: *mut leanh::LeanObject,
    mut v_00_u03c3_1456_: *mut leanh::LeanObject,
    mut v_m_1457_: *mut leanh::LeanObject,
    mut v_00_u03b5_1458_: *mut leanh::LeanObject,
    mut v_inst_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1459_);
    v___f_1460_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1460_, 0, v_inst_1459_);
    v___f_1461_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1461_, 0, v_inst_1459_);
    v___x_1462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1462_, 0, v___f_1460_);
    leanh::lean_ctor_set(v___x_1462_, 1, v___f_1461_);
    return v___x_1462_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
    mut v_ctx_1463_: *mut leanh::LeanObject,
    mut v_00_u03b2_1464_: *mut leanh::LeanObject,
    mut v_x_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1463_);
    v___x_1466_ = leanh::lean_apply_1(v_x_1465_, v_ctx_1463_);
    return v___x_1466_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_ctx_1467_: *mut leanh::LeanObject,
    mut v_00_u03b2_1468_: *mut leanh::LeanObject,
    mut v_x_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
        v_ctx_1467_,
        v_00_u03b2_1468_,
        v_x_1469_,
    );
    leanh::lean_dec(v_ctx_1467_);
    return v_res_1470_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg(
    mut v_f_1471_: *mut leanh::LeanObject,
    mut v_ctx_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1472_);
    v___f_1473_ = leanh::lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1473_, 0, v_ctx_1472_);
    v___x_1474_ = leanh::lean_apply_1(v_f_1471_, v___f_1473_);
    return v___x_1474_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(
    mut v_f_1475_: *mut leanh::LeanObject,
    mut v_ctx_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_1475_, v_ctx_1476_);
    leanh::lean_dec(v_ctx_1476_);
    return v_res_1477_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1(
    mut v_00_u03c9_1478_: *mut leanh::LeanObject,
    mut v_00_u03c3_1479_: *mut leanh::LeanObject,
    mut v_m_1480_: *mut leanh::LeanObject,
    mut v_00_u03b1_1481_: *mut leanh::LeanObject,
    mut v_f_1482_: *mut leanh::LeanObject,
    mut v_ctx_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1483_);
    v___f_1484_ = leanh::lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1484_, 0, v_ctx_1483_);
    v___x_1485_ = leanh::lean_apply_1(v_f_1482_, v___f_1484_);
    return v___x_1485_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___boxed(
    mut v_00_u03c9_1486_: *mut leanh::LeanObject,
    mut v_00_u03c3_1487_: *mut leanh::LeanObject,
    mut v_m_1488_: *mut leanh::LeanObject,
    mut v_00_u03b1_1489_: *mut leanh::LeanObject,
    mut v_f_1490_: *mut leanh::LeanObject,
    mut v_ctx_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l_instMonadControlStateRefT_x27___aux__1(
        v_00_u03c9_1486_,
        v_00_u03c3_1487_,
        v_m_1488_,
        v_00_u03b1_1489_,
        v_f_1490_,
        v_ctx_1491_,
    );
    leanh::lean_dec(v_ctx_1491_);
    return v_res_1492_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg(
    mut v_x_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1493_);
    return v_x_1493_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(
    mut v_x_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_1494_);
    leanh::lean_dec(v_x_1494_);
    return v_res_1495_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3(
    mut v_00_u03c9_1496_: *mut leanh::LeanObject,
    mut v_00_u03c3_1497_: *mut leanh::LeanObject,
    mut v_m_1498_: *mut leanh::LeanObject,
    mut v_00_u03b1_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1500_);
    return v_x_1500_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___boxed(
    mut v_00_u03c9_1502_: *mut leanh::LeanObject,
    mut v_00_u03c3_1503_: *mut leanh::LeanObject,
    mut v_m_1504_: *mut leanh::LeanObject,
    mut v_00_u03b1_1505_: *mut leanh::LeanObject,
    mut v_x_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_instMonadControlStateRefT_x27___aux__3(
        v_00_u03c9_1502_,
        v_00_u03c3_1503_,
        v_m_1504_,
        v_00_u03b1_1505_,
        v_x_1506_,
        v_x_1507_,
    );
    leanh::lean_dec(v_x_1507_);
    leanh::lean_dec(v_x_1506_);
    return v_res_1508_;
}
pub unsafe fn l_instMonadControlStateRefT_x27(
    mut v_00_u03c9_1514_: *mut leanh::LeanObject,
    mut v_00_u03c3_1515_: *mut leanh::LeanObject,
    mut v_m_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_instMonadControlStateRefT_x27___closed__2;
    return v___x_1517_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
    mut v_h_1518_: *mut leanh::LeanObject,
    mut v_ctx_1519_: *mut leanh::LeanObject,
    mut v_a_x3f_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1519_);
    v___x_1521_ = leanh::lean_apply_2(v_h_1518_, v_a_x3f_1520_, v_ctx_1519_);
    return v___x_1521_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_h_1522_: *mut leanh::LeanObject,
    mut v_ctx_1523_: *mut leanh::LeanObject,
    mut v_a_x3f_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
        v_h_1522_,
        v_ctx_1523_,
        v_a_x3f_1524_,
    );
    leanh::lean_dec(v_ctx_1523_);
    return v_res_1525_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg(
    mut v_inst_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_h_1528_: *mut leanh::LeanObject,
    mut v_ctx_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_ctx_1529_, 2);
    v___f_1530_ = leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1530_, 0, v_h_1528_);
    leanh::lean_closure_set(v___f_1530_, 1, v_ctx_1529_);
    v___x_1531_ = leanh::lean_apply_1(v_x_1527_, v_ctx_1529_);
    v___x_1532_ = leanh::lean_apply_4(
        v_inst_1526_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1531_,
        v___f_1530_,
    );
    return v___x_1532_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(
    mut v_inst_1533_: *mut leanh::LeanObject,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_h_1535_: *mut leanh::LeanObject,
    mut v_ctx_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(
        v_inst_1533_,
        v_x_1534_,
        v_h_1535_,
        v_ctx_1536_,
    );
    leanh::lean_dec(v_ctx_1536_);
    return v_res_1537_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1(
    mut v_m_1538_: *mut leanh::LeanObject,
    mut v_00_u03c9_1539_: *mut leanh::LeanObject,
    mut v_00_u03c3_1540_: *mut leanh::LeanObject,
    mut v_inst_1541_: *mut leanh::LeanObject,
    mut v_00_u03b1_1542_: *mut leanh::LeanObject,
    mut v_00_u03b2_1543_: *mut leanh::LeanObject,
    mut v_x_1544_: *mut leanh::LeanObject,
    mut v_h_1545_: *mut leanh::LeanObject,
    mut v_ctx_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_ctx_1546_, 2);
    v___f_1547_ = leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1547_, 0, v_h_1545_);
    leanh::lean_closure_set(v___f_1547_, 1, v_ctx_1546_);
    v___x_1548_ = leanh::lean_apply_1(v_x_1544_, v_ctx_1546_);
    v___x_1549_ = leanh::lean_apply_4(
        v_inst_1541_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1548_,
        v___f_1547_,
    );
    return v___x_1549_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___boxed(
    mut v_m_1550_: *mut leanh::LeanObject,
    mut v_00_u03c9_1551_: *mut leanh::LeanObject,
    mut v_00_u03c3_1552_: *mut leanh::LeanObject,
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_00_u03b1_1554_: *mut leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut leanh::LeanObject,
    mut v_x_1556_: *mut leanh::LeanObject,
    mut v_h_1557_: *mut leanh::LeanObject,
    mut v_ctx_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_instMonadFinallyStateRefT_x27___aux__1(
        v_m_1550_,
        v_00_u03c9_1551_,
        v_00_u03c3_1552_,
        v_inst_1553_,
        v_00_u03b1_1554_,
        v_00_u03b2_1555_,
        v_x_1556_,
        v_h_1557_,
        v_ctx_1558_,
    );
    leanh::lean_dec(v_ctx_1558_);
    return v_res_1559_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___redArg(
    mut v_inst_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1561_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1561_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1561_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1561_, 3, v_inst_1560_);
    return v___x_1561_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27(
    mut v_m_1562_: *mut leanh::LeanObject,
    mut v_00_u03c9_1563_: *mut leanh::LeanObject,
    mut v_00_u03c3_1564_: *mut leanh::LeanObject,
    mut v_inst_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1566_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1566_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1566_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1566_, 3, v_inst_1565_);
    return v___x_1566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_StateRef(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_StateRef(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_StateRef(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_StateRef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_StateRef(builtin);
}