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
pub static l_StateRefT_x27_instMonadLift___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadLift___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadLift___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_StateRefT_x27_instMonadFunctor___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadFunctor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value:
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
    m_fun: l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__1_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__3___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_StateRefT_x27_run___redArg___lam__0(
    mut v_a_784_: *mut crate::leanh::LeanObject,
    mut v_toPure_785_: *mut crate::leanh::LeanObject,
    mut v_s_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_787_, 0, v_a_784_);
    crate::leanh::lean_ctor_set(v___x_787_, 1, v_s_786_);
    v___x_788_ = crate::leanh::lean_apply_2(v_toPure_785_, crate::leanh::lean_box(0), v___x_787_);
    return v___x_788_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__1(
    mut v_toPure_789_: *mut crate::leanh::LeanObject,
    mut v_ref_790_: *mut crate::leanh::LeanObject,
    mut v_inst_791_: *mut crate::leanh::LeanObject,
    mut v_toBind_792_: *mut crate::leanh::LeanObject,
    mut v_a_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_794_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_794_, 0, v_a_793_);
    crate::leanh::lean_closure_set(v___f_794_, 1, v_toPure_789_);
    v___x_795_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_795_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_795_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_795_, 2, v_ref_790_);
    v___x_796_ = crate::leanh::lean_apply_2(v_inst_791_, crate::leanh::lean_box(0), v___x_795_);
    v___x_797_ = crate::leanh::lean_apply_4(
        v_toBind_792_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_796_,
        v___f_794_,
    );
    return v___x_797_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__2(
    mut v_toPure_798_: *mut crate::leanh::LeanObject,
    mut v_inst_799_: *mut crate::leanh::LeanObject,
    mut v_toBind_800_: *mut crate::leanh::LeanObject,
    mut v_x_801_: *mut crate::leanh::LeanObject,
    mut v_ref_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_800_);
    crate::leanh::lean_inc(v_ref_802_);
    v___f_803_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_803_, 0, v_toPure_798_);
    crate::leanh::lean_closure_set(v___f_803_, 1, v_ref_802_);
    crate::leanh::lean_closure_set(v___f_803_, 2, v_inst_799_);
    crate::leanh::lean_closure_set(v___f_803_, 3, v_toBind_800_);
    v___x_804_ = crate::leanh::lean_apply_1(v_x_801_, v_ref_802_);
    v___x_805_ = crate::leanh::lean_apply_4(
        v_toBind_800_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_804_,
        v___f_803_,
    );
    return v___x_805_;
}
pub unsafe fn l_StateRefT_x27_run___redArg(
    mut v_inst_806_: *mut crate::leanh::LeanObject,
    mut v_inst_807_: *mut crate::leanh::LeanObject,
    mut v_x_808_: *mut crate::leanh::LeanObject,
    mut v_s_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_810_ = crate::leanh::lean_ctor_get(v_inst_806_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_810_);
    v_toBind_811_ = crate::leanh::lean_ctor_get(v_inst_806_, 1);
    crate::leanh::lean_inc_n(v_toBind_811_, 2);
    crate::leanh::lean_dec_ref(v_inst_806_);
    v_toPure_812_ = crate::leanh::lean_ctor_get(v_toApplicative_810_, 1);
    crate::leanh::lean_inc(v_toPure_812_);
    crate::leanh::lean_dec_ref(v_toApplicative_810_);
    v___x_813_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_813_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_813_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_813_, 2, v_s_809_);
    crate::leanh::lean_inc(v_inst_807_);
    v___x_814_ = crate::leanh::lean_apply_2(v_inst_807_, crate::leanh::lean_box(0), v___x_813_);
    v___f_815_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_815_, 0, v_toPure_812_);
    crate::leanh::lean_closure_set(v___f_815_, 1, v_inst_807_);
    crate::leanh::lean_closure_set(v___f_815_, 2, v_toBind_811_);
    crate::leanh::lean_closure_set(v___f_815_, 3, v_x_808_);
    v___x_816_ = crate::leanh::lean_apply_4(
        v_toBind_811_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_814_,
        v___f_815_,
    );
    return v___x_816_;
}
pub unsafe fn l_StateRefT_x27_run(
    mut v_00_u03c9_817_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_818_: *mut crate::leanh::LeanObject,
    mut v_m_819_: *mut crate::leanh::LeanObject,
    mut v_inst_820_: *mut crate::leanh::LeanObject,
    mut v_inst_821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_822_: *mut crate::leanh::LeanObject,
    mut v_x_823_: *mut crate::leanh::LeanObject,
    mut v_s_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_825_ = crate::leanh::lean_ctor_get(v_inst_820_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_825_);
    v_toBind_826_ = crate::leanh::lean_ctor_get(v_inst_820_, 1);
    crate::leanh::lean_inc_n(v_toBind_826_, 2);
    crate::leanh::lean_dec_ref(v_inst_820_);
    v_toPure_827_ = crate::leanh::lean_ctor_get(v_toApplicative_825_, 1);
    crate::leanh::lean_inc(v_toPure_827_);
    crate::leanh::lean_dec_ref(v_toApplicative_825_);
    v___x_828_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_828_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_828_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_828_, 2, v_s_824_);
    crate::leanh::lean_inc(v_inst_821_);
    v___x_829_ = crate::leanh::lean_apply_2(v_inst_821_, crate::leanh::lean_box(0), v___x_828_);
    v___f_830_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_830_, 0, v_toPure_827_);
    crate::leanh::lean_closure_set(v___f_830_, 1, v_inst_821_);
    crate::leanh::lean_closure_set(v___f_830_, 2, v_toBind_826_);
    crate::leanh::lean_closure_set(v___f_830_, 3, v_x_823_);
    v___x_831_ = crate::leanh::lean_apply_4(
        v_toBind_826_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_829_,
        v___f_830_,
    );
    return v___x_831_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg___lam__0(
    mut v_toPure_832_: *mut crate::leanh::LeanObject,
    mut v_____x_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_834_ = crate::leanh::lean_ctor_get(v_____x_833_, 0);
    crate::leanh::lean_inc(v_fst_834_);
    crate::leanh::lean_dec_ref(v_____x_833_);
    v___x_835_ = crate::leanh::lean_apply_2(v_toPure_832_, crate::leanh::lean_box(0), v_fst_834_);
    return v___x_835_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg(
    mut v_inst_836_: *mut crate::leanh::LeanObject,
    mut v_inst_837_: *mut crate::leanh::LeanObject,
    mut v_x_838_: *mut crate::leanh::LeanObject,
    mut v_s_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_840_ = crate::leanh::lean_ctor_get(v_inst_836_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_840_);
    v_toBind_841_ = crate::leanh::lean_ctor_get(v_inst_836_, 1);
    crate::leanh::lean_inc_n(v_toBind_841_, 3);
    crate::leanh::lean_dec_ref(v_inst_836_);
    v_toPure_842_ = crate::leanh::lean_ctor_get(v_toApplicative_840_, 1);
    crate::leanh::lean_inc_n(v_toPure_842_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_840_);
    v___x_843_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_843_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_843_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_843_, 2, v_s_839_);
    crate::leanh::lean_inc(v_inst_837_);
    v___x_844_ = crate::leanh::lean_apply_2(v_inst_837_, crate::leanh::lean_box(0), v___x_843_);
    v___f_845_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_845_, 0, v_toPure_842_);
    v___f_846_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_846_, 0, v_toPure_842_);
    crate::leanh::lean_closure_set(v___f_846_, 1, v_inst_837_);
    crate::leanh::lean_closure_set(v___f_846_, 2, v_toBind_841_);
    crate::leanh::lean_closure_set(v___f_846_, 3, v_x_838_);
    v___x_847_ = crate::leanh::lean_apply_4(
        v_toBind_841_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_844_,
        v___f_846_,
    );
    v___x_848_ = crate::leanh::lean_apply_4(
        v_toBind_841_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_847_,
        v___f_845_,
    );
    return v___x_848_;
}
pub unsafe fn l_StateRefT_x27_run_x27(
    mut v_00_u03c9_849_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_850_: *mut crate::leanh::LeanObject,
    mut v_m_851_: *mut crate::leanh::LeanObject,
    mut v_inst_852_: *mut crate::leanh::LeanObject,
    mut v_inst_853_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_s_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_857_ = crate::leanh::lean_ctor_get(v_inst_852_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_857_);
    v_toBind_858_ = crate::leanh::lean_ctor_get(v_inst_852_, 1);
    crate::leanh::lean_inc_n(v_toBind_858_, 3);
    crate::leanh::lean_dec_ref(v_inst_852_);
    v_toPure_859_ = crate::leanh::lean_ctor_get(v_toApplicative_857_, 1);
    crate::leanh::lean_inc_n(v_toPure_859_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_857_);
    v___x_860_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_860_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_860_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_860_, 2, v_s_856_);
    crate::leanh::lean_inc(v_inst_853_);
    v___x_861_ = crate::leanh::lean_apply_2(v_inst_853_, crate::leanh::lean_box(0), v___x_860_);
    v___f_862_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_862_, 0, v_toPure_859_);
    v___f_863_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_863_, 0, v_toPure_859_);
    crate::leanh::lean_closure_set(v___f_863_, 1, v_inst_853_);
    crate::leanh::lean_closure_set(v___f_863_, 2, v_toBind_858_);
    crate::leanh::lean_closure_set(v___f_863_, 3, v_x_855_);
    v___x_864_ = crate::leanh::lean_apply_4(
        v_toBind_858_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_861_,
        v___f_863_,
    );
    v___x_865_ = crate::leanh::lean_apply_4(
        v_toBind_858_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_864_,
        v___f_862_,
    );
    return v___x_865_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg(
    mut v_x_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_866_);
    return v_x_866_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg___boxed(
    mut v_x_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_868_ = l_StateRefT_x27_lift___redArg(v_x_867_);
    crate::leanh::lean_dec(v_x_867_);
    return v_res_868_;
}
pub unsafe fn l_StateRefT_x27_lift(
    mut v_00_u03c9_869_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_870_: *mut crate::leanh::LeanObject,
    mut v_m_871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_872_: *mut crate::leanh::LeanObject,
    mut v_x_873_: *mut crate::leanh::LeanObject,
    mut v_x_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_873_);
    return v_x_873_;
}
pub unsafe fn l_StateRefT_x27_lift___boxed(
    mut v_00_u03c9_875_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_876_: *mut crate::leanh::LeanObject,
    mut v_m_877_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_x_879_: *mut crate::leanh::LeanObject,
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_StateRefT_x27_lift(
        v_00_u03c9_875_,
        v_00_u03c3_876_,
        v_m_877_,
        v_00_u03b1_878_,
        v_x_879_,
        v_x_880_,
    );
    crate::leanh::lean_dec(v_x_880_);
    crate::leanh::lean_dec(v_x_879_);
    return v_res_881_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg(
    mut v_inst_882_: *mut crate::leanh::LeanObject,
    mut v_f_883_: *mut crate::leanh::LeanObject,
    mut v_x_884_: *mut crate::leanh::LeanObject,
    mut v_r_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_886_ = crate::leanh::lean_ctor_get(v_inst_882_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_886_);
    crate::leanh::lean_dec_ref(v_inst_882_);
    v_toFunctor_887_ = crate::leanh::lean_ctor_get(v_toApplicative_886_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_887_);
    crate::leanh::lean_dec_ref(v_toApplicative_886_);
    v_map_888_ = crate::leanh::lean_ctor_get(v_toFunctor_887_, 0);
    crate::leanh::lean_inc(v_map_888_);
    crate::leanh::lean_dec_ref(v_toFunctor_887_);
    crate::leanh::lean_inc(v_r_885_);
    v___x_889_ = crate::leanh::lean_apply_1(v_x_884_, v_r_885_);
    v___x_890_ = crate::leanh::lean_apply_4(
        v_map_888_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_883_,
        v___x_889_,
    );
    return v___x_890_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg___boxed(
    mut v_inst_891_: *mut crate::leanh::LeanObject,
    mut v_f_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v_r_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ =
        l_StateRefT_x27_instMonad___aux__1___redArg(v_inst_891_, v_f_892_, v_x_893_, v_r_894_);
    crate::leanh::lean_dec(v_r_894_);
    return v_res_895_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1(
    mut v_00_u03c9_896_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_897_: *mut crate::leanh::LeanObject,
    mut v_m_898_: *mut crate::leanh::LeanObject,
    mut v_inst_899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_900_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_901_: *mut crate::leanh::LeanObject,
    mut v_f_902_: *mut crate::leanh::LeanObject,
    mut v_x_903_: *mut crate::leanh::LeanObject,
    mut v_r_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_905_ = crate::leanh::lean_ctor_get(v_inst_899_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_905_);
    crate::leanh::lean_dec_ref(v_inst_899_);
    v_toFunctor_906_ = crate::leanh::lean_ctor_get(v_toApplicative_905_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_906_);
    crate::leanh::lean_dec_ref(v_toApplicative_905_);
    v_map_907_ = crate::leanh::lean_ctor_get(v_toFunctor_906_, 0);
    crate::leanh::lean_inc(v_map_907_);
    crate::leanh::lean_dec_ref(v_toFunctor_906_);
    crate::leanh::lean_inc(v_r_904_);
    v___x_908_ = crate::leanh::lean_apply_1(v_x_903_, v_r_904_);
    v___x_909_ = crate::leanh::lean_apply_4(
        v_map_907_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_902_,
        v___x_908_,
    );
    return v___x_909_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___boxed(
    mut v_00_u03c9_910_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_911_: *mut crate::leanh::LeanObject,
    mut v_m_912_: *mut crate::leanh::LeanObject,
    mut v_inst_913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_914_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_915_: *mut crate::leanh::LeanObject,
    mut v_f_916_: *mut crate::leanh::LeanObject,
    mut v_x_917_: *mut crate::leanh::LeanObject,
    mut v_r_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_918_);
    return v_res_919_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg(
    mut v_inst_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_x_922_: *mut crate::leanh::LeanObject,
    mut v_r_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_924_ = crate::leanh::lean_ctor_get(v_inst_920_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_924_);
    crate::leanh::lean_dec_ref(v_inst_920_);
    v_toFunctor_925_ = crate::leanh::lean_ctor_get(v_toApplicative_924_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_925_);
    crate::leanh::lean_dec_ref(v_toApplicative_924_);
    v_mapConst_926_ = crate::leanh::lean_ctor_get(v_toFunctor_925_, 1);
    crate::leanh::lean_inc(v_mapConst_926_);
    crate::leanh::lean_dec_ref(v_toFunctor_925_);
    crate::leanh::lean_inc(v_r_923_);
    v___x_927_ = crate::leanh::lean_apply_1(v_x_922_, v_r_923_);
    v___x_928_ = crate::leanh::lean_apply_4(
        v_mapConst_926_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_921_,
        v___x_927_,
    );
    return v___x_928_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg___boxed(
    mut v_inst_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_x_931_: *mut crate::leanh::LeanObject,
    mut v_r_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ =
        l_StateRefT_x27_instMonad___aux__3___redArg(v_inst_929_, v_a_930_, v_x_931_, v_r_932_);
    crate::leanh::lean_dec(v_r_932_);
    return v_res_933_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3(
    mut v_00_u03c9_934_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_935_: *mut crate::leanh::LeanObject,
    mut v_m_936_: *mut crate::leanh::LeanObject,
    mut v_inst_937_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_x_941_: *mut crate::leanh::LeanObject,
    mut v_r_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_943_ = crate::leanh::lean_ctor_get(v_inst_937_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_943_);
    crate::leanh::lean_dec_ref(v_inst_937_);
    v_toFunctor_944_ = crate::leanh::lean_ctor_get(v_toApplicative_943_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_944_);
    crate::leanh::lean_dec_ref(v_toApplicative_943_);
    v_mapConst_945_ = crate::leanh::lean_ctor_get(v_toFunctor_944_, 1);
    crate::leanh::lean_inc(v_mapConst_945_);
    crate::leanh::lean_dec_ref(v_toFunctor_944_);
    crate::leanh::lean_inc(v_r_942_);
    v___x_946_ = crate::leanh::lean_apply_1(v_x_941_, v_r_942_);
    v___x_947_ = crate::leanh::lean_apply_4(
        v_mapConst_945_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_940_,
        v___x_946_,
    );
    return v___x_947_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___boxed(
    mut v_00_u03c9_948_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_949_: *mut crate::leanh::LeanObject,
    mut v_m_950_: *mut crate::leanh::LeanObject,
    mut v_inst_951_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_x_955_: *mut crate::leanh::LeanObject,
    mut v_r_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_956_);
    return v_res_957_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___redArg(
    mut v_inst_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_960_ = crate::leanh::lean_ctor_get(v_inst_958_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_960_);
    crate::leanh::lean_dec_ref(v_inst_958_);
    v_toPure_961_ = crate::leanh::lean_ctor_get(v_toApplicative_960_, 1);
    crate::leanh::lean_inc(v_toPure_961_);
    crate::leanh::lean_dec_ref(v_toApplicative_960_);
    v___x_962_ = crate::leanh::lean_apply_2(v_toPure_961_, crate::leanh::lean_box(0), v_a_959_);
    return v___x_962_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5(
    mut v_00_u03c9_963_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_964_: *mut crate::leanh::LeanObject,
    mut v_m_965_: *mut crate::leanh::LeanObject,
    mut v_inst_966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_970_ = crate::leanh::lean_ctor_get(v_inst_966_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_970_);
    crate::leanh::lean_dec_ref(v_inst_966_);
    v_toPure_971_ = crate::leanh::lean_ctor_get(v_toApplicative_970_, 1);
    crate::leanh::lean_inc(v_toPure_971_);
    crate::leanh::lean_dec_ref(v_toApplicative_970_);
    v___x_972_ = crate::leanh::lean_apply_2(v_toPure_971_, crate::leanh::lean_box(0), v_a_968_);
    return v___x_972_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___boxed(
    mut v_00_u03c9_973_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_974_: *mut crate::leanh::LeanObject,
    mut v_m_975_: *mut crate::leanh::LeanObject,
    mut v_inst_976_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_StateRefT_x27_instMonad___aux__5(
        v_00_u03c9_973_,
        v_00_u03c3_974_,
        v_m_975_,
        v_inst_976_,
        v_00_u03b1_977_,
        v_a_978_,
        v_a_979_,
    );
    crate::leanh::lean_dec(v_a_979_);
    return v_res_980_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(
    mut v_x_981_: *mut crate::leanh::LeanObject,
    mut v_r_982_: *mut crate::leanh::LeanObject,
    mut v_x_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_r_982_);
    v___x_985_ = crate::leanh::lean_apply_2(v_x_981_, v___x_984_, v_r_982_);
    return v___x_985_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_x_986_: *mut crate::leanh::LeanObject,
    mut v_r_987_: *mut crate::leanh::LeanObject,
    mut v_x_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(v_x_986_, v_r_987_, v_x_988_);
    crate::leanh::lean_dec(v_r_987_);
    return v_res_989_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg(
    mut v_inst_990_: *mut crate::leanh::LeanObject,
    mut v_f_991_: *mut crate::leanh::LeanObject,
    mut v_x_992_: *mut crate::leanh::LeanObject,
    mut v_r_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_994_ = crate::leanh::lean_ctor_get(v_inst_990_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_994_);
    crate::leanh::lean_dec_ref(v_inst_990_);
    v_toSeq_995_ = crate::leanh::lean_ctor_get(v_toApplicative_994_, 2);
    crate::leanh::lean_inc(v_toSeq_995_);
    crate::leanh::lean_dec_ref(v_toApplicative_994_);
    crate::leanh::lean_inc_n(v_r_993_, 2);
    v___f_996_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_996_, 0, v_x_992_);
    crate::leanh::lean_closure_set(v___f_996_, 1, v_r_993_);
    v___x_997_ = crate::leanh::lean_apply_1(v_f_991_, v_r_993_);
    v___x_998_ = crate::leanh::lean_apply_4(
        v_toSeq_995_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_997_,
        v___f_996_,
    );
    return v___x_998_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___boxed(
    mut v_inst_999_: *mut crate::leanh::LeanObject,
    mut v_f_1000_: *mut crate::leanh::LeanObject,
    mut v_x_1001_: *mut crate::leanh::LeanObject,
    mut v_r_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ =
        l_StateRefT_x27_instMonad___aux__7___redArg(v_inst_999_, v_f_1000_, v_x_1001_, v_r_1002_);
    crate::leanh::lean_dec(v_r_1002_);
    return v_res_1003_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7(
    mut v_00_u03c9_1004_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1005_: *mut crate::leanh::LeanObject,
    mut v_m_1006_: *mut crate::leanh::LeanObject,
    mut v_inst_1007_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1008_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1009_: *mut crate::leanh::LeanObject,
    mut v_f_1010_: *mut crate::leanh::LeanObject,
    mut v_x_1011_: *mut crate::leanh::LeanObject,
    mut v_r_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1013_ = crate::leanh::lean_ctor_get(v_inst_1007_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1013_);
    crate::leanh::lean_dec_ref(v_inst_1007_);
    v_toSeq_1014_ = crate::leanh::lean_ctor_get(v_toApplicative_1013_, 2);
    crate::leanh::lean_inc(v_toSeq_1014_);
    crate::leanh::lean_dec_ref(v_toApplicative_1013_);
    crate::leanh::lean_inc_n(v_r_1012_, 2);
    v___f_1015_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1015_, 0, v_x_1011_);
    crate::leanh::lean_closure_set(v___f_1015_, 1, v_r_1012_);
    v___x_1016_ = crate::leanh::lean_apply_1(v_f_1010_, v_r_1012_);
    v___x_1017_ = crate::leanh::lean_apply_4(
        v_toSeq_1014_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1016_,
        v___f_1015_,
    );
    return v___x_1017_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___boxed(
    mut v_00_u03c9_1018_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1019_: *mut crate::leanh::LeanObject,
    mut v_m_1020_: *mut crate::leanh::LeanObject,
    mut v_inst_1021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1022_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1023_: *mut crate::leanh::LeanObject,
    mut v_f_1024_: *mut crate::leanh::LeanObject,
    mut v_x_1025_: *mut crate::leanh::LeanObject,
    mut v_r_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_1026_);
    return v_res_1027_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(
    mut v_b_1028_: *mut crate::leanh::LeanObject,
    mut v_r_1029_: *mut crate::leanh::LeanObject,
    mut v_x_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_r_1029_);
    v___x_1032_ = crate::leanh::lean_apply_2(v_b_1028_, v___x_1031_, v_r_1029_);
    return v___x_1032_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed(
    mut v_b_1033_: *mut crate::leanh::LeanObject,
    mut v_r_1034_: *mut crate::leanh::LeanObject,
    mut v_x_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ =
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(v_b_1033_, v_r_1034_, v_x_1035_);
    crate::leanh::lean_dec(v_r_1034_);
    return v_res_1036_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg(
    mut v_inst_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_b_1039_: *mut crate::leanh::LeanObject,
    mut v_r_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1041_ = crate::leanh::lean_ctor_get(v_inst_1037_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1041_);
    crate::leanh::lean_dec_ref(v_inst_1037_);
    v_toSeqLeft_1042_ = crate::leanh::lean_ctor_get(v_toApplicative_1041_, 3);
    crate::leanh::lean_inc(v_toSeqLeft_1042_);
    crate::leanh::lean_dec_ref(v_toApplicative_1041_);
    crate::leanh::lean_inc_n(v_r_1040_, 2);
    v___f_1043_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1043_, 0, v_b_1039_);
    crate::leanh::lean_closure_set(v___f_1043_, 1, v_r_1040_);
    v___x_1044_ = crate::leanh::lean_apply_1(v_a_1038_, v_r_1040_);
    v___x_1045_ = crate::leanh::lean_apply_4(
        v_toSeqLeft_1042_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1044_,
        v___f_1043_,
    );
    return v___x_1045_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___boxed(
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_b_1048_: *mut crate::leanh::LeanObject,
    mut v_r_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ =
        l_StateRefT_x27_instMonad___aux__9___redArg(v_inst_1046_, v_a_1047_, v_b_1048_, v_r_1049_);
    crate::leanh::lean_dec(v_r_1049_);
    return v_res_1050_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9(
    mut v_00_u03c9_1051_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1052_: *mut crate::leanh::LeanObject,
    mut v_m_1053_: *mut crate::leanh::LeanObject,
    mut v_inst_1054_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1055_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1056_: *mut crate::leanh::LeanObject,
    mut v_a_1057_: *mut crate::leanh::LeanObject,
    mut v_b_1058_: *mut crate::leanh::LeanObject,
    mut v_r_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1060_ = crate::leanh::lean_ctor_get(v_inst_1054_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1060_);
    crate::leanh::lean_dec_ref(v_inst_1054_);
    v_toSeqLeft_1061_ = crate::leanh::lean_ctor_get(v_toApplicative_1060_, 3);
    crate::leanh::lean_inc(v_toSeqLeft_1061_);
    crate::leanh::lean_dec_ref(v_toApplicative_1060_);
    crate::leanh::lean_inc_n(v_r_1059_, 2);
    v___f_1062_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1062_, 0, v_b_1058_);
    crate::leanh::lean_closure_set(v___f_1062_, 1, v_r_1059_);
    v___x_1063_ = crate::leanh::lean_apply_1(v_a_1057_, v_r_1059_);
    v___x_1064_ = crate::leanh::lean_apply_4(
        v_toSeqLeft_1061_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1063_,
        v___f_1062_,
    );
    return v___x_1064_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___boxed(
    mut v_00_u03c9_1065_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1066_: *mut crate::leanh::LeanObject,
    mut v_m_1067_: *mut crate::leanh::LeanObject,
    mut v_inst_1068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_b_1072_: *mut crate::leanh::LeanObject,
    mut v_r_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_1073_);
    return v_res_1074_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg(
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_b_1077_: *mut crate::leanh::LeanObject,
    mut v_r_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1079_ = crate::leanh::lean_ctor_get(v_inst_1075_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1079_);
    crate::leanh::lean_dec_ref(v_inst_1075_);
    v_toSeqRight_1080_ = crate::leanh::lean_ctor_get(v_toApplicative_1079_, 4);
    crate::leanh::lean_inc(v_toSeqRight_1080_);
    crate::leanh::lean_dec_ref(v_toApplicative_1079_);
    crate::leanh::lean_inc_n(v_r_1078_, 2);
    v___f_1081_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1081_, 0, v_b_1077_);
    crate::leanh::lean_closure_set(v___f_1081_, 1, v_r_1078_);
    v___x_1082_ = crate::leanh::lean_apply_1(v_a_1076_, v_r_1078_);
    v___x_1083_ = crate::leanh::lean_apply_4(
        v_toSeqRight_1080_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1082_,
        v___f_1081_,
    );
    return v___x_1083_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg___boxed(
    mut v_inst_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_b_1086_: *mut crate::leanh::LeanObject,
    mut v_r_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ =
        l_StateRefT_x27_instMonad___aux__11___redArg(v_inst_1084_, v_a_1085_, v_b_1086_, v_r_1087_);
    crate::leanh::lean_dec(v_r_1087_);
    return v_res_1088_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11(
    mut v_00_u03c9_1089_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1090_: *mut crate::leanh::LeanObject,
    mut v_m_1091_: *mut crate::leanh::LeanObject,
    mut v_inst_1092_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1093_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
    mut v_b_1096_: *mut crate::leanh::LeanObject,
    mut v_r_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = crate::leanh::lean_ctor_get(v_inst_1092_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1098_);
    crate::leanh::lean_dec_ref(v_inst_1092_);
    v_toSeqRight_1099_ = crate::leanh::lean_ctor_get(v_toApplicative_1098_, 4);
    crate::leanh::lean_inc(v_toSeqRight_1099_);
    crate::leanh::lean_dec_ref(v_toApplicative_1098_);
    crate::leanh::lean_inc_n(v_r_1097_, 2);
    v___f_1100_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1100_, 0, v_b_1096_);
    crate::leanh::lean_closure_set(v___f_1100_, 1, v_r_1097_);
    v___x_1101_ = crate::leanh::lean_apply_1(v_a_1095_, v_r_1097_);
    v___x_1102_ = crate::leanh::lean_apply_4(
        v_toSeqRight_1099_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1101_,
        v___f_1100_,
    );
    return v___x_1102_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___boxed(
    mut v_00_u03c9_1103_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1104_: *mut crate::leanh::LeanObject,
    mut v_m_1105_: *mut crate::leanh::LeanObject,
    mut v_inst_1106_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1107_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_b_1110_: *mut crate::leanh::LeanObject,
    mut v_r_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_1111_);
    return v_res_1112_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(
    mut v_f_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1114_);
    v___x_1116_ = crate::leanh::lean_apply_2(v_f_1113_, v_a_1115_, v_a_1114_);
    return v___x_1116_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_f_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ =
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(v_f_1117_, v_a_1118_, v_a_1119_);
    crate::leanh::lean_dec(v_a_1118_);
    return v_res_1120_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg(
    mut v_inst_1121_: *mut crate::leanh::LeanObject,
    mut v_x_1122_: *mut crate::leanh::LeanObject,
    mut v_f_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1125_ = crate::leanh::lean_ctor_get(v_inst_1121_, 1);
    crate::leanh::lean_inc(v_toBind_1125_);
    crate::leanh::lean_dec_ref(v_inst_1121_);
    crate::leanh::lean_inc_n(v_a_1124_, 2);
    v___f_1126_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1126_, 0, v_f_1123_);
    crate::leanh::lean_closure_set(v___f_1126_, 1, v_a_1124_);
    v___x_1127_ = crate::leanh::lean_apply_1(v_x_1122_, v_a_1124_);
    v___x_1128_ = crate::leanh::lean_apply_4(
        v_toBind_1125_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1127_,
        v___f_1126_,
    );
    return v___x_1128_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___boxed(
    mut v_inst_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
    mut v_f_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ =
        l_StateRefT_x27_instMonad___aux__13___redArg(v_inst_1129_, v_x_1130_, v_f_1131_, v_a_1132_);
    crate::leanh::lean_dec(v_a_1132_);
    return v_res_1133_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13(
    mut v_00_u03c9_1134_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1135_: *mut crate::leanh::LeanObject,
    mut v_m_1136_: *mut crate::leanh::LeanObject,
    mut v_inst_1137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v_f_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1143_ = crate::leanh::lean_ctor_get(v_inst_1137_, 1);
    crate::leanh::lean_inc(v_toBind_1143_);
    crate::leanh::lean_dec_ref(v_inst_1137_);
    crate::leanh::lean_inc_n(v_a_1142_, 2);
    v___f_1144_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1144_, 0, v_f_1141_);
    crate::leanh::lean_closure_set(v___f_1144_, 1, v_a_1142_);
    v___x_1145_ = crate::leanh::lean_apply_1(v_x_1140_, v_a_1142_);
    v___x_1146_ = crate::leanh::lean_apply_4(
        v_toBind_1143_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1145_,
        v___f_1144_,
    );
    return v___x_1146_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___boxed(
    mut v_00_u03c9_1147_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1148_: *mut crate::leanh::LeanObject,
    mut v_m_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1151_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
    mut v_f_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1155_);
    return v_res_1156_;
}
pub unsafe fn l_StateRefT_x27_instMonad___redArg(
    mut v_inst_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1157_, 6);
    v___x_1158_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1158_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1158_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1158_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1158_, 3, v_inst_1157_);
    v___x_1159_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1159_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1159_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1159_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1159_, 3, v_inst_1157_);
    v___x_1160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    v___x_1161_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1161_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1161_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1161_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1161_, 3, v_inst_1157_);
    v___x_1162_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1162_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1162_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1162_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1162_, 3, v_inst_1157_);
    v___x_1163_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1163_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1163_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1163_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1163_, 3, v_inst_1157_);
    v___x_1164_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1164_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1164_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1164_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1164_, 3, v_inst_1157_);
    v___x_1165_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1160_);
    crate::leanh::lean_ctor_set(v___x_1165_, 1, v___x_1161_);
    crate::leanh::lean_ctor_set(v___x_1165_, 2, v___x_1162_);
    crate::leanh::lean_ctor_set(v___x_1165_, 3, v___x_1163_);
    crate::leanh::lean_ctor_set(v___x_1165_, 4, v___x_1164_);
    v___x_1166_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1166_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1166_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1166_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1166_, 3, v_inst_1157_);
    v___x_1167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1165_);
    crate::leanh::lean_ctor_set(v___x_1167_, 1, v___x_1166_);
    return v___x_1167_;
}
pub unsafe fn l_StateRefT_x27_instMonad(
    mut v_00_u03c9_1168_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1169_: *mut crate::leanh::LeanObject,
    mut v_m_1170_: *mut crate::leanh::LeanObject,
    mut v_inst_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_StateRefT_x27_instMonad___redArg(v_inst_1171_);
    return v___x_1172_;
}
pub unsafe fn l_StateRefT_x27_instMonadLift(
    mut v_00_u03c9_1174_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1175_: *mut crate::leanh::LeanObject,
    mut v_m_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_StateRefT_x27_instMonadLift___closed__0;
    return v___x_1177_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg(
    mut v_f_1178_: *mut crate::leanh::LeanObject,
    mut v_x_1179_: *mut crate::leanh::LeanObject,
    mut v_ctx_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1180_);
    v___x_1181_ = crate::leanh::lean_apply_1(v_x_1179_, v_ctx_1180_);
    v___x_1182_ = crate::leanh::lean_apply_2(v_f_1178_, crate::leanh::lean_box(0), v___x_1181_);
    return v___x_1182_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(
    mut v_f_1183_: *mut crate::leanh::LeanObject,
    mut v_x_1184_: *mut crate::leanh::LeanObject,
    mut v_ctx_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_1183_, v_x_1184_, v_ctx_1185_);
    crate::leanh::lean_dec(v_ctx_1185_);
    return v_res_1186_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1(
    mut v_00_u03c9_1187_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1188_: *mut crate::leanh::LeanObject,
    mut v_m_1189_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1190_: *mut crate::leanh::LeanObject,
    mut v_f_1191_: *mut crate::leanh::LeanObject,
    mut v_x_1192_: *mut crate::leanh::LeanObject,
    mut v_ctx_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1193_);
    v___x_1194_ = crate::leanh::lean_apply_1(v_x_1192_, v_ctx_1193_);
    v___x_1195_ = crate::leanh::lean_apply_2(v_f_1191_, crate::leanh::lean_box(0), v___x_1194_);
    return v___x_1195_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___boxed(
    mut v_00_u03c9_1196_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1197_: *mut crate::leanh::LeanObject,
    mut v_m_1198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1199_: *mut crate::leanh::LeanObject,
    mut v_f_1200_: *mut crate::leanh::LeanObject,
    mut v_x_1201_: *mut crate::leanh::LeanObject,
    mut v_ctx_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_StateRefT_x27_instMonadFunctor___aux__1(
        v_00_u03c9_1196_,
        v_00_u03c3_1197_,
        v_m_1198_,
        v_00_u03b1_1199_,
        v_f_1200_,
        v_x_1201_,
        v_ctx_1202_,
    );
    crate::leanh::lean_dec(v_ctx_1202_);
    return v_res_1203_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor(
    mut v_00_u03c9_1205_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1206_: *mut crate::leanh::LeanObject,
    mut v_m_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_StateRefT_x27_instMonadFunctor___closed__0;
    return v___x_1208_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___redArg(
    mut v_inst_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_1210_ = crate::leanh::lean_ctor_get(v_inst_1209_, 1);
    crate::leanh::lean_inc(v_failure_1210_);
    crate::leanh::lean_dec_ref(v_inst_1209_);
    v___x_1211_ = crate::leanh::lean_apply_1(v_failure_1210_, crate::leanh::lean_box(0));
    return v___x_1211_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1(
    mut v_00_u03c9_1212_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1213_: *mut crate::leanh::LeanObject,
    mut v_m_1214_: *mut crate::leanh::LeanObject,
    mut v_inst_1215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1216_: *mut crate::leanh::LeanObject,
    mut v_a_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_1218_ = crate::leanh::lean_ctor_get(v_inst_1215_, 1);
    crate::leanh::lean_inc(v_failure_1218_);
    crate::leanh::lean_dec_ref(v_inst_1215_);
    v___x_1219_ = crate::leanh::lean_apply_1(v_failure_1218_, crate::leanh::lean_box(0));
    return v___x_1219_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed(
    mut v_00_u03c9_1220_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1221_: *mut crate::leanh::LeanObject,
    mut v_m_1222_: *mut crate::leanh::LeanObject,
    mut v_inst_1223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1224_: *mut crate::leanh::LeanObject,
    mut v_a_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_StateRefT_x27_instAlternativeOfMonad___aux__1(
        v_00_u03c9_1220_,
        v_00_u03c3_1221_,
        v_m_1222_,
        v_inst_1223_,
        v_00_u03b1_1224_,
        v_a_1225_,
    );
    crate::leanh::lean_dec(v_a_1225_);
    return v_res_1226_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
    mut v_x_u2082_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_x_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_a_1228_);
    v___x_1231_ = crate::leanh::lean_apply_2(v_x_u2082_1227_, v___x_1230_, v_a_1228_);
    return v___x_1231_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_u2082_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_x_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
        v_x_u2082_1232_,
        v_a_1233_,
        v_x_1234_,
    );
    crate::leanh::lean_dec(v_a_1233_);
    return v_res_1235_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
    mut v_inst_1236_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1237_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1240_ = crate::leanh::lean_ctor_get(v_inst_1236_, 2);
    crate::leanh::lean_inc(v_orElse_1240_);
    crate::leanh::lean_dec_ref(v_inst_1236_);
    crate::leanh::lean_inc_n(v_a_1239_, 2);
    v___f_1241_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1241_, 0, v_x_u2082_1238_);
    crate::leanh::lean_closure_set(v___f_1241_, 1, v_a_1239_);
    v___x_1242_ = crate::leanh::lean_apply_1(v_x_u2081_1237_, v_a_1239_);
    v___x_1243_ = crate::leanh::lean_apply_3(
        v_orElse_1240_,
        crate::leanh::lean_box(0),
        v___x_1242_,
        v___f_1241_,
    );
    return v___x_1243_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___boxed(
    mut v_inst_1244_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1245_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
        v_inst_1244_,
        v_x_u2081_1245_,
        v_x_u2082_1246_,
        v_a_1247_,
    );
    crate::leanh::lean_dec(v_a_1247_);
    return v_res_1248_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3(
    mut v_00_u03c9_1249_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1250_: *mut crate::leanh::LeanObject,
    mut v_m_1251_: *mut crate::leanh::LeanObject,
    mut v_inst_1252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1253_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1254_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1257_ = crate::leanh::lean_ctor_get(v_inst_1252_, 2);
    crate::leanh::lean_inc(v_orElse_1257_);
    crate::leanh::lean_dec_ref(v_inst_1252_);
    crate::leanh::lean_inc_n(v_a_1256_, 2);
    v___f_1258_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1258_, 0, v_x_u2082_1255_);
    crate::leanh::lean_closure_set(v___f_1258_, 1, v_a_1256_);
    v___x_1259_ = crate::leanh::lean_apply_1(v_x_u2081_1254_, v_a_1256_);
    v___x_1260_ = crate::leanh::lean_apply_3(
        v_orElse_1257_,
        crate::leanh::lean_box(0),
        v___x_1259_,
        v___f_1258_,
    );
    return v___x_1260_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed(
    mut v_00_u03c9_1261_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1262_: *mut crate::leanh::LeanObject,
    mut v_m_1263_: *mut crate::leanh::LeanObject,
    mut v_inst_1264_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1265_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1266_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1268_);
    return v_res_1269_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___redArg(
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
    mut v_inst_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_StateRefT_x27_instMonad___redArg(v_inst_1271_);
    v_toApplicative_1273_ = crate::leanh::lean_ctor_get(v___x_1272_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1273_);
    crate::leanh::lean_dec_ref(v___x_1272_);
    crate::leanh::lean_inc_ref(v_inst_1270_);
    v___x_1274_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1274_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1274_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1274_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1274_, 3, v_inst_1270_);
    v___x_1275_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1275_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1275_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1275_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1275_, 3, v_inst_1270_);
    v___x_1276_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1276_, 0, v_toApplicative_1273_);
    crate::leanh::lean_ctor_set(v___x_1276_, 1, v___x_1274_);
    crate::leanh::lean_ctor_set(v___x_1276_, 2, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad(
    mut v_00_u03c9_1277_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1278_: *mut crate::leanh::LeanObject,
    mut v_m_1279_: *mut crate::leanh::LeanObject,
    mut v_inst_1280_: *mut crate::leanh::LeanObject,
    mut v_inst_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_1280_, v_inst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(
    mut v_x_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1283_);
    return v_x_1283_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(v_x_1284_);
    crate::leanh::lean_dec(v_x_1284_);
    return v_res_1285_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
    mut v_inst_1287_: *mut crate::leanh::LeanObject,
    mut v_inst_1288_: *mut crate::leanh::LeanObject,
    mut v_x_1289_: *mut crate::leanh::LeanObject,
    mut v_r_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1291_ = crate::leanh::lean_ctor_get(v_inst_1287_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1291_);
    crate::leanh::lean_dec_ref(v_inst_1287_);
    v_toFunctor_1292_ = crate::leanh::lean_ctor_get(v_toApplicative_1291_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1292_);
    crate::leanh::lean_dec_ref(v_toApplicative_1291_);
    v_map_1293_ = crate::leanh::lean_ctor_get(v_toFunctor_1292_, 0);
    crate::leanh::lean_inc(v_map_1293_);
    crate::leanh::lean_dec_ref(v_toFunctor_1292_);
    v___f_1294_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    crate::leanh::lean_inc(v_r_1290_);
    v___x_1295_ = crate::leanh::lean_apply_1(v_x_1289_, v_r_1290_);
    v___x_1296_ = crate::leanh::lean_apply_2(v_inst_1288_, crate::leanh::lean_box(0), v___x_1295_);
    v___x_1297_ = crate::leanh::lean_apply_4(
        v_map_1293_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1294_,
        v___x_1296_,
    );
    return v___x_1297_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___boxed(
    mut v_inst_1298_: *mut crate::leanh::LeanObject,
    mut v_inst_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v_r_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
        v_inst_1298_,
        v_inst_1299_,
        v_x_1300_,
        v_r_1301_,
    );
    crate::leanh::lean_dec(v_r_1301_);
    return v_res_1302_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3(
    mut v_00_u03c9_1303_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1304_: *mut crate::leanh::LeanObject,
    mut v_m_1305_: *mut crate::leanh::LeanObject,
    mut v_inst_1306_: *mut crate::leanh::LeanObject,
    mut v_inst_1307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1308_: *mut crate::leanh::LeanObject,
    mut v_x_1309_: *mut crate::leanh::LeanObject,
    mut v_r_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1311_ = crate::leanh::lean_ctor_get(v_inst_1306_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1311_);
    crate::leanh::lean_dec_ref(v_inst_1306_);
    v_toFunctor_1312_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1312_);
    crate::leanh::lean_dec_ref(v_toApplicative_1311_);
    v_map_1313_ = crate::leanh::lean_ctor_get(v_toFunctor_1312_, 0);
    crate::leanh::lean_inc(v_map_1313_);
    crate::leanh::lean_dec_ref(v_toFunctor_1312_);
    v___f_1314_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    crate::leanh::lean_inc(v_r_1310_);
    v___x_1315_ = crate::leanh::lean_apply_1(v_x_1309_, v_r_1310_);
    v___x_1316_ = crate::leanh::lean_apply_2(v_inst_1307_, crate::leanh::lean_box(0), v___x_1315_);
    v___x_1317_ = crate::leanh::lean_apply_4(
        v_map_1313_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1314_,
        v___x_1316_,
    );
    return v___x_1317_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed(
    mut v_00_u03c9_1318_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1319_: *mut crate::leanh::LeanObject,
    mut v_m_1320_: *mut crate::leanh::LeanObject,
    mut v_inst_1321_: *mut crate::leanh::LeanObject,
    mut v_inst_1322_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1323_: *mut crate::leanh::LeanObject,
    mut v_x_1324_: *mut crate::leanh::LeanObject,
    mut v_r_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_r_1325_);
    return v_res_1326_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___redArg(
    mut v_inst_1327_: *mut crate::leanh::LeanObject,
    mut v_inst_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1329_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1329_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1329_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1329_, 3, v_inst_1327_);
    crate::leanh::lean_closure_set(v___x_1329_, 4, v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad(
    mut v_00_u03c9_1330_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1331_: *mut crate::leanh::LeanObject,
    mut v_m_1332_: *mut crate::leanh::LeanObject,
    mut v_inst_1333_: *mut crate::leanh::LeanObject,
    mut v_inst_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1335_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1335_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1335_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1335_, 3, v_inst_1333_);
    crate::leanh::lean_closure_set(v___x_1335_, 4, v_inst_1334_);
    return v___x_1335_;
}
pub unsafe fn l_StateRefT_x27_get___redArg(
    mut v_inst_1336_: *mut crate::leanh::LeanObject,
    mut v_ref_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1337_);
    v___x_1338_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1338_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1338_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1338_, 2, v_ref_1337_);
    v___x_1339_ = crate::leanh::lean_apply_2(v_inst_1336_, crate::leanh::lean_box(0), v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_StateRefT_x27_get___redArg___boxed(
    mut v_inst_1340_: *mut crate::leanh::LeanObject,
    mut v_ref_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_StateRefT_x27_get___redArg(v_inst_1340_, v_ref_1341_);
    crate::leanh::lean_dec(v_ref_1341_);
    return v_res_1342_;
}
pub unsafe fn l_StateRefT_x27_get(
    mut v_00_u03c9_1343_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1344_: *mut crate::leanh::LeanObject,
    mut v_m_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_ref_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1347_);
    v___x_1348_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1348_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1348_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1348_, 2, v_ref_1347_);
    v___x_1349_ = crate::leanh::lean_apply_2(v_inst_1346_, crate::leanh::lean_box(0), v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_StateRefT_x27_get___boxed(
    mut v_00_u03c9_1350_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1351_: *mut crate::leanh::LeanObject,
    mut v_m_1352_: *mut crate::leanh::LeanObject,
    mut v_inst_1353_: *mut crate::leanh::LeanObject,
    mut v_ref_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_StateRefT_x27_get(
        v_00_u03c9_1350_,
        v_00_u03c3_1351_,
        v_m_1352_,
        v_inst_1353_,
        v_ref_1354_,
    );
    crate::leanh::lean_dec(v_ref_1354_);
    return v_res_1355_;
}
pub unsafe fn l_StateRefT_x27_set___redArg(
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_s_1357_: *mut crate::leanh::LeanObject,
    mut v_ref_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1358_);
    v___x_1359_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_1359_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1359_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1359_, 2, v_ref_1358_);
    crate::leanh::lean_closure_set(v___x_1359_, 3, v_s_1357_);
    v___x_1360_ = crate::leanh::lean_apply_2(v_inst_1356_, crate::leanh::lean_box(0), v___x_1359_);
    return v___x_1360_;
}
pub unsafe fn l_StateRefT_x27_set___redArg___boxed(
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_s_1362_: *mut crate::leanh::LeanObject,
    mut v_ref_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_StateRefT_x27_set___redArg(v_inst_1361_, v_s_1362_, v_ref_1363_);
    crate::leanh::lean_dec(v_ref_1363_);
    return v_res_1364_;
}
pub unsafe fn l_StateRefT_x27_set(
    mut v_00_u03c9_1365_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1366_: *mut crate::leanh::LeanObject,
    mut v_m_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
    mut v_s_1369_: *mut crate::leanh::LeanObject,
    mut v_ref_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1370_);
    v___x_1371_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_1371_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1371_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1371_, 2, v_ref_1370_);
    crate::leanh::lean_closure_set(v___x_1371_, 3, v_s_1369_);
    v___x_1372_ = crate::leanh::lean_apply_2(v_inst_1368_, crate::leanh::lean_box(0), v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_StateRefT_x27_set___boxed(
    mut v_00_u03c9_1373_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1374_: *mut crate::leanh::LeanObject,
    mut v_m_1375_: *mut crate::leanh::LeanObject,
    mut v_inst_1376_: *mut crate::leanh::LeanObject,
    mut v_s_1377_: *mut crate::leanh::LeanObject,
    mut v_ref_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_StateRefT_x27_set(
        v_00_u03c9_1373_,
        v_00_u03c3_1374_,
        v_m_1375_,
        v_inst_1376_,
        v_s_1377_,
        v_ref_1378_,
    );
    crate::leanh::lean_dec(v_ref_1378_);
    return v_res_1379_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg(
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_f_1381_: *mut crate::leanh::LeanObject,
    mut v_ref_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1382_);
    v___x_1383_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1383_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1383_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1383_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1383_, 3, v_ref_1382_);
    crate::leanh::lean_closure_set(v___x_1383_, 4, v_f_1381_);
    v___x_1384_ = crate::leanh::lean_apply_2(v_inst_1380_, crate::leanh::lean_box(0), v___x_1383_);
    return v___x_1384_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg___boxed(
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
    mut v_f_1386_: *mut crate::leanh::LeanObject,
    mut v_ref_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_StateRefT_x27_modifyGet___redArg(v_inst_1385_, v_f_1386_, v_ref_1387_);
    crate::leanh::lean_dec(v_ref_1387_);
    return v_res_1388_;
}
pub unsafe fn l_StateRefT_x27_modifyGet(
    mut v_00_u03c9_1389_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1390_: *mut crate::leanh::LeanObject,
    mut v_m_1391_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1392_: *mut crate::leanh::LeanObject,
    mut v_inst_1393_: *mut crate::leanh::LeanObject,
    mut v_f_1394_: *mut crate::leanh::LeanObject,
    mut v_ref_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ref_1395_);
    v___x_1396_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1396_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1396_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1396_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1396_, 3, v_ref_1395_);
    crate::leanh::lean_closure_set(v___x_1396_, 4, v_f_1394_);
    v___x_1397_ = crate::leanh::lean_apply_2(v_inst_1393_, crate::leanh::lean_box(0), v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___boxed(
    mut v_00_u03c9_1398_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1399_: *mut crate::leanh::LeanObject,
    mut v_m_1400_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1401_: *mut crate::leanh::LeanObject,
    mut v_inst_1402_: *mut crate::leanh::LeanObject,
    mut v_f_1403_: *mut crate::leanh::LeanObject,
    mut v_ref_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_StateRefT_x27_modifyGet(
        v_00_u03c9_1398_,
        v_00_u03c3_1399_,
        v_m_1400_,
        v_00_u03b1_1401_,
        v_inst_1402_,
        v_f_1403_,
        v_ref_1404_,
    );
    crate::leanh::lean_dec(v_ref_1404_);
    return v_res_1405_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
    mut v_inst_1406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1409_);
    v___x_1410_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1410_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1410_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1410_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1410_, 3, v___y_1409_);
    crate::leanh::lean_closure_set(v___x_1410_, 4, v___y_1408_);
    v___x_1411_ = crate::leanh::lean_apply_2(v_inst_1406_, crate::leanh::lean_box(0), v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
        v_inst_1412_,
        v_00_u03b1_1413_,
        v___y_1414_,
        v___y_1415_,
    );
    crate::leanh::lean_dec(v___y_1415_);
    return v_res_1416_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_inst_1417_, 2);
    v___f_1418_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1418_, 0, v_inst_1417_);
    v___x_1419_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1419_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1419_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1419_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1419_, 3, v_inst_1417_);
    v___x_1420_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_set___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1420_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1420_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1420_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1420_, 3, v_inst_1417_);
    v___x_1421_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1421_, 0, v___x_1419_);
    crate::leanh::lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    crate::leanh::lean_ctor_set(v___x_1421_, 2, v___f_1418_);
    return v___x_1421_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(
    mut v_00_u03c9_1422_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1423_: *mut crate::leanh::LeanObject,
    mut v_m_1424_: *mut crate::leanh::LeanObject,
    mut v_inst_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_1425_);
    return v___x_1426_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
    mut v_inst_1427_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_1431_ = crate::leanh::lean_ctor_get(v_inst_1427_, 0);
    crate::leanh::lean_inc(v_throw_1431_);
    crate::leanh::lean_dec_ref(v_inst_1427_);
    v___x_1432_ = crate::leanh::lean_apply_2(v_throw_1431_, crate::leanh::lean_box(0), v___y_1429_);
    return v___x_1432_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(
    mut v_inst_1433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
        v_inst_1433_,
        v_00_u03b1_1434_,
        v___y_1435_,
        v___y_1436_,
    );
    crate::leanh::lean_dec(v___y_1436_);
    return v_res_1437_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(
    mut v_c_1438_: *mut crate::leanh::LeanObject,
    mut v_s_1439_: *mut crate::leanh::LeanObject,
    mut v_e_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = crate::leanh::lean_apply_2(v_c_1438_, v_e_1440_, v_s_1439_);
    return v___x_1441_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(
    mut v_inst_1442_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1443_: *mut crate::leanh::LeanObject,
    mut v_x_1444_: *mut crate::leanh::LeanObject,
    mut v_c_1445_: *mut crate::leanh::LeanObject,
    mut v_s_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_1447_ = crate::leanh::lean_ctor_get(v_inst_1442_, 1);
    crate::leanh::lean_inc(v_tryCatch_1447_);
    crate::leanh::lean_dec_ref(v_inst_1442_);
    crate::leanh::lean_inc(v_s_1446_);
    v___f_1448_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1448_, 0, v_c_1445_);
    crate::leanh::lean_closure_set(v___f_1448_, 1, v_s_1446_);
    v___x_1449_ = crate::leanh::lean_apply_1(v_x_1444_, v_s_1446_);
    v___x_1450_ = crate::leanh::lean_apply_3(
        v_tryCatch_1447_,
        crate::leanh::lean_box(0),
        v___x_1449_,
        v___f_1448_,
    );
    return v___x_1450_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg(
    mut v_inst_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1451_);
    v___f_1452_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1452_, 0, v_inst_1451_);
    v___f_1453_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1453_, 0, v_inst_1451_);
    v___x_1454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1454_, 0, v___f_1452_);
    crate::leanh::lean_ctor_set(v___x_1454_, 1, v___f_1453_);
    return v___x_1454_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf(
    mut v_00_u03c9_1455_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1456_: *mut crate::leanh::LeanObject,
    mut v_m_1457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1458_: *mut crate::leanh::LeanObject,
    mut v_inst_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1459_);
    v___f_1460_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1460_, 0, v_inst_1459_);
    v___f_1461_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1461_, 0, v_inst_1459_);
    v___x_1462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___f_1460_);
    crate::leanh::lean_ctor_set(v___x_1462_, 1, v___f_1461_);
    return v___x_1462_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
    mut v_ctx_1463_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1464_: *mut crate::leanh::LeanObject,
    mut v_x_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1463_);
    v___x_1466_ = crate::leanh::lean_apply_1(v_x_1465_, v_ctx_1463_);
    return v___x_1466_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_ctx_1467_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1468_: *mut crate::leanh::LeanObject,
    mut v_x_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
        v_ctx_1467_,
        v_00_u03b2_1468_,
        v_x_1469_,
    );
    crate::leanh::lean_dec(v_ctx_1467_);
    return v_res_1470_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg(
    mut v_f_1471_: *mut crate::leanh::LeanObject,
    mut v_ctx_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1472_);
    v___f_1473_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1473_, 0, v_ctx_1472_);
    v___x_1474_ = crate::leanh::lean_apply_1(v_f_1471_, v___f_1473_);
    return v___x_1474_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(
    mut v_f_1475_: *mut crate::leanh::LeanObject,
    mut v_ctx_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_1475_, v_ctx_1476_);
    crate::leanh::lean_dec(v_ctx_1476_);
    return v_res_1477_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1(
    mut v_00_u03c9_1478_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1479_: *mut crate::leanh::LeanObject,
    mut v_m_1480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1481_: *mut crate::leanh::LeanObject,
    mut v_f_1482_: *mut crate::leanh::LeanObject,
    mut v_ctx_1483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1483_);
    v___f_1484_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1484_, 0, v_ctx_1483_);
    v___x_1485_ = crate::leanh::lean_apply_1(v_f_1482_, v___f_1484_);
    return v___x_1485_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___boxed(
    mut v_00_u03c9_1486_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1487_: *mut crate::leanh::LeanObject,
    mut v_m_1488_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1489_: *mut crate::leanh::LeanObject,
    mut v_f_1490_: *mut crate::leanh::LeanObject,
    mut v_ctx_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l_instMonadControlStateRefT_x27___aux__1(
        v_00_u03c9_1486_,
        v_00_u03c3_1487_,
        v_m_1488_,
        v_00_u03b1_1489_,
        v_f_1490_,
        v_ctx_1491_,
    );
    crate::leanh::lean_dec(v_ctx_1491_);
    return v_res_1492_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg(
    mut v_x_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1493_);
    return v_x_1493_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(
    mut v_x_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_1494_);
    crate::leanh::lean_dec(v_x_1494_);
    return v_res_1495_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3(
    mut v_00_u03c9_1496_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1497_: *mut crate::leanh::LeanObject,
    mut v_m_1498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
    mut v_x_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1500_);
    return v_x_1500_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___boxed(
    mut v_00_u03c9_1502_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1503_: *mut crate::leanh::LeanObject,
    mut v_m_1504_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1505_: *mut crate::leanh::LeanObject,
    mut v_x_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_instMonadControlStateRefT_x27___aux__3(
        v_00_u03c9_1502_,
        v_00_u03c3_1503_,
        v_m_1504_,
        v_00_u03b1_1505_,
        v_x_1506_,
        v_x_1507_,
    );
    crate::leanh::lean_dec(v_x_1507_);
    crate::leanh::lean_dec(v_x_1506_);
    return v_res_1508_;
}
pub unsafe fn l_instMonadControlStateRefT_x27(
    mut v_00_u03c9_1514_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1515_: *mut crate::leanh::LeanObject,
    mut v_m_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_instMonadControlStateRefT_x27___closed__2;
    return v___x_1517_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
    mut v_h_1518_: *mut crate::leanh::LeanObject,
    mut v_ctx_1519_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_ctx_1519_);
    v___x_1521_ = crate::leanh::lean_apply_2(v_h_1518_, v_a_x3f_1520_, v_ctx_1519_);
    return v___x_1521_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_h_1522_: *mut crate::leanh::LeanObject,
    mut v_ctx_1523_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
        v_h_1522_,
        v_ctx_1523_,
        v_a_x3f_1524_,
    );
    crate::leanh::lean_dec(v_ctx_1523_);
    return v_res_1525_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg(
    mut v_inst_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
    mut v_h_1528_: *mut crate::leanh::LeanObject,
    mut v_ctx_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_ctx_1529_, 2);
    v___f_1530_ = crate::leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1530_, 0, v_h_1528_);
    crate::leanh::lean_closure_set(v___f_1530_, 1, v_ctx_1529_);
    v___x_1531_ = crate::leanh::lean_apply_1(v_x_1527_, v_ctx_1529_);
    v___x_1532_ = crate::leanh::lean_apply_4(
        v_inst_1526_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1531_,
        v___f_1530_,
    );
    return v___x_1532_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(
    mut v_inst_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_h_1535_: *mut crate::leanh::LeanObject,
    mut v_ctx_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(
        v_inst_1533_,
        v_x_1534_,
        v_h_1535_,
        v_ctx_1536_,
    );
    crate::leanh::lean_dec(v_ctx_1536_);
    return v_res_1537_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1(
    mut v_m_1538_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_1539_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1540_: *mut crate::leanh::LeanObject,
    mut v_inst_1541_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1543_: *mut crate::leanh::LeanObject,
    mut v_x_1544_: *mut crate::leanh::LeanObject,
    mut v_h_1545_: *mut crate::leanh::LeanObject,
    mut v_ctx_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_ctx_1546_, 2);
    v___f_1547_ = crate::leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1547_, 0, v_h_1545_);
    crate::leanh::lean_closure_set(v___f_1547_, 1, v_ctx_1546_);
    v___x_1548_ = crate::leanh::lean_apply_1(v_x_1544_, v_ctx_1546_);
    v___x_1549_ = crate::leanh::lean_apply_4(
        v_inst_1541_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1548_,
        v___f_1547_,
    );
    return v___x_1549_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___boxed(
    mut v_m_1550_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_1551_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1552_: *mut crate::leanh::LeanObject,
    mut v_inst_1553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1554_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut crate::leanh::LeanObject,
    mut v_x_1556_: *mut crate::leanh::LeanObject,
    mut v_h_1557_: *mut crate::leanh::LeanObject,
    mut v_ctx_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_ctx_1558_);
    return v_res_1559_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___redArg(
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = crate::leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1561_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1561_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1561_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1561_, 3, v_inst_1560_);
    return v___x_1561_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27(
    mut v_m_1562_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_1563_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1564_: *mut crate::leanh::LeanObject,
    mut v_inst_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = crate::leanh::lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1566_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1566_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1566_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1566_, 3, v_inst_1565_);
    return v___x_1566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_StateRef(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_ST(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Reader(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_StateRef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_StateRef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_ST(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Reader(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_StateRef(builtin);
}
