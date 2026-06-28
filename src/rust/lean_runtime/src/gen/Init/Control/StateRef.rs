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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_StateRefT_x27_instMonadLift___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadLift___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadLift___closed__0_value) as *mut LeanObject;
pub static l_StateRefT_x27_instMonadFunctor___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_StateRefT_x27_instMonadFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadFunctor___closed__0_value) as *mut LeanObject;
pub static l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value:
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
    m_fun: l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value) as *mut LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__1_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlStateRefT_x27___aux__3___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_instMonadControlStateRefT_x27___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value) as *mut LeanObject;
pub static l_instMonadControlStateRefT_x27___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadControlStateRefT_x27___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlStateRefT_x27___closed__2_value) as *mut LeanObject;
pub unsafe fn l_StateRefT_x27_run___redArg___lam__0(
    mut v_a_784_: *mut LeanObject,
    mut v_toPure_785_: *mut LeanObject,
    mut v_s_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_787_, 0, v_a_784_);
    lean_ctor_set(v___x_787_, 1, v_s_786_);
    v___x_788_ = lean_apply_2(v_toPure_785_, lean_box(0), v___x_787_);
    return v___x_788_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__1(
    mut v_toPure_789_: *mut LeanObject,
    mut v_ref_790_: *mut LeanObject,
    mut v_inst_791_: *mut LeanObject,
    mut v_toBind_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___f_794_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_794_, 0, v_a_793_);
    lean_closure_set(v___f_794_, 1, v_toPure_789_);
    v___x_795_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_795_, 0, lean_box(0));
    lean_closure_set(v___x_795_, 1, lean_box(0));
    lean_closure_set(v___x_795_, 2, v_ref_790_);
    v___x_796_ = lean_apply_2(v_inst_791_, lean_box(0), v___x_795_);
    v___x_797_ = lean_apply_4(
        v_toBind_792_,
        lean_box(0),
        lean_box(0),
        v___x_796_,
        v___f_794_,
    );
    return v___x_797_;
}
pub unsafe fn l_StateRefT_x27_run___redArg___lam__2(
    mut v_toPure_798_: *mut LeanObject,
    mut v_inst_799_: *mut LeanObject,
    mut v_toBind_800_: *mut LeanObject,
    mut v_x_801_: *mut LeanObject,
    mut v_ref_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_800_);
    lean_inc(v_ref_802_);
    v___f_803_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_803_, 0, v_toPure_798_);
    lean_closure_set(v___f_803_, 1, v_ref_802_);
    lean_closure_set(v___f_803_, 2, v_inst_799_);
    lean_closure_set(v___f_803_, 3, v_toBind_800_);
    v___x_804_ = lean_apply_1(v_x_801_, v_ref_802_);
    v___x_805_ = lean_apply_4(
        v_toBind_800_,
        lean_box(0),
        lean_box(0),
        v___x_804_,
        v___f_803_,
    );
    return v___x_805_;
}
pub unsafe fn l_StateRefT_x27_run___redArg(
    mut v_inst_806_: *mut LeanObject,
    mut v_inst_807_: *mut LeanObject,
    mut v_x_808_: *mut LeanObject,
    mut v_s_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_810_ = lean_ctor_get(v_inst_806_, 0);
    lean_inc_ref(v_toApplicative_810_);
    v_toBind_811_ = lean_ctor_get(v_inst_806_, 1);
    lean_inc_n(v_toBind_811_, 2);
    lean_dec_ref(v_inst_806_);
    v_toPure_812_ = lean_ctor_get(v_toApplicative_810_, 1);
    lean_inc(v_toPure_812_);
    lean_dec_ref(v_toApplicative_810_);
    v___x_813_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_813_, 0, lean_box(0));
    lean_closure_set(v___x_813_, 1, lean_box(0));
    lean_closure_set(v___x_813_, 2, v_s_809_);
    lean_inc(v_inst_807_);
    v___x_814_ = lean_apply_2(v_inst_807_, lean_box(0), v___x_813_);
    v___f_815_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_815_, 0, v_toPure_812_);
    lean_closure_set(v___f_815_, 1, v_inst_807_);
    lean_closure_set(v___f_815_, 2, v_toBind_811_);
    lean_closure_set(v___f_815_, 3, v_x_808_);
    v___x_816_ = lean_apply_4(
        v_toBind_811_,
        lean_box(0),
        lean_box(0),
        v___x_814_,
        v___f_815_,
    );
    return v___x_816_;
}
pub unsafe fn l_StateRefT_x27_run(
    mut v_00_u03c9_817_: *mut LeanObject,
    mut v_00_u03c3_818_: *mut LeanObject,
    mut v_m_819_: *mut LeanObject,
    mut v_inst_820_: *mut LeanObject,
    mut v_inst_821_: *mut LeanObject,
    mut v_00_u03b1_822_: *mut LeanObject,
    mut v_x_823_: *mut LeanObject,
    mut v_s_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_825_ = lean_ctor_get(v_inst_820_, 0);
    lean_inc_ref(v_toApplicative_825_);
    v_toBind_826_ = lean_ctor_get(v_inst_820_, 1);
    lean_inc_n(v_toBind_826_, 2);
    lean_dec_ref(v_inst_820_);
    v_toPure_827_ = lean_ctor_get(v_toApplicative_825_, 1);
    lean_inc(v_toPure_827_);
    lean_dec_ref(v_toApplicative_825_);
    v___x_828_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_828_, 0, lean_box(0));
    lean_closure_set(v___x_828_, 1, lean_box(0));
    lean_closure_set(v___x_828_, 2, v_s_824_);
    lean_inc(v_inst_821_);
    v___x_829_ = lean_apply_2(v_inst_821_, lean_box(0), v___x_828_);
    v___f_830_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_830_, 0, v_toPure_827_);
    lean_closure_set(v___f_830_, 1, v_inst_821_);
    lean_closure_set(v___f_830_, 2, v_toBind_826_);
    lean_closure_set(v___f_830_, 3, v_x_823_);
    v___x_831_ = lean_apply_4(
        v_toBind_826_,
        lean_box(0),
        lean_box(0),
        v___x_829_,
        v___f_830_,
    );
    return v___x_831_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg___lam__0(
    mut v_toPure_832_: *mut LeanObject,
    mut v_____x_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v_fst_834_ = lean_ctor_get(v_____x_833_, 0);
    lean_inc(v_fst_834_);
    lean_dec_ref(v_____x_833_);
    v___x_835_ = lean_apply_2(v_toPure_832_, lean_box(0), v_fst_834_);
    return v___x_835_;
}
pub unsafe fn l_StateRefT_x27_run_x27___redArg(
    mut v_inst_836_: *mut LeanObject,
    mut v_inst_837_: *mut LeanObject,
    mut v_x_838_: *mut LeanObject,
    mut v_s_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_840_ = lean_ctor_get(v_inst_836_, 0);
    lean_inc_ref(v_toApplicative_840_);
    v_toBind_841_ = lean_ctor_get(v_inst_836_, 1);
    lean_inc_n(v_toBind_841_, 3);
    lean_dec_ref(v_inst_836_);
    v_toPure_842_ = lean_ctor_get(v_toApplicative_840_, 1);
    lean_inc_n(v_toPure_842_, 2);
    lean_dec_ref(v_toApplicative_840_);
    v___x_843_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_843_, 0, lean_box(0));
    lean_closure_set(v___x_843_, 1, lean_box(0));
    lean_closure_set(v___x_843_, 2, v_s_839_);
    lean_inc(v_inst_837_);
    v___x_844_ = lean_apply_2(v_inst_837_, lean_box(0), v___x_843_);
    v___f_845_ = lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_845_, 0, v_toPure_842_);
    v___f_846_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_846_, 0, v_toPure_842_);
    lean_closure_set(v___f_846_, 1, v_inst_837_);
    lean_closure_set(v___f_846_, 2, v_toBind_841_);
    lean_closure_set(v___f_846_, 3, v_x_838_);
    v___x_847_ = lean_apply_4(
        v_toBind_841_,
        lean_box(0),
        lean_box(0),
        v___x_844_,
        v___f_846_,
    );
    v___x_848_ = lean_apply_4(
        v_toBind_841_,
        lean_box(0),
        lean_box(0),
        v___x_847_,
        v___f_845_,
    );
    return v___x_848_;
}
pub unsafe fn l_StateRefT_x27_run_x27(
    mut v_00_u03c9_849_: *mut LeanObject,
    mut v_00_u03c3_850_: *mut LeanObject,
    mut v_m_851_: *mut LeanObject,
    mut v_inst_852_: *mut LeanObject,
    mut v_inst_853_: *mut LeanObject,
    mut v_00_u03b1_854_: *mut LeanObject,
    mut v_x_855_: *mut LeanObject,
    mut v_s_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_857_ = lean_ctor_get(v_inst_852_, 0);
    lean_inc_ref(v_toApplicative_857_);
    v_toBind_858_ = lean_ctor_get(v_inst_852_, 1);
    lean_inc_n(v_toBind_858_, 3);
    lean_dec_ref(v_inst_852_);
    v_toPure_859_ = lean_ctor_get(v_toApplicative_857_, 1);
    lean_inc_n(v_toPure_859_, 2);
    lean_dec_ref(v_toApplicative_857_);
    v___x_860_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_860_, 0, lean_box(0));
    lean_closure_set(v___x_860_, 1, lean_box(0));
    lean_closure_set(v___x_860_, 2, v_s_856_);
    lean_inc(v_inst_853_);
    v___x_861_ = lean_apply_2(v_inst_853_, lean_box(0), v___x_860_);
    v___f_862_ = lean_alloc_closure(
        l_StateRefT_x27_run_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_862_, 0, v_toPure_859_);
    v___f_863_ = lean_alloc_closure(
        l_StateRefT_x27_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_863_, 0, v_toPure_859_);
    lean_closure_set(v___f_863_, 1, v_inst_853_);
    lean_closure_set(v___f_863_, 2, v_toBind_858_);
    lean_closure_set(v___f_863_, 3, v_x_855_);
    v___x_864_ = lean_apply_4(
        v_toBind_858_,
        lean_box(0),
        lean_box(0),
        v___x_861_,
        v___f_863_,
    );
    v___x_865_ = lean_apply_4(
        v_toBind_858_,
        lean_box(0),
        lean_box(0),
        v___x_864_,
        v___f_862_,
    );
    return v___x_865_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg(mut v_x_866_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_866_);
    return v_x_866_;
}
pub unsafe fn l_StateRefT_x27_lift___redArg___boxed(
    mut v_x_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_868_: *mut LeanObject = core::ptr::null_mut();
    v_res_868_ = l_StateRefT_x27_lift___redArg(v_x_867_);
    lean_dec(v_x_867_);
    return v_res_868_;
}
pub unsafe fn l_StateRefT_x27_lift(
    mut v_00_u03c9_869_: *mut LeanObject,
    mut v_00_u03c3_870_: *mut LeanObject,
    mut v_m_871_: *mut LeanObject,
    mut v_00_u03b1_872_: *mut LeanObject,
    mut v_x_873_: *mut LeanObject,
    mut v_x_874_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_873_);
    return v_x_873_;
}
pub unsafe fn l_StateRefT_x27_lift___boxed(
    mut v_00_u03c9_875_: *mut LeanObject,
    mut v_00_u03c3_876_: *mut LeanObject,
    mut v_m_877_: *mut LeanObject,
    mut v_00_u03b1_878_: *mut LeanObject,
    mut v_x_879_: *mut LeanObject,
    mut v_x_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_881_: *mut LeanObject = core::ptr::null_mut();
    v_res_881_ = l_StateRefT_x27_lift(
        v_00_u03c9_875_,
        v_00_u03c3_876_,
        v_m_877_,
        v_00_u03b1_878_,
        v_x_879_,
        v_x_880_,
    );
    lean_dec(v_x_880_);
    lean_dec(v_x_879_);
    return v_res_881_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg(
    mut v_inst_882_: *mut LeanObject,
    mut v_f_883_: *mut LeanObject,
    mut v_x_884_: *mut LeanObject,
    mut v_r_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_886_ = lean_ctor_get(v_inst_882_, 0);
    lean_inc_ref(v_toApplicative_886_);
    lean_dec_ref(v_inst_882_);
    v_toFunctor_887_ = lean_ctor_get(v_toApplicative_886_, 0);
    lean_inc_ref(v_toFunctor_887_);
    lean_dec_ref(v_toApplicative_886_);
    v_map_888_ = lean_ctor_get(v_toFunctor_887_, 0);
    lean_inc(v_map_888_);
    lean_dec_ref(v_toFunctor_887_);
    lean_inc(v_r_885_);
    v___x_889_ = lean_apply_1(v_x_884_, v_r_885_);
    v___x_890_ = lean_apply_4(v_map_888_, lean_box(0), lean_box(0), v_f_883_, v___x_889_);
    return v___x_890_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___redArg___boxed(
    mut v_inst_891_: *mut LeanObject,
    mut v_f_892_: *mut LeanObject,
    mut v_x_893_: *mut LeanObject,
    mut v_r_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ =
        l_StateRefT_x27_instMonad___aux__1___redArg(v_inst_891_, v_f_892_, v_x_893_, v_r_894_);
    lean_dec(v_r_894_);
    return v_res_895_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1(
    mut v_00_u03c9_896_: *mut LeanObject,
    mut v_00_u03c3_897_: *mut LeanObject,
    mut v_m_898_: *mut LeanObject,
    mut v_inst_899_: *mut LeanObject,
    mut v_00_u03b1_900_: *mut LeanObject,
    mut v_00_u03b2_901_: *mut LeanObject,
    mut v_f_902_: *mut LeanObject,
    mut v_x_903_: *mut LeanObject,
    mut v_r_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_905_ = lean_ctor_get(v_inst_899_, 0);
    lean_inc_ref(v_toApplicative_905_);
    lean_dec_ref(v_inst_899_);
    v_toFunctor_906_ = lean_ctor_get(v_toApplicative_905_, 0);
    lean_inc_ref(v_toFunctor_906_);
    lean_dec_ref(v_toApplicative_905_);
    v_map_907_ = lean_ctor_get(v_toFunctor_906_, 0);
    lean_inc(v_map_907_);
    lean_dec_ref(v_toFunctor_906_);
    lean_inc(v_r_904_);
    v___x_908_ = lean_apply_1(v_x_903_, v_r_904_);
    v___x_909_ = lean_apply_4(v_map_907_, lean_box(0), lean_box(0), v_f_902_, v___x_908_);
    return v___x_909_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__1___boxed(
    mut v_00_u03c9_910_: *mut LeanObject,
    mut v_00_u03c3_911_: *mut LeanObject,
    mut v_m_912_: *mut LeanObject,
    mut v_inst_913_: *mut LeanObject,
    mut v_00_u03b1_914_: *mut LeanObject,
    mut v_00_u03b2_915_: *mut LeanObject,
    mut v_f_916_: *mut LeanObject,
    mut v_x_917_: *mut LeanObject,
    mut v_r_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_918_);
    return v_res_919_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg(
    mut v_inst_920_: *mut LeanObject,
    mut v_a_921_: *mut LeanObject,
    mut v_x_922_: *mut LeanObject,
    mut v_r_923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_924_ = lean_ctor_get(v_inst_920_, 0);
    lean_inc_ref(v_toApplicative_924_);
    lean_dec_ref(v_inst_920_);
    v_toFunctor_925_ = lean_ctor_get(v_toApplicative_924_, 0);
    lean_inc_ref(v_toFunctor_925_);
    lean_dec_ref(v_toApplicative_924_);
    v_mapConst_926_ = lean_ctor_get(v_toFunctor_925_, 1);
    lean_inc(v_mapConst_926_);
    lean_dec_ref(v_toFunctor_925_);
    lean_inc(v_r_923_);
    v___x_927_ = lean_apply_1(v_x_922_, v_r_923_);
    v___x_928_ = lean_apply_4(
        v_mapConst_926_,
        lean_box(0),
        lean_box(0),
        v_a_921_,
        v___x_927_,
    );
    return v___x_928_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___redArg___boxed(
    mut v_inst_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_x_931_: *mut LeanObject,
    mut v_r_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_933_: *mut LeanObject = core::ptr::null_mut();
    v_res_933_ =
        l_StateRefT_x27_instMonad___aux__3___redArg(v_inst_929_, v_a_930_, v_x_931_, v_r_932_);
    lean_dec(v_r_932_);
    return v_res_933_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3(
    mut v_00_u03c9_934_: *mut LeanObject,
    mut v_00_u03c3_935_: *mut LeanObject,
    mut v_m_936_: *mut LeanObject,
    mut v_inst_937_: *mut LeanObject,
    mut v_00_u03b1_938_: *mut LeanObject,
    mut v_00_u03b2_939_: *mut LeanObject,
    mut v_a_940_: *mut LeanObject,
    mut v_x_941_: *mut LeanObject,
    mut v_r_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_943_ = lean_ctor_get(v_inst_937_, 0);
    lean_inc_ref(v_toApplicative_943_);
    lean_dec_ref(v_inst_937_);
    v_toFunctor_944_ = lean_ctor_get(v_toApplicative_943_, 0);
    lean_inc_ref(v_toFunctor_944_);
    lean_dec_ref(v_toApplicative_943_);
    v_mapConst_945_ = lean_ctor_get(v_toFunctor_944_, 1);
    lean_inc(v_mapConst_945_);
    lean_dec_ref(v_toFunctor_944_);
    lean_inc(v_r_942_);
    v___x_946_ = lean_apply_1(v_x_941_, v_r_942_);
    v___x_947_ = lean_apply_4(
        v_mapConst_945_,
        lean_box(0),
        lean_box(0),
        v_a_940_,
        v___x_946_,
    );
    return v___x_947_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__3___boxed(
    mut v_00_u03c9_948_: *mut LeanObject,
    mut v_00_u03c3_949_: *mut LeanObject,
    mut v_m_950_: *mut LeanObject,
    mut v_inst_951_: *mut LeanObject,
    mut v_00_u03b1_952_: *mut LeanObject,
    mut v_00_u03b2_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_x_955_: *mut LeanObject,
    mut v_r_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_957_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_956_);
    return v_res_957_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___redArg(
    mut v_inst_958_: *mut LeanObject,
    mut v_a_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_960_ = lean_ctor_get(v_inst_958_, 0);
    lean_inc_ref(v_toApplicative_960_);
    lean_dec_ref(v_inst_958_);
    v_toPure_961_ = lean_ctor_get(v_toApplicative_960_, 1);
    lean_inc(v_toPure_961_);
    lean_dec_ref(v_toApplicative_960_);
    v___x_962_ = lean_apply_2(v_toPure_961_, lean_box(0), v_a_959_);
    return v___x_962_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5(
    mut v_00_u03c9_963_: *mut LeanObject,
    mut v_00_u03c3_964_: *mut LeanObject,
    mut v_m_965_: *mut LeanObject,
    mut v_inst_966_: *mut LeanObject,
    mut v_00_u03b1_967_: *mut LeanObject,
    mut v_a_968_: *mut LeanObject,
    mut v_a_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_970_ = lean_ctor_get(v_inst_966_, 0);
    lean_inc_ref(v_toApplicative_970_);
    lean_dec_ref(v_inst_966_);
    v_toPure_971_ = lean_ctor_get(v_toApplicative_970_, 1);
    lean_inc(v_toPure_971_);
    lean_dec_ref(v_toApplicative_970_);
    v___x_972_ = lean_apply_2(v_toPure_971_, lean_box(0), v_a_968_);
    return v___x_972_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__5___boxed(
    mut v_00_u03c9_973_: *mut LeanObject,
    mut v_00_u03c3_974_: *mut LeanObject,
    mut v_m_975_: *mut LeanObject,
    mut v_inst_976_: *mut LeanObject,
    mut v_00_u03b1_977_: *mut LeanObject,
    mut v_a_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_980_: *mut LeanObject = core::ptr::null_mut();
    v_res_980_ = l_StateRefT_x27_instMonad___aux__5(
        v_00_u03c9_973_,
        v_00_u03c3_974_,
        v_m_975_,
        v_inst_976_,
        v_00_u03b1_977_,
        v_a_978_,
        v_a_979_,
    );
    lean_dec(v_a_979_);
    return v_res_980_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(
    mut v_x_981_: *mut LeanObject,
    mut v_r_982_: *mut LeanObject,
    mut v_x_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ = lean_box(0);
    lean_inc(v_r_982_);
    v___x_985_ = lean_apply_2(v_x_981_, v___x_984_, v_r_982_);
    return v___x_985_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_x_986_: *mut LeanObject,
    mut v_r_987_: *mut LeanObject,
    mut v_x_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_989_: *mut LeanObject = core::ptr::null_mut();
    v_res_989_ = l_StateRefT_x27_instMonad___aux__7___redArg___lam__0(v_x_986_, v_r_987_, v_x_988_);
    lean_dec(v_r_987_);
    return v_res_989_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg(
    mut v_inst_990_: *mut LeanObject,
    mut v_f_991_: *mut LeanObject,
    mut v_x_992_: *mut LeanObject,
    mut v_r_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_994_ = lean_ctor_get(v_inst_990_, 0);
    lean_inc_ref(v_toApplicative_994_);
    lean_dec_ref(v_inst_990_);
    v_toSeq_995_ = lean_ctor_get(v_toApplicative_994_, 2);
    lean_inc(v_toSeq_995_);
    lean_dec_ref(v_toApplicative_994_);
    lean_inc_n(v_r_993_, 2);
    v___f_996_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_996_, 0, v_x_992_);
    lean_closure_set(v___f_996_, 1, v_r_993_);
    v___x_997_ = lean_apply_1(v_f_991_, v_r_993_);
    v___x_998_ = lean_apply_4(
        v_toSeq_995_,
        lean_box(0),
        lean_box(0),
        v___x_997_,
        v___f_996_,
    );
    return v___x_998_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___redArg___boxed(
    mut v_inst_999_: *mut LeanObject,
    mut v_f_1000_: *mut LeanObject,
    mut v_x_1001_: *mut LeanObject,
    mut v_r_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_res_1003_ =
        l_StateRefT_x27_instMonad___aux__7___redArg(v_inst_999_, v_f_1000_, v_x_1001_, v_r_1002_);
    lean_dec(v_r_1002_);
    return v_res_1003_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7(
    mut v_00_u03c9_1004_: *mut LeanObject,
    mut v_00_u03c3_1005_: *mut LeanObject,
    mut v_m_1006_: *mut LeanObject,
    mut v_inst_1007_: *mut LeanObject,
    mut v_00_u03b1_1008_: *mut LeanObject,
    mut v_00_u03b2_1009_: *mut LeanObject,
    mut v_f_1010_: *mut LeanObject,
    mut v_x_1011_: *mut LeanObject,
    mut v_r_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1013_ = lean_ctor_get(v_inst_1007_, 0);
    lean_inc_ref(v_toApplicative_1013_);
    lean_dec_ref(v_inst_1007_);
    v_toSeq_1014_ = lean_ctor_get(v_toApplicative_1013_, 2);
    lean_inc(v_toSeq_1014_);
    lean_dec_ref(v_toApplicative_1013_);
    lean_inc_n(v_r_1012_, 2);
    v___f_1015_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1015_, 0, v_x_1011_);
    lean_closure_set(v___f_1015_, 1, v_r_1012_);
    v___x_1016_ = lean_apply_1(v_f_1010_, v_r_1012_);
    v___x_1017_ = lean_apply_4(
        v_toSeq_1014_,
        lean_box(0),
        lean_box(0),
        v___x_1016_,
        v___f_1015_,
    );
    return v___x_1017_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__7___boxed(
    mut v_00_u03c9_1018_: *mut LeanObject,
    mut v_00_u03c3_1019_: *mut LeanObject,
    mut v_m_1020_: *mut LeanObject,
    mut v_inst_1021_: *mut LeanObject,
    mut v_00_u03b1_1022_: *mut LeanObject,
    mut v_00_u03b2_1023_: *mut LeanObject,
    mut v_f_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
    mut v_r_1026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1027_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_1026_);
    return v_res_1027_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(
    mut v_b_1028_: *mut LeanObject,
    mut v_r_1029_: *mut LeanObject,
    mut v_x_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1031_ = lean_box(0);
    lean_inc(v_r_1029_);
    v___x_1032_ = lean_apply_2(v_b_1028_, v___x_1031_, v_r_1029_);
    return v___x_1032_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed(
    mut v_b_1033_: *mut LeanObject,
    mut v_r_1034_: *mut LeanObject,
    mut v_x_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ =
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0(v_b_1033_, v_r_1034_, v_x_1035_);
    lean_dec(v_r_1034_);
    return v_res_1036_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg(
    mut v_inst_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_b_1039_: *mut LeanObject,
    mut v_r_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1041_ = lean_ctor_get(v_inst_1037_, 0);
    lean_inc_ref(v_toApplicative_1041_);
    lean_dec_ref(v_inst_1037_);
    v_toSeqLeft_1042_ = lean_ctor_get(v_toApplicative_1041_, 3);
    lean_inc(v_toSeqLeft_1042_);
    lean_dec_ref(v_toApplicative_1041_);
    lean_inc_n(v_r_1040_, 2);
    v___f_1043_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1043_, 0, v_b_1039_);
    lean_closure_set(v___f_1043_, 1, v_r_1040_);
    v___x_1044_ = lean_apply_1(v_a_1038_, v_r_1040_);
    v___x_1045_ = lean_apply_4(
        v_toSeqLeft_1042_,
        lean_box(0),
        lean_box(0),
        v___x_1044_,
        v___f_1043_,
    );
    return v___x_1045_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___redArg___boxed(
    mut v_inst_1046_: *mut LeanObject,
    mut v_a_1047_: *mut LeanObject,
    mut v_b_1048_: *mut LeanObject,
    mut v_r_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ =
        l_StateRefT_x27_instMonad___aux__9___redArg(v_inst_1046_, v_a_1047_, v_b_1048_, v_r_1049_);
    lean_dec(v_r_1049_);
    return v_res_1050_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9(
    mut v_00_u03c9_1051_: *mut LeanObject,
    mut v_00_u03c3_1052_: *mut LeanObject,
    mut v_m_1053_: *mut LeanObject,
    mut v_inst_1054_: *mut LeanObject,
    mut v_00_u03b1_1055_: *mut LeanObject,
    mut v_00_u03b2_1056_: *mut LeanObject,
    mut v_a_1057_: *mut LeanObject,
    mut v_b_1058_: *mut LeanObject,
    mut v_r_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1060_ = lean_ctor_get(v_inst_1054_, 0);
    lean_inc_ref(v_toApplicative_1060_);
    lean_dec_ref(v_inst_1054_);
    v_toSeqLeft_1061_ = lean_ctor_get(v_toApplicative_1060_, 3);
    lean_inc(v_toSeqLeft_1061_);
    lean_dec_ref(v_toApplicative_1060_);
    lean_inc_n(v_r_1059_, 2);
    v___f_1062_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1062_, 0, v_b_1058_);
    lean_closure_set(v___f_1062_, 1, v_r_1059_);
    v___x_1063_ = lean_apply_1(v_a_1057_, v_r_1059_);
    v___x_1064_ = lean_apply_4(
        v_toSeqLeft_1061_,
        lean_box(0),
        lean_box(0),
        v___x_1063_,
        v___f_1062_,
    );
    return v___x_1064_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__9___boxed(
    mut v_00_u03c9_1065_: *mut LeanObject,
    mut v_00_u03c3_1066_: *mut LeanObject,
    mut v_m_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_00_u03b1_1069_: *mut LeanObject,
    mut v_00_u03b2_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_b_1072_: *mut LeanObject,
    mut v_r_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_1073_);
    return v_res_1074_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg(
    mut v_inst_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
    mut v_b_1077_: *mut LeanObject,
    mut v_r_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1079_ = lean_ctor_get(v_inst_1075_, 0);
    lean_inc_ref(v_toApplicative_1079_);
    lean_dec_ref(v_inst_1075_);
    v_toSeqRight_1080_ = lean_ctor_get(v_toApplicative_1079_, 4);
    lean_inc(v_toSeqRight_1080_);
    lean_dec_ref(v_toApplicative_1079_);
    lean_inc_n(v_r_1078_, 2);
    v___f_1081_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1081_, 0, v_b_1077_);
    lean_closure_set(v___f_1081_, 1, v_r_1078_);
    v___x_1082_ = lean_apply_1(v_a_1076_, v_r_1078_);
    v___x_1083_ = lean_apply_4(
        v_toSeqRight_1080_,
        lean_box(0),
        lean_box(0),
        v___x_1082_,
        v___f_1081_,
    );
    return v___x_1083_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___redArg___boxed(
    mut v_inst_1084_: *mut LeanObject,
    mut v_a_1085_: *mut LeanObject,
    mut v_b_1086_: *mut LeanObject,
    mut v_r_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1088_: *mut LeanObject = core::ptr::null_mut();
    v_res_1088_ =
        l_StateRefT_x27_instMonad___aux__11___redArg(v_inst_1084_, v_a_1085_, v_b_1086_, v_r_1087_);
    lean_dec(v_r_1087_);
    return v_res_1088_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11(
    mut v_00_u03c9_1089_: *mut LeanObject,
    mut v_00_u03c3_1090_: *mut LeanObject,
    mut v_m_1091_: *mut LeanObject,
    mut v_inst_1092_: *mut LeanObject,
    mut v_00_u03b1_1093_: *mut LeanObject,
    mut v_00_u03b2_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
    mut v_b_1096_: *mut LeanObject,
    mut v_r_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1098_ = lean_ctor_get(v_inst_1092_, 0);
    lean_inc_ref(v_toApplicative_1098_);
    lean_dec_ref(v_inst_1092_);
    v_toSeqRight_1099_ = lean_ctor_get(v_toApplicative_1098_, 4);
    lean_inc(v_toSeqRight_1099_);
    lean_dec_ref(v_toApplicative_1098_);
    lean_inc_n(v_r_1097_, 2);
    v___f_1100_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1100_, 0, v_b_1096_);
    lean_closure_set(v___f_1100_, 1, v_r_1097_);
    v___x_1101_ = lean_apply_1(v_a_1095_, v_r_1097_);
    v___x_1102_ = lean_apply_4(
        v_toSeqRight_1099_,
        lean_box(0),
        lean_box(0),
        v___x_1101_,
        v___f_1100_,
    );
    return v___x_1102_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__11___boxed(
    mut v_00_u03c9_1103_: *mut LeanObject,
    mut v_00_u03c3_1104_: *mut LeanObject,
    mut v_m_1105_: *mut LeanObject,
    mut v_inst_1106_: *mut LeanObject,
    mut v_00_u03b1_1107_: *mut LeanObject,
    mut v_00_u03b2_1108_: *mut LeanObject,
    mut v_a_1109_: *mut LeanObject,
    mut v_b_1110_: *mut LeanObject,
    mut v_r_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1112_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_1111_);
    return v_res_1112_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(
    mut v_f_1113_: *mut LeanObject,
    mut v_a_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1114_);
    v___x_1116_ = lean_apply_2(v_f_1113_, v_a_1115_, v_a_1114_);
    return v___x_1116_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_f_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1120_: *mut LeanObject = core::ptr::null_mut();
    v_res_1120_ =
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0(v_f_1117_, v_a_1118_, v_a_1119_);
    lean_dec(v_a_1118_);
    return v_res_1120_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg(
    mut v_inst_1121_: *mut LeanObject,
    mut v_x_1122_: *mut LeanObject,
    mut v_f_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1125_ = lean_ctor_get(v_inst_1121_, 1);
    lean_inc(v_toBind_1125_);
    lean_dec_ref(v_inst_1121_);
    lean_inc_n(v_a_1124_, 2);
    v___f_1126_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1126_, 0, v_f_1123_);
    lean_closure_set(v___f_1126_, 1, v_a_1124_);
    v___x_1127_ = lean_apply_1(v_x_1122_, v_a_1124_);
    v___x_1128_ = lean_apply_4(
        v_toBind_1125_,
        lean_box(0),
        lean_box(0),
        v___x_1127_,
        v___f_1126_,
    );
    return v___x_1128_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___redArg___boxed(
    mut v_inst_1129_: *mut LeanObject,
    mut v_x_1130_: *mut LeanObject,
    mut v_f_1131_: *mut LeanObject,
    mut v_a_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1133_: *mut LeanObject = core::ptr::null_mut();
    v_res_1133_ =
        l_StateRefT_x27_instMonad___aux__13___redArg(v_inst_1129_, v_x_1130_, v_f_1131_, v_a_1132_);
    lean_dec(v_a_1132_);
    return v_res_1133_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13(
    mut v_00_u03c9_1134_: *mut LeanObject,
    mut v_00_u03c3_1135_: *mut LeanObject,
    mut v_m_1136_: *mut LeanObject,
    mut v_inst_1137_: *mut LeanObject,
    mut v_00_u03b1_1138_: *mut LeanObject,
    mut v_00_u03b2_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
    mut v_f_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1143_ = lean_ctor_get(v_inst_1137_, 1);
    lean_inc(v_toBind_1143_);
    lean_dec_ref(v_inst_1137_);
    lean_inc_n(v_a_1142_, 2);
    v___f_1144_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1144_, 0, v_f_1141_);
    lean_closure_set(v___f_1144_, 1, v_a_1142_);
    v___x_1145_ = lean_apply_1(v_x_1140_, v_a_1142_);
    v___x_1146_ = lean_apply_4(
        v_toBind_1143_,
        lean_box(0),
        lean_box(0),
        v___x_1145_,
        v___f_1144_,
    );
    return v___x_1146_;
}
pub unsafe fn l_StateRefT_x27_instMonad___aux__13___boxed(
    mut v_00_u03c9_1147_: *mut LeanObject,
    mut v_00_u03c3_1148_: *mut LeanObject,
    mut v_m_1149_: *mut LeanObject,
    mut v_inst_1150_: *mut LeanObject,
    mut v_00_u03b1_1151_: *mut LeanObject,
    mut v_00_u03b2_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
    mut v_f_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1156_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1155_);
    return v_res_1156_;
}
pub unsafe fn l_StateRefT_x27_instMonad___redArg(
    mut v_inst_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1157_, 6);
    v___x_1158_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1158_, 0, lean_box(0));
    lean_closure_set(v___x_1158_, 1, lean_box(0));
    lean_closure_set(v___x_1158_, 2, lean_box(0));
    lean_closure_set(v___x_1158_, 3, v_inst_1157_);
    v___x_1159_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1159_, 0, lean_box(0));
    lean_closure_set(v___x_1159_, 1, lean_box(0));
    lean_closure_set(v___x_1159_, 2, lean_box(0));
    lean_closure_set(v___x_1159_, 3, v_inst_1157_);
    v___x_1160_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    v___x_1161_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___x_1161_, 0, lean_box(0));
    lean_closure_set(v___x_1161_, 1, lean_box(0));
    lean_closure_set(v___x_1161_, 2, lean_box(0));
    lean_closure_set(v___x_1161_, 3, v_inst_1157_);
    v___x_1162_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1162_, 0, lean_box(0));
    lean_closure_set(v___x_1162_, 1, lean_box(0));
    lean_closure_set(v___x_1162_, 2, lean_box(0));
    lean_closure_set(v___x_1162_, 3, v_inst_1157_);
    v___x_1163_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1163_, 0, lean_box(0));
    lean_closure_set(v___x_1163_, 1, lean_box(0));
    lean_closure_set(v___x_1163_, 2, lean_box(0));
    lean_closure_set(v___x_1163_, 3, v_inst_1157_);
    v___x_1164_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1164_, 0, lean_box(0));
    lean_closure_set(v___x_1164_, 1, lean_box(0));
    lean_closure_set(v___x_1164_, 2, lean_box(0));
    lean_closure_set(v___x_1164_, 3, v_inst_1157_);
    v___x_1165_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1165_, 0, v___x_1160_);
    lean_ctor_set(v___x_1165_, 1, v___x_1161_);
    lean_ctor_set(v___x_1165_, 2, v___x_1162_);
    lean_ctor_set(v___x_1165_, 3, v___x_1163_);
    lean_ctor_set(v___x_1165_, 4, v___x_1164_);
    v___x_1166_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1166_, 0, lean_box(0));
    lean_closure_set(v___x_1166_, 1, lean_box(0));
    lean_closure_set(v___x_1166_, 2, lean_box(0));
    lean_closure_set(v___x_1166_, 3, v_inst_1157_);
    v___x_1167_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1167_, 0, v___x_1165_);
    lean_ctor_set(v___x_1167_, 1, v___x_1166_);
    return v___x_1167_;
}
pub unsafe fn l_StateRefT_x27_instMonad(
    mut v_00_u03c9_1168_: *mut LeanObject,
    mut v_00_u03c3_1169_: *mut LeanObject,
    mut v_m_1170_: *mut LeanObject,
    mut v_inst_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_StateRefT_x27_instMonad___redArg(v_inst_1171_);
    return v___x_1172_;
}
pub unsafe fn l_StateRefT_x27_instMonadLift(
    mut v_00_u03c9_1174_: *mut LeanObject,
    mut v_00_u03c3_1175_: *mut LeanObject,
    mut v_m_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_StateRefT_x27_instMonadLift___closed__0;
    return v___x_1177_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg(
    mut v_f_1178_: *mut LeanObject,
    mut v_x_1179_: *mut LeanObject,
    mut v_ctx_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1180_);
    v___x_1181_ = lean_apply_1(v_x_1179_, v_ctx_1180_);
    v___x_1182_ = lean_apply_2(v_f_1178_, lean_box(0), v___x_1181_);
    return v___x_1182_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___redArg___boxed(
    mut v_f_1183_: *mut LeanObject,
    mut v_x_1184_: *mut LeanObject,
    mut v_ctx_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1186_: *mut LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_StateRefT_x27_instMonadFunctor___aux__1___redArg(v_f_1183_, v_x_1184_, v_ctx_1185_);
    lean_dec(v_ctx_1185_);
    return v_res_1186_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1(
    mut v_00_u03c9_1187_: *mut LeanObject,
    mut v_00_u03c3_1188_: *mut LeanObject,
    mut v_m_1189_: *mut LeanObject,
    mut v_00_u03b1_1190_: *mut LeanObject,
    mut v_f_1191_: *mut LeanObject,
    mut v_x_1192_: *mut LeanObject,
    mut v_ctx_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1193_);
    v___x_1194_ = lean_apply_1(v_x_1192_, v_ctx_1193_);
    v___x_1195_ = lean_apply_2(v_f_1191_, lean_box(0), v___x_1194_);
    return v___x_1195_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor___aux__1___boxed(
    mut v_00_u03c9_1196_: *mut LeanObject,
    mut v_00_u03c3_1197_: *mut LeanObject,
    mut v_m_1198_: *mut LeanObject,
    mut v_00_u03b1_1199_: *mut LeanObject,
    mut v_f_1200_: *mut LeanObject,
    mut v_x_1201_: *mut LeanObject,
    mut v_ctx_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1203_: *mut LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_StateRefT_x27_instMonadFunctor___aux__1(
        v_00_u03c9_1196_,
        v_00_u03c3_1197_,
        v_m_1198_,
        v_00_u03b1_1199_,
        v_f_1200_,
        v_x_1201_,
        v_ctx_1202_,
    );
    lean_dec(v_ctx_1202_);
    return v_res_1203_;
}
pub unsafe fn l_StateRefT_x27_instMonadFunctor(
    mut v_00_u03c9_1205_: *mut LeanObject,
    mut v_00_u03c3_1206_: *mut LeanObject,
    mut v_m_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_StateRefT_x27_instMonadFunctor___closed__0;
    return v___x_1208_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___redArg(
    mut v_inst_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v_failure_1210_ = lean_ctor_get(v_inst_1209_, 1);
    lean_inc(v_failure_1210_);
    lean_dec_ref(v_inst_1209_);
    v___x_1211_ = lean_apply_1(v_failure_1210_, lean_box(0));
    return v___x_1211_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1(
    mut v_00_u03c9_1212_: *mut LeanObject,
    mut v_00_u03c3_1213_: *mut LeanObject,
    mut v_m_1214_: *mut LeanObject,
    mut v_inst_1215_: *mut LeanObject,
    mut v_00_u03b1_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    v_failure_1218_ = lean_ctor_get(v_inst_1215_, 1);
    lean_inc(v_failure_1218_);
    lean_dec_ref(v_inst_1215_);
    v___x_1219_ = lean_apply_1(v_failure_1218_, lean_box(0));
    return v___x_1219_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed(
    mut v_00_u03c9_1220_: *mut LeanObject,
    mut v_00_u03c3_1221_: *mut LeanObject,
    mut v_m_1222_: *mut LeanObject,
    mut v_inst_1223_: *mut LeanObject,
    mut v_00_u03b1_1224_: *mut LeanObject,
    mut v_a_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1226_: *mut LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_StateRefT_x27_instAlternativeOfMonad___aux__1(
        v_00_u03c9_1220_,
        v_00_u03c3_1221_,
        v_m_1222_,
        v_inst_1223_,
        v_00_u03b1_1224_,
        v_a_1225_,
    );
    lean_dec(v_a_1225_);
    return v_res_1226_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
    mut v_x_u2082_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    v___x_1230_ = lean_box(0);
    lean_inc(v_a_1228_);
    v___x_1231_ = lean_apply_2(v_x_u2082_1227_, v___x_1230_, v_a_1228_);
    return v___x_1231_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_u2082_1232_: *mut LeanObject,
    mut v_a_1233_: *mut LeanObject,
    mut v_x_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1235_: *mut LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0(
        v_x_u2082_1232_,
        v_a_1233_,
        v_x_1234_,
    );
    lean_dec(v_a_1233_);
    return v_res_1235_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
    mut v_inst_1236_: *mut LeanObject,
    mut v_x_u2081_1237_: *mut LeanObject,
    mut v_x_u2082_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_1240_ = lean_ctor_get(v_inst_1236_, 2);
    lean_inc(v_orElse_1240_);
    lean_dec_ref(v_inst_1236_);
    lean_inc_n(v_a_1239_, 2);
    v___f_1241_ = lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1241_, 0, v_x_u2082_1238_);
    lean_closure_set(v___f_1241_, 1, v_a_1239_);
    v___x_1242_ = lean_apply_1(v_x_u2081_1237_, v_a_1239_);
    v___x_1243_ = lean_apply_3(v_orElse_1240_, lean_box(0), v___x_1242_, v___f_1241_);
    return v___x_1243_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___boxed(
    mut v_inst_1244_: *mut LeanObject,
    mut v_x_u2081_1245_: *mut LeanObject,
    mut v_x_u2082_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg(
        v_inst_1244_,
        v_x_u2081_1245_,
        v_x_u2082_1246_,
        v_a_1247_,
    );
    lean_dec(v_a_1247_);
    return v_res_1248_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3(
    mut v_00_u03c9_1249_: *mut LeanObject,
    mut v_00_u03c3_1250_: *mut LeanObject,
    mut v_m_1251_: *mut LeanObject,
    mut v_inst_1252_: *mut LeanObject,
    mut v_00_u03b1_1253_: *mut LeanObject,
    mut v_x_u2081_1254_: *mut LeanObject,
    mut v_x_u2082_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_1257_ = lean_ctor_get(v_inst_1252_, 2);
    lean_inc(v_orElse_1257_);
    lean_dec_ref(v_inst_1252_);
    lean_inc_n(v_a_1256_, 2);
    v___f_1258_ = lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1258_, 0, v_x_u2082_1255_);
    lean_closure_set(v___f_1258_, 1, v_a_1256_);
    v___x_1259_ = lean_apply_1(v_x_u2081_1254_, v_a_1256_);
    v___x_1260_ = lean_apply_3(v_orElse_1257_, lean_box(0), v___x_1259_, v___f_1258_);
    return v___x_1260_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed(
    mut v_00_u03c9_1261_: *mut LeanObject,
    mut v_00_u03c3_1262_: *mut LeanObject,
    mut v_m_1263_: *mut LeanObject,
    mut v_inst_1264_: *mut LeanObject,
    mut v_00_u03b1_1265_: *mut LeanObject,
    mut v_x_u2081_1266_: *mut LeanObject,
    mut v_x_u2082_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1269_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1268_);
    return v_res_1269_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad___redArg(
    mut v_inst_1270_: *mut LeanObject,
    mut v_inst_1271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_StateRefT_x27_instMonad___redArg(v_inst_1271_);
    v_toApplicative_1273_ = lean_ctor_get(v___x_1272_, 0);
    lean_inc_ref(v_toApplicative_1273_);
    lean_dec_ref(v___x_1272_);
    lean_inc_ref(v_inst_1270_);
    v___x_1274_ = lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__1___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_1274_, 0, lean_box(0));
    lean_closure_set(v___x_1274_, 1, lean_box(0));
    lean_closure_set(v___x_1274_, 2, lean_box(0));
    lean_closure_set(v___x_1274_, 3, v_inst_1270_);
    v___x_1275_ = lean_alloc_closure(
        l_StateRefT_x27_instAlternativeOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___x_1275_, 0, lean_box(0));
    lean_closure_set(v___x_1275_, 1, lean_box(0));
    lean_closure_set(v___x_1275_, 2, lean_box(0));
    lean_closure_set(v___x_1275_, 3, v_inst_1270_);
    v___x_1276_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1276_, 0, v_toApplicative_1273_);
    lean_ctor_set(v___x_1276_, 1, v___x_1274_);
    lean_ctor_set(v___x_1276_, 2, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_StateRefT_x27_instAlternativeOfMonad(
    mut v_00_u03c9_1277_: *mut LeanObject,
    mut v_00_u03c3_1278_: *mut LeanObject,
    mut v_m_1279_: *mut LeanObject,
    mut v_inst_1280_: *mut LeanObject,
    mut v_inst_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v_inst_1280_, v_inst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(
    mut v_x_1283_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1283_);
    return v_x_1283_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0___boxed(
    mut v_x_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1285_: *mut LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___lam__0(v_x_1284_);
    lean_dec(v_x_1284_);
    return v_res_1285_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
    mut v_inst_1287_: *mut LeanObject,
    mut v_inst_1288_: *mut LeanObject,
    mut v_x_1289_: *mut LeanObject,
    mut v_r_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1291_ = lean_ctor_get(v_inst_1287_, 0);
    lean_inc_ref(v_toApplicative_1291_);
    lean_dec_ref(v_inst_1287_);
    v_toFunctor_1292_ = lean_ctor_get(v_toApplicative_1291_, 0);
    lean_inc_ref(v_toFunctor_1292_);
    lean_dec_ref(v_toApplicative_1291_);
    v_map_1293_ = lean_ctor_get(v_toFunctor_1292_, 0);
    lean_inc(v_map_1293_);
    lean_dec_ref(v_toFunctor_1292_);
    v___f_1294_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    lean_inc(v_r_1290_);
    v___x_1295_ = lean_apply_1(v_x_1289_, v_r_1290_);
    v___x_1296_ = lean_apply_2(v_inst_1288_, lean_box(0), v___x_1295_);
    v___x_1297_ = lean_apply_4(
        v_map_1293_,
        lean_box(0),
        lean_box(0),
        v___f_1294_,
        v___x_1296_,
    );
    return v___x_1297_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___boxed(
    mut v_inst_1298_: *mut LeanObject,
    mut v_inst_1299_: *mut LeanObject,
    mut v_x_1300_: *mut LeanObject,
    mut v_r_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg(
        v_inst_1298_,
        v_inst_1299_,
        v_x_1300_,
        v_r_1301_,
    );
    lean_dec(v_r_1301_);
    return v_res_1302_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3(
    mut v_00_u03c9_1303_: *mut LeanObject,
    mut v_00_u03c3_1304_: *mut LeanObject,
    mut v_m_1305_: *mut LeanObject,
    mut v_inst_1306_: *mut LeanObject,
    mut v_inst_1307_: *mut LeanObject,
    mut v_00_u03b1_1308_: *mut LeanObject,
    mut v_x_1309_: *mut LeanObject,
    mut v_r_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1311_ = lean_ctor_get(v_inst_1306_, 0);
    lean_inc_ref(v_toApplicative_1311_);
    lean_dec_ref(v_inst_1306_);
    v_toFunctor_1312_ = lean_ctor_get(v_toApplicative_1311_, 0);
    lean_inc_ref(v_toFunctor_1312_);
    lean_dec_ref(v_toApplicative_1311_);
    v_map_1313_ = lean_ctor_get(v_toFunctor_1312_, 0);
    lean_inc(v_map_1313_);
    lean_dec_ref(v_toFunctor_1312_);
    v___f_1314_ = l_StateRefT_x27_instMonadAttachOfMonad___aux__3___redArg___closed__0;
    lean_inc(v_r_1310_);
    v___x_1315_ = lean_apply_1(v_x_1309_, v_r_1310_);
    v___x_1316_ = lean_apply_2(v_inst_1307_, lean_box(0), v___x_1315_);
    v___x_1317_ = lean_apply_4(
        v_map_1313_,
        lean_box(0),
        lean_box(0),
        v___f_1314_,
        v___x_1316_,
    );
    return v___x_1317_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed(
    mut v_00_u03c9_1318_: *mut LeanObject,
    mut v_00_u03c3_1319_: *mut LeanObject,
    mut v_m_1320_: *mut LeanObject,
    mut v_inst_1321_: *mut LeanObject,
    mut v_inst_1322_: *mut LeanObject,
    mut v_00_u03b1_1323_: *mut LeanObject,
    mut v_x_1324_: *mut LeanObject,
    mut v_r_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1326_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_r_1325_);
    return v_res_1326_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad___redArg(
    mut v_inst_1327_: *mut LeanObject,
    mut v_inst_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1329_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___x_1329_, 0, lean_box(0));
    lean_closure_set(v___x_1329_, 1, lean_box(0));
    lean_closure_set(v___x_1329_, 2, lean_box(0));
    lean_closure_set(v___x_1329_, 3, v_inst_1327_);
    lean_closure_set(v___x_1329_, 4, v_inst_1328_);
    return v___x_1329_;
}
pub unsafe fn l_StateRefT_x27_instMonadAttachOfMonad(
    mut v_00_u03c9_1330_: *mut LeanObject,
    mut v_00_u03c3_1331_: *mut LeanObject,
    mut v_m_1332_: *mut LeanObject,
    mut v_inst_1333_: *mut LeanObject,
    mut v_inst_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadAttachOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___x_1335_, 0, lean_box(0));
    lean_closure_set(v___x_1335_, 1, lean_box(0));
    lean_closure_set(v___x_1335_, 2, lean_box(0));
    lean_closure_set(v___x_1335_, 3, v_inst_1333_);
    lean_closure_set(v___x_1335_, 4, v_inst_1334_);
    return v___x_1335_;
}
pub unsafe fn l_StateRefT_x27_get___redArg(
    mut v_inst_1336_: *mut LeanObject,
    mut v_ref_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1337_);
    v___x_1338_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1338_, 0, lean_box(0));
    lean_closure_set(v___x_1338_, 1, lean_box(0));
    lean_closure_set(v___x_1338_, 2, v_ref_1337_);
    v___x_1339_ = lean_apply_2(v_inst_1336_, lean_box(0), v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_StateRefT_x27_get___redArg___boxed(
    mut v_inst_1340_: *mut LeanObject,
    mut v_ref_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1342_: *mut LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_StateRefT_x27_get___redArg(v_inst_1340_, v_ref_1341_);
    lean_dec(v_ref_1341_);
    return v_res_1342_;
}
pub unsafe fn l_StateRefT_x27_get(
    mut v_00_u03c9_1343_: *mut LeanObject,
    mut v_00_u03c3_1344_: *mut LeanObject,
    mut v_m_1345_: *mut LeanObject,
    mut v_inst_1346_: *mut LeanObject,
    mut v_ref_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1347_);
    v___x_1348_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1348_, 0, lean_box(0));
    lean_closure_set(v___x_1348_, 1, lean_box(0));
    lean_closure_set(v___x_1348_, 2, v_ref_1347_);
    v___x_1349_ = lean_apply_2(v_inst_1346_, lean_box(0), v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_StateRefT_x27_get___boxed(
    mut v_00_u03c9_1350_: *mut LeanObject,
    mut v_00_u03c3_1351_: *mut LeanObject,
    mut v_m_1352_: *mut LeanObject,
    mut v_inst_1353_: *mut LeanObject,
    mut v_ref_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_StateRefT_x27_get(
        v_00_u03c9_1350_,
        v_00_u03c3_1351_,
        v_m_1352_,
        v_inst_1353_,
        v_ref_1354_,
    );
    lean_dec(v_ref_1354_);
    return v_res_1355_;
}
pub unsafe fn l_StateRefT_x27_set___redArg(
    mut v_inst_1356_: *mut LeanObject,
    mut v_s_1357_: *mut LeanObject,
    mut v_ref_1358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1358_);
    v___x_1359_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1359_, 0, lean_box(0));
    lean_closure_set(v___x_1359_, 1, lean_box(0));
    lean_closure_set(v___x_1359_, 2, v_ref_1358_);
    lean_closure_set(v___x_1359_, 3, v_s_1357_);
    v___x_1360_ = lean_apply_2(v_inst_1356_, lean_box(0), v___x_1359_);
    return v___x_1360_;
}
pub unsafe fn l_StateRefT_x27_set___redArg___boxed(
    mut v_inst_1361_: *mut LeanObject,
    mut v_s_1362_: *mut LeanObject,
    mut v_ref_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1364_: *mut LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_StateRefT_x27_set___redArg(v_inst_1361_, v_s_1362_, v_ref_1363_);
    lean_dec(v_ref_1363_);
    return v_res_1364_;
}
pub unsafe fn l_StateRefT_x27_set(
    mut v_00_u03c9_1365_: *mut LeanObject,
    mut v_00_u03c3_1366_: *mut LeanObject,
    mut v_m_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
    mut v_s_1369_: *mut LeanObject,
    mut v_ref_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1370_);
    v___x_1371_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1371_, 0, lean_box(0));
    lean_closure_set(v___x_1371_, 1, lean_box(0));
    lean_closure_set(v___x_1371_, 2, v_ref_1370_);
    lean_closure_set(v___x_1371_, 3, v_s_1369_);
    v___x_1372_ = lean_apply_2(v_inst_1368_, lean_box(0), v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_StateRefT_x27_set___boxed(
    mut v_00_u03c9_1373_: *mut LeanObject,
    mut v_00_u03c3_1374_: *mut LeanObject,
    mut v_m_1375_: *mut LeanObject,
    mut v_inst_1376_: *mut LeanObject,
    mut v_s_1377_: *mut LeanObject,
    mut v_ref_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1379_: *mut LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_StateRefT_x27_set(
        v_00_u03c9_1373_,
        v_00_u03c3_1374_,
        v_m_1375_,
        v_inst_1376_,
        v_s_1377_,
        v_ref_1378_,
    );
    lean_dec(v_ref_1378_);
    return v_res_1379_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg(
    mut v_inst_1380_: *mut LeanObject,
    mut v_f_1381_: *mut LeanObject,
    mut v_ref_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1382_);
    v___x_1383_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_1383_, 0, lean_box(0));
    lean_closure_set(v___x_1383_, 1, lean_box(0));
    lean_closure_set(v___x_1383_, 2, lean_box(0));
    lean_closure_set(v___x_1383_, 3, v_ref_1382_);
    lean_closure_set(v___x_1383_, 4, v_f_1381_);
    v___x_1384_ = lean_apply_2(v_inst_1380_, lean_box(0), v___x_1383_);
    return v___x_1384_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___redArg___boxed(
    mut v_inst_1385_: *mut LeanObject,
    mut v_f_1386_: *mut LeanObject,
    mut v_ref_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_StateRefT_x27_modifyGet___redArg(v_inst_1385_, v_f_1386_, v_ref_1387_);
    lean_dec(v_ref_1387_);
    return v_res_1388_;
}
pub unsafe fn l_StateRefT_x27_modifyGet(
    mut v_00_u03c9_1389_: *mut LeanObject,
    mut v_00_u03c3_1390_: *mut LeanObject,
    mut v_m_1391_: *mut LeanObject,
    mut v_00_u03b1_1392_: *mut LeanObject,
    mut v_inst_1393_: *mut LeanObject,
    mut v_f_1394_: *mut LeanObject,
    mut v_ref_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_1395_);
    v___x_1396_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_1396_, 0, lean_box(0));
    lean_closure_set(v___x_1396_, 1, lean_box(0));
    lean_closure_set(v___x_1396_, 2, lean_box(0));
    lean_closure_set(v___x_1396_, 3, v_ref_1395_);
    lean_closure_set(v___x_1396_, 4, v_f_1394_);
    v___x_1397_ = lean_apply_2(v_inst_1393_, lean_box(0), v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn l_StateRefT_x27_modifyGet___boxed(
    mut v_00_u03c9_1398_: *mut LeanObject,
    mut v_00_u03c3_1399_: *mut LeanObject,
    mut v_m_1400_: *mut LeanObject,
    mut v_00_u03b1_1401_: *mut LeanObject,
    mut v_inst_1402_: *mut LeanObject,
    mut v_f_1403_: *mut LeanObject,
    mut v_ref_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1405_: *mut LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_StateRefT_x27_modifyGet(
        v_00_u03c9_1398_,
        v_00_u03c3_1399_,
        v_m_1400_,
        v_00_u03b1_1401_,
        v_inst_1402_,
        v_f_1403_,
        v_ref_1404_,
    );
    lean_dec(v_ref_1404_);
    return v_res_1405_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
    mut v_inst_1406_: *mut LeanObject,
    mut v_00_u03b1_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1409_);
    v___x_1410_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_1410_, 0, lean_box(0));
    lean_closure_set(v___x_1410_, 1, lean_box(0));
    lean_closure_set(v___x_1410_, 2, lean_box(0));
    lean_closure_set(v___x_1410_, 3, v___y_1409_);
    lean_closure_set(v___x_1410_, 4, v___y_1408_);
    v___x_1411_ = lean_apply_2(v_inst_1406_, lean_box(0), v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed(
    mut v_inst_1412_: *mut LeanObject,
    mut v_00_u03b1_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1416_: *mut LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0(
        v_inst_1412_,
        v_00_u03b1_1413_,
        v___y_1414_,
        v___y_1415_,
    );
    lean_dec(v___y_1415_);
    return v_res_1416_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(
    mut v_inst_1417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_inst_1417_, 2);
    v___f_1418_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1418_, 0, v_inst_1417_);
    v___x_1419_ = lean_alloc_closure(l_StateRefT_x27_get___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1419_, 0, lean_box(0));
    lean_closure_set(v___x_1419_, 1, lean_box(0));
    lean_closure_set(v___x_1419_, 2, lean_box(0));
    lean_closure_set(v___x_1419_, 3, v_inst_1417_);
    v___x_1420_ = lean_alloc_closure(l_StateRefT_x27_set___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1420_, 0, lean_box(0));
    lean_closure_set(v___x_1420_, 1, lean_box(0));
    lean_closure_set(v___x_1420_, 2, lean_box(0));
    lean_closure_set(v___x_1420_, 3, v_inst_1417_);
    v___x_1421_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1421_, 0, v___x_1419_);
    lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    lean_ctor_set(v___x_1421_, 2, v___f_1418_);
    return v___x_1421_;
}
pub unsafe fn l_StateRefT_x27_instMonadStateOfOfMonadLiftTST(
    mut v_00_u03c9_1422_: *mut LeanObject,
    mut v_00_u03c3_1423_: *mut LeanObject,
    mut v_m_1424_: *mut LeanObject,
    mut v_inst_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v_inst_1425_);
    return v___x_1426_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
    mut v_inst_1427_: *mut LeanObject,
    mut v_00_u03b1_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v_throw_1431_ = lean_ctor_get(v_inst_1427_, 0);
    lean_inc(v_throw_1431_);
    lean_dec_ref(v_inst_1427_);
    v___x_1432_ = lean_apply_2(v_throw_1431_, lean_box(0), v___y_1429_);
    return v___x_1432_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(
    mut v_inst_1433_: *mut LeanObject,
    mut v_00_u03b1_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_StateRefT_x27_instMonadExceptOf___redArg___lam__0(
        v_inst_1433_,
        v_00_u03b1_1434_,
        v___y_1435_,
        v___y_1436_,
    );
    lean_dec(v___y_1436_);
    return v_res_1437_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__1(
    mut v_c_1438_: *mut LeanObject,
    mut v_s_1439_: *mut LeanObject,
    mut v_e_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1441_ = lean_apply_2(v_c_1438_, v_e_1440_, v_s_1439_);
    return v___x_1441_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(
    mut v_inst_1442_: *mut LeanObject,
    mut v_00_u03b1_1443_: *mut LeanObject,
    mut v_x_1444_: *mut LeanObject,
    mut v_c_1445_: *mut LeanObject,
    mut v_s_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_1447_ = lean_ctor_get(v_inst_1442_, 1);
    lean_inc(v_tryCatch_1447_);
    lean_dec_ref(v_inst_1442_);
    lean_inc(v_s_1446_);
    v___f_1448_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1448_, 0, v_c_1445_);
    lean_closure_set(v___f_1448_, 1, v_s_1446_);
    v___x_1449_ = lean_apply_1(v_x_1444_, v_s_1446_);
    v___x_1450_ = lean_apply_3(v_tryCatch_1447_, lean_box(0), v___x_1449_, v___f_1448_);
    return v___x_1450_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf___redArg(
    mut v_inst_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1451_);
    v___f_1452_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1452_, 0, v_inst_1451_);
    v___f_1453_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1453_, 0, v_inst_1451_);
    v___x_1454_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1454_, 0, v___f_1452_);
    lean_ctor_set(v___x_1454_, 1, v___f_1453_);
    return v___x_1454_;
}
pub unsafe fn l_StateRefT_x27_instMonadExceptOf(
    mut v_00_u03c9_1455_: *mut LeanObject,
    mut v_00_u03c3_1456_: *mut LeanObject,
    mut v_m_1457_: *mut LeanObject,
    mut v_00_u03b5_1458_: *mut LeanObject,
    mut v_inst_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1459_);
    v___f_1460_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1460_, 0, v_inst_1459_);
    v___f_1461_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1461_, 0, v_inst_1459_);
    v___x_1462_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1462_, 0, v___f_1460_);
    lean_ctor_set(v___x_1462_, 1, v___f_1461_);
    return v___x_1462_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
    mut v_ctx_1463_: *mut LeanObject,
    mut v_00_u03b2_1464_: *mut LeanObject,
    mut v_x_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1463_);
    v___x_1466_ = lean_apply_1(v_x_1465_, v_ctx_1463_);
    return v___x_1466_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_ctx_1467_: *mut LeanObject,
    mut v_00_u03b2_1468_: *mut LeanObject,
    mut v_x_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1470_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0(
        v_ctx_1467_,
        v_00_u03b2_1468_,
        v_x_1469_,
    );
    lean_dec(v_ctx_1467_);
    return v_res_1470_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg(
    mut v_f_1471_: *mut LeanObject,
    mut v_ctx_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1472_);
    v___f_1473_ = lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1473_, 0, v_ctx_1472_);
    v___x_1474_ = lean_apply_1(v_f_1471_, v___f_1473_);
    return v___x_1474_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___redArg___boxed(
    mut v_f_1475_: *mut LeanObject,
    mut v_ctx_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_instMonadControlStateRefT_x27___aux__1___redArg(v_f_1475_, v_ctx_1476_);
    lean_dec(v_ctx_1476_);
    return v_res_1477_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1(
    mut v_00_u03c9_1478_: *mut LeanObject,
    mut v_00_u03c3_1479_: *mut LeanObject,
    mut v_m_1480_: *mut LeanObject,
    mut v_00_u03b1_1481_: *mut LeanObject,
    mut v_f_1482_: *mut LeanObject,
    mut v_ctx_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1483_);
    v___f_1484_ = lean_alloc_closure(
        l_instMonadControlStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1484_, 0, v_ctx_1483_);
    v___x_1485_ = lean_apply_1(v_f_1482_, v___f_1484_);
    return v___x_1485_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__1___boxed(
    mut v_00_u03c9_1486_: *mut LeanObject,
    mut v_00_u03c3_1487_: *mut LeanObject,
    mut v_m_1488_: *mut LeanObject,
    mut v_00_u03b1_1489_: *mut LeanObject,
    mut v_f_1490_: *mut LeanObject,
    mut v_ctx_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1492_: *mut LeanObject = core::ptr::null_mut();
    v_res_1492_ = l_instMonadControlStateRefT_x27___aux__1(
        v_00_u03c9_1486_,
        v_00_u03c3_1487_,
        v_m_1488_,
        v_00_u03b1_1489_,
        v_f_1490_,
        v_ctx_1491_,
    );
    lean_dec(v_ctx_1491_);
    return v_res_1492_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg(
    mut v_x_1493_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1493_);
    return v_x_1493_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___redArg___boxed(
    mut v_x_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1495_: *mut LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_instMonadControlStateRefT_x27___aux__3___redArg(v_x_1494_);
    lean_dec(v_x_1494_);
    return v_res_1495_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3(
    mut v_00_u03c9_1496_: *mut LeanObject,
    mut v_00_u03c3_1497_: *mut LeanObject,
    mut v_m_1498_: *mut LeanObject,
    mut v_00_u03b1_1499_: *mut LeanObject,
    mut v_x_1500_: *mut LeanObject,
    mut v_x_1501_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1500_);
    return v_x_1500_;
}
pub unsafe fn l_instMonadControlStateRefT_x27___aux__3___boxed(
    mut v_00_u03c9_1502_: *mut LeanObject,
    mut v_00_u03c3_1503_: *mut LeanObject,
    mut v_m_1504_: *mut LeanObject,
    mut v_00_u03b1_1505_: *mut LeanObject,
    mut v_x_1506_: *mut LeanObject,
    mut v_x_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_instMonadControlStateRefT_x27___aux__3(
        v_00_u03c9_1502_,
        v_00_u03c3_1503_,
        v_m_1504_,
        v_00_u03b1_1505_,
        v_x_1506_,
        v_x_1507_,
    );
    lean_dec(v_x_1507_);
    lean_dec(v_x_1506_);
    return v_res_1508_;
}
pub unsafe fn l_instMonadControlStateRefT_x27(
    mut v_00_u03c9_1514_: *mut LeanObject,
    mut v_00_u03c3_1515_: *mut LeanObject,
    mut v_m_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_instMonadControlStateRefT_x27___closed__2;
    return v___x_1517_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
    mut v_h_1518_: *mut LeanObject,
    mut v_ctx_1519_: *mut LeanObject,
    mut v_a_x3f_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_1519_);
    v___x_1521_ = lean_apply_2(v_h_1518_, v_a_x3f_1520_, v_ctx_1519_);
    return v___x_1521_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed(
    mut v_h_1522_: *mut LeanObject,
    mut v_ctx_1523_: *mut LeanObject,
    mut v_a_x3f_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0(
        v_h_1522_,
        v_ctx_1523_,
        v_a_x3f_1524_,
    );
    lean_dec(v_ctx_1523_);
    return v_res_1525_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg(
    mut v_inst_1526_: *mut LeanObject,
    mut v_x_1527_: *mut LeanObject,
    mut v_h_1528_: *mut LeanObject,
    mut v_ctx_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_ctx_1529_, 2);
    v___f_1530_ = lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1530_, 0, v_h_1528_);
    lean_closure_set(v___f_1530_, 1, v_ctx_1529_);
    v___x_1531_ = lean_apply_1(v_x_1527_, v_ctx_1529_);
    v___x_1532_ = lean_apply_4(
        v_inst_1526_,
        lean_box(0),
        lean_box(0),
        v___x_1531_,
        v___f_1530_,
    );
    return v___x_1532_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___redArg___boxed(
    mut v_inst_1533_: *mut LeanObject,
    mut v_x_1534_: *mut LeanObject,
    mut v_h_1535_: *mut LeanObject,
    mut v_ctx_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1537_: *mut LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_instMonadFinallyStateRefT_x27___aux__1___redArg(
        v_inst_1533_,
        v_x_1534_,
        v_h_1535_,
        v_ctx_1536_,
    );
    lean_dec(v_ctx_1536_);
    return v_res_1537_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1(
    mut v_m_1538_: *mut LeanObject,
    mut v_00_u03c9_1539_: *mut LeanObject,
    mut v_00_u03c3_1540_: *mut LeanObject,
    mut v_inst_1541_: *mut LeanObject,
    mut v_00_u03b1_1542_: *mut LeanObject,
    mut v_00_u03b2_1543_: *mut LeanObject,
    mut v_x_1544_: *mut LeanObject,
    mut v_h_1545_: *mut LeanObject,
    mut v_ctx_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_ctx_1546_, 2);
    v___f_1547_ = lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1547_, 0, v_h_1545_);
    lean_closure_set(v___f_1547_, 1, v_ctx_1546_);
    v___x_1548_ = lean_apply_1(v_x_1544_, v_ctx_1546_);
    v___x_1549_ = lean_apply_4(
        v_inst_1541_,
        lean_box(0),
        lean_box(0),
        v___x_1548_,
        v___f_1547_,
    );
    return v___x_1549_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___aux__1___boxed(
    mut v_m_1550_: *mut LeanObject,
    mut v_00_u03c9_1551_: *mut LeanObject,
    mut v_00_u03c3_1552_: *mut LeanObject,
    mut v_inst_1553_: *mut LeanObject,
    mut v_00_u03b1_1554_: *mut LeanObject,
    mut v_00_u03b2_1555_: *mut LeanObject,
    mut v_x_1556_: *mut LeanObject,
    mut v_h_1557_: *mut LeanObject,
    mut v_ctx_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1559_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_ctx_1558_);
    return v_res_1559_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27___redArg(
    mut v_inst_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1561_ = lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1561_, 0, lean_box(0));
    lean_closure_set(v___x_1561_, 1, lean_box(0));
    lean_closure_set(v___x_1561_, 2, lean_box(0));
    lean_closure_set(v___x_1561_, 3, v_inst_1560_);
    return v___x_1561_;
}
pub unsafe fn l_instMonadFinallyStateRefT_x27(
    mut v_m_1562_: *mut LeanObject,
    mut v_00_u03c9_1563_: *mut LeanObject,
    mut v_00_u03c3_1564_: *mut LeanObject,
    mut v_inst_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = lean_alloc_closure(
        l_instMonadFinallyStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_1566_, 0, lean_box(0));
    lean_closure_set(v___x_1566_, 1, lean_box(0));
    lean_closure_set(v___x_1566_, 2, lean_box(0));
    lean_closure_set(v___x_1566_, 3, v_inst_1565_);
    return v___x_1566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_StateRef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_ST(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Reader(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_StateRef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_StateRef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_ST(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Reader(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_StateRef(builtin);
}
