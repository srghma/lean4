// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Loop
// Imports: Init.Data.Iterators.Consumers.Monadic.Partial Init.Data.Iterators.Internal.LawfulMonadLiftFunction Init.WFExtrinsicFix Init.Data.Iterators.Consumers.Monadic.Total Init.PropLemmas
use crate::ffi::lean_nat_add;
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Partial::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Partial,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Total::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total,
};
use crate::r#gen::Init::Data::Iterators::Internal::LawfulMonadLiftFunction::{
    initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction,
    runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::{
    initialize_Init_WFExtrinsicFix, l_WellFounded_opaqueFix_u2083___redArg,
    runtime_initialize_Init_WFExtrinsicFix,
};
pub static l_Std_IterM_foldM___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_IterM_foldM___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IterM_foldM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_foldM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_IterM_isEmpty___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_IteratorLoop_WithWF_instWellFoundedRelation(
    mut v_00_u03b1_2408_: *mut crate::leanh::LeanObject,
    mut v_m_2409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2410_: *mut crate::leanh::LeanObject,
    mut v_inst_2411_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2412_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2413_: *mut crate::leanh::LeanObject,
    mut v_hwf_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = crate::leanh::lean_box(0);
    return v___x_2415_;
}
pub unsafe fn l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(
    mut v_00_u03b1_2416_: *mut crate::leanh::LeanObject,
    mut v_m_2417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2420_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2421_: *mut crate::leanh::LeanObject,
    mut v_hwf_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(
        v_00_u03b1_2416_,
        v_m_2417_,
        v_00_u03b2_2418_,
        v_inst_2419_,
        v_00_u03b3_2420_,
        v_PlausibleForInStep_2421_,
        v_hwf_2422_,
    );
    crate::leanh::lean_dec(v_inst_2419_);
    return v_res_2423_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(
    mut v_toPure_2424_: *mut crate::leanh::LeanObject,
    mut v_recur_2425_: *mut crate::leanh::LeanObject,
    mut v_it_2426_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2427_) == 0 {
        let mut v_a_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_2426_);
        crate::leanh::lean_dec(v_recur_2425_);
        v_a_2428_ = crate::leanh::lean_ctor_get(v_____do__lift_2427_, 0);
        crate::leanh::lean_inc(v_a_2428_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2427_, 1);
        v___x_2429_ =
            crate::leanh::lean_apply_2(v_toPure_2424_, crate::leanh::lean_box(0), v_a_2428_);
        return v___x_2429_;
    } else {
        let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2424_);
        v_a_2430_ = crate::leanh::lean_ctor_get(v_____do__lift_2427_, 0);
        crate::leanh::lean_inc(v_a_2430_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2427_, 1);
        v___x_2431_ = crate::leanh::lean_apply_4(
            v_recur_2425_,
            v_it_2426_,
            v_a_2430_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_2431_;
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(
    mut v_toPure_2432_: *mut crate::leanh::LeanObject,
    mut v_recur_2433_: *mut crate::leanh::LeanObject,
    mut v_f_2434_: *mut crate::leanh::LeanObject,
    mut v_acc_2435_: *mut crate::leanh::LeanObject,
    mut v_toBind_2436_: *mut crate::leanh::LeanObject,
    mut v_s_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_2437_) {
        0 => {
            let mut v_it_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_2438_ = crate::leanh::lean_ctor_get(v_s_2437_, 0);
            crate::leanh::lean_inc(v_it_2438_);
            v_out_2439_ = crate::leanh::lean_ctor_get(v_s_2437_, 1);
            crate::leanh::lean_inc(v_out_2439_);
            crate::leanh::lean_dec_ref_known(v_s_2437_, 2);
            v___f_2440_ = crate::leanh::lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_2440_, 0, v_toPure_2432_);
            crate::leanh::lean_closure_set(v___f_2440_, 1, v_recur_2433_);
            crate::leanh::lean_closure_set(v___f_2440_, 2, v_it_2438_);
            v___x_2441_ = crate::leanh::lean_apply_3(
                v_f_2434_,
                v_out_2439_,
                crate::leanh::lean_box(0),
                v_acc_2435_,
            );
            v___x_2442_ = crate::leanh::lean_apply_4(
                v_toBind_2436_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2441_,
                v___f_2440_,
            );
            return v___x_2442_;
        }
        1 => {
            let mut v_it_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2436_);
            crate::leanh::lean_dec(v_f_2434_);
            crate::leanh::lean_dec(v_toPure_2432_);
            v_it_2443_ = crate::leanh::lean_ctor_get(v_s_2437_, 0);
            crate::leanh::lean_inc(v_it_2443_);
            crate::leanh::lean_dec_ref_known(v_s_2437_, 1);
            v___x_2444_ = crate::leanh::lean_apply_4(
                v_recur_2433_,
                v_it_2443_,
                v_acc_2435_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_2444_;
        }
        _ => {
            let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2436_);
            crate::leanh::lean_dec(v_f_2434_);
            crate::leanh::lean_dec(v_recur_2433_);
            v___x_2445_ =
                crate::leanh::lean_apply_2(v_toPure_2432_, crate::leanh::lean_box(0), v_acc_2435_);
            return v___x_2445_;
        }
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(
    mut v_toPure_2446_: *mut crate::leanh::LeanObject,
    mut v_f_2447_: *mut crate::leanh::LeanObject,
    mut v_toBind_2448_: *mut crate::leanh::LeanObject,
    mut v_inst_2449_: *mut crate::leanh::LeanObject,
    mut v_lift_2450_: *mut crate::leanh::LeanObject,
    mut v_it_2451_: *mut crate::leanh::LeanObject,
    mut v_acc_2452_: *mut crate::leanh::LeanObject,
    mut v_hP_2453_: *mut crate::leanh::LeanObject,
    mut v_recur_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2455_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2455_, 0, v_toPure_2446_);
    crate::leanh::lean_closure_set(v___f_2455_, 1, v_recur_2454_);
    crate::leanh::lean_closure_set(v___f_2455_, 2, v_f_2447_);
    crate::leanh::lean_closure_set(v___f_2455_, 3, v_acc_2452_);
    crate::leanh::lean_closure_set(v___f_2455_, 4, v_toBind_2448_);
    v___x_2456_ = crate::leanh::lean_apply_1(v_inst_2449_, v_it_2451_);
    v___x_2457_ = crate::leanh::lean_apply_4(
        v_lift_2450_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2455_,
        v___x_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg(
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v_inst_2459_: *mut crate::leanh::LeanObject,
    mut v_lift_2460_: *mut crate::leanh::LeanObject,
    mut v_it_2461_: *mut crate::leanh::LeanObject,
    mut v_init_2462_: *mut crate::leanh::LeanObject,
    mut v_f_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2464_ = crate::leanh::lean_ctor_get(v_inst_2459_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2464_);
    v_toBind_2465_ = crate::leanh::lean_ctor_get(v_inst_2459_, 1);
    crate::leanh::lean_inc(v_toBind_2465_);
    crate::leanh::lean_dec_ref(v_inst_2459_);
    v_toPure_2466_ = crate::leanh::lean_ctor_get(v_toApplicative_2464_, 1);
    crate::leanh::lean_inc(v_toPure_2466_);
    crate::leanh::lean_dec_ref(v_toApplicative_2464_);
    v___f_2467_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2467_, 0, v_toPure_2466_);
    crate::leanh::lean_closure_set(v___f_2467_, 1, v_f_2463_);
    crate::leanh::lean_closure_set(v___f_2467_, 2, v_toBind_2465_);
    crate::leanh::lean_closure_set(v___f_2467_, 3, v_inst_2458_);
    crate::leanh::lean_closure_set(v___f_2467_, 4, v_lift_2460_);
    v___x_2468_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2467_,
        v_it_2461_,
        v_init_2462_,
        crate::leanh::lean_box(0),
    );
    return v___x_2468_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27(
    mut v_m_2469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2470_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2471_: *mut crate::leanh::LeanObject,
    mut v_inst_2472_: *mut crate::leanh::LeanObject,
    mut v_n_2473_: *mut crate::leanh::LeanObject,
    mut v_inst_2474_: *mut crate::leanh::LeanObject,
    mut v_lift_2475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2476_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2477_: *mut crate::leanh::LeanObject,
    mut v_it_2478_: *mut crate::leanh::LeanObject,
    mut v_init_2479_: *mut crate::leanh::LeanObject,
    mut v_P_2480_: *mut crate::leanh::LeanObject,
    mut v_hP_2481_: *mut crate::leanh::LeanObject,
    mut v_f_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2483_ = crate::leanh::lean_ctor_get(v_inst_2474_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2483_);
    v_toBind_2484_ = crate::leanh::lean_ctor_get(v_inst_2474_, 1);
    crate::leanh::lean_inc(v_toBind_2484_);
    crate::leanh::lean_dec_ref(v_inst_2474_);
    v_toPure_2485_ = crate::leanh::lean_ctor_get(v_toApplicative_2483_, 1);
    crate::leanh::lean_inc(v_toPure_2485_);
    crate::leanh::lean_dec_ref(v_toApplicative_2483_);
    v___f_2486_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2486_, 0, v_toPure_2485_);
    crate::leanh::lean_closure_set(v___f_2486_, 1, v_f_2482_);
    crate::leanh::lean_closure_set(v___f_2486_, 2, v_toBind_2484_);
    crate::leanh::lean_closure_set(v___f_2486_, 3, v_inst_2472_);
    crate::leanh::lean_closure_set(v___f_2486_, 4, v_lift_2475_);
    v___x_2487_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2486_,
        v_it_2478_,
        v_init_2479_,
        crate::leanh::lean_box(0),
    );
    return v___x_2487_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(
    mut v_toPure_2488_: *mut crate::leanh::LeanObject,
    mut v_inst_2489_: *mut crate::leanh::LeanObject,
    mut v_inst_2490_: *mut crate::leanh::LeanObject,
    mut v_lift_2491_: *mut crate::leanh::LeanObject,
    mut v_f_2492_: *mut crate::leanh::LeanObject,
    mut v_init_2493_: *mut crate::leanh::LeanObject,
    mut v_toBind_2494_: *mut crate::leanh::LeanObject,
    mut v_s_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_2495_) {
        0 => {
            let mut v_it_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_2496_ = crate::leanh::lean_ctor_get(v_s_2495_, 0);
            crate::leanh::lean_inc(v_it_2496_);
            v_out_2497_ = crate::leanh::lean_ctor_get(v_s_2495_, 1);
            crate::leanh::lean_inc(v_out_2497_);
            crate::leanh::lean_dec_ref_known(v_s_2495_, 2);
            crate::leanh::lean_inc(v_f_2492_);
            v___f_2498_ = crate::leanh::lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0
                    as *mut core::ffi::c_void,
                7,
                6,
            );
            crate::leanh::lean_closure_set(v___f_2498_, 0, v_toPure_2488_);
            crate::leanh::lean_closure_set(v___f_2498_, 1, v_inst_2489_);
            crate::leanh::lean_closure_set(v___f_2498_, 2, v_inst_2490_);
            crate::leanh::lean_closure_set(v___f_2498_, 3, v_lift_2491_);
            crate::leanh::lean_closure_set(v___f_2498_, 4, v_it_2496_);
            crate::leanh::lean_closure_set(v___f_2498_, 5, v_f_2492_);
            v___x_2499_ = crate::leanh::lean_apply_3(
                v_f_2492_,
                v_out_2497_,
                crate::leanh::lean_box(0),
                v_init_2493_,
            );
            v___x_2500_ = crate::leanh::lean_apply_4(
                v_toBind_2494_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2499_,
                v___f_2498_,
            );
            return v___x_2500_;
        }
        1 => {
            let mut v_it_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2494_);
            crate::leanh::lean_dec(v_toPure_2488_);
            v_it_2501_ = crate::leanh::lean_ctor_get(v_s_2495_, 0);
            crate::leanh::lean_inc(v_it_2501_);
            crate::leanh::lean_dec_ref_known(v_s_2495_, 1);
            v___x_2502_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(
                v_inst_2489_,
                v_inst_2490_,
                v_lift_2491_,
                v_it_2501_,
                v_init_2493_,
                v_f_2492_,
            );
            return v___x_2502_;
        }
        _ => {
            let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2494_);
            crate::leanh::lean_dec(v_f_2492_);
            crate::leanh::lean_dec(v_lift_2491_);
            crate::leanh::lean_dec_ref(v_inst_2490_);
            crate::leanh::lean_dec(v_inst_2489_);
            v___x_2503_ =
                crate::leanh::lean_apply_2(v_toPure_2488_, crate::leanh::lean_box(0), v_init_2493_);
            return v___x_2503_;
        }
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(
    mut v_inst_2504_: *mut crate::leanh::LeanObject,
    mut v_inst_2505_: *mut crate::leanh::LeanObject,
    mut v_lift_2506_: *mut crate::leanh::LeanObject,
    mut v_it_2507_: *mut crate::leanh::LeanObject,
    mut v_init_2508_: *mut crate::leanh::LeanObject,
    mut v_f_2509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2510_ = crate::leanh::lean_ctor_get(v_inst_2505_, 0);
    v_toBind_2511_ = crate::leanh::lean_ctor_get(v_inst_2505_, 1);
    crate::leanh::lean_inc(v_toBind_2511_);
    v_toPure_2512_ = crate::leanh::lean_ctor_get(v_toApplicative_2510_, 1);
    crate::leanh::lean_inc(v_toPure_2512_);
    crate::leanh::lean_inc(v_lift_2506_);
    crate::leanh::lean_inc(v_inst_2504_);
    v___f_2513_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2513_, 0, v_toPure_2512_);
    crate::leanh::lean_closure_set(v___f_2513_, 1, v_inst_2504_);
    crate::leanh::lean_closure_set(v___f_2513_, 2, v_inst_2505_);
    crate::leanh::lean_closure_set(v___f_2513_, 3, v_lift_2506_);
    crate::leanh::lean_closure_set(v___f_2513_, 4, v_f_2509_);
    crate::leanh::lean_closure_set(v___f_2513_, 5, v_init_2508_);
    crate::leanh::lean_closure_set(v___f_2513_, 6, v_toBind_2511_);
    v___x_2514_ = crate::leanh::lean_apply_1(v_inst_2504_, v_it_2507_);
    v___x_2515_ = crate::leanh::lean_apply_4(
        v_lift_2506_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2513_,
        v___x_2514_,
    );
    return v___x_2515_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(
    mut v_toPure_2516_: *mut crate::leanh::LeanObject,
    mut v_inst_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_lift_2519_: *mut crate::leanh::LeanObject,
    mut v_it_2520_: *mut crate::leanh::LeanObject,
    mut v_f_2521_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2522_) == 0 {
        let mut v_a_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_2521_);
        crate::leanh::lean_dec(v_it_2520_);
        crate::leanh::lean_dec(v_lift_2519_);
        crate::leanh::lean_dec_ref(v_inst_2518_);
        crate::leanh::lean_dec(v_inst_2517_);
        v_a_2523_ = crate::leanh::lean_ctor_get(v_____do__lift_2522_, 0);
        crate::leanh::lean_inc(v_a_2523_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2522_, 1);
        v___x_2524_ =
            crate::leanh::lean_apply_2(v_toPure_2516_, crate::leanh::lean_box(0), v_a_2523_);
        return v___x_2524_;
    } else {
        let mut v_a_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2516_);
        v_a_2525_ = crate::leanh::lean_ctor_get(v_____do__lift_2522_, 0);
        crate::leanh::lean_inc(v_a_2525_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2522_, 1);
        v___x_2526_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(
            v_inst_2517_,
            v_inst_2518_,
            v_lift_2519_,
            v_it_2520_,
            v_a_2525_,
            v_f_2521_,
        );
        return v___x_2526_;
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf(
    mut v_m_2527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2529_: *mut crate::leanh::LeanObject,
    mut v_inst_2530_: *mut crate::leanh::LeanObject,
    mut v_n_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
    mut v_lift_2533_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2534_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2535_: *mut crate::leanh::LeanObject,
    mut v_wf_2536_: *mut crate::leanh::LeanObject,
    mut v_it_2537_: *mut crate::leanh::LeanObject,
    mut v_init_2538_: *mut crate::leanh::LeanObject,
    mut v_P_2539_: *mut crate::leanh::LeanObject,
    mut v_hP_2540_: *mut crate::leanh::LeanObject,
    mut v_f_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(
        v_inst_2530_,
        v_inst_2532_,
        v_lift_2533_,
        v_it_2537_,
        v_init_2538_,
        v_f_2541_,
    );
    return v___x_2542_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(
    mut v_x_2543_: *mut crate::leanh::LeanObject,
    mut v_h__1_2544_: *mut crate::leanh::LeanObject,
    mut v_h__2_2545_: *mut crate::leanh::LeanObject,
    mut v_h__3_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2543_) {
        0 => {
            let mut v_it_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2546_);
            crate::leanh::lean_dec(v_h__2_2545_);
            v_it_2547_ = crate::leanh::lean_ctor_get(v_x_2543_, 0);
            crate::leanh::lean_inc(v_it_2547_);
            v_out_2548_ = crate::leanh::lean_ctor_get(v_x_2543_, 1);
            crate::leanh::lean_inc(v_out_2548_);
            crate::leanh::lean_dec_ref_known(v_x_2543_, 2);
            v___x_2549_ = crate::leanh::lean_apply_3(
                v_h__1_2544_,
                v_it_2547_,
                v_out_2548_,
                crate::leanh::lean_box(0),
            );
            return v___x_2549_;
        }
        1 => {
            let mut v_it_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2546_);
            crate::leanh::lean_dec(v_h__1_2544_);
            v_it_2550_ = crate::leanh::lean_ctor_get(v_x_2543_, 0);
            crate::leanh::lean_inc(v_it_2550_);
            crate::leanh::lean_dec_ref_known(v_x_2543_, 1);
            v___x_2551_ =
                crate::leanh::lean_apply_2(v_h__2_2545_, v_it_2550_, crate::leanh::lean_box(0));
            return v___x_2551_;
        }
        _ => {
            let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2545_);
            crate::leanh::lean_dec(v_h__1_2544_);
            v___x_2552_ = crate::leanh::lean_apply_1(v_h__3_2546_, crate::leanh::lean_box(0));
            return v___x_2552_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_2553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2554_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2555_: *mut crate::leanh::LeanObject,
    mut v_inst_2556_: *mut crate::leanh::LeanObject,
    mut v_it_2557_: *mut crate::leanh::LeanObject,
    mut v_motive_2558_: *mut crate::leanh::LeanObject,
    mut v_x_2559_: *mut crate::leanh::LeanObject,
    mut v_h__1_2560_: *mut crate::leanh::LeanObject,
    mut v_h__2_2561_: *mut crate::leanh::LeanObject,
    mut v_h__3_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2559_) {
        0 => {
            let mut v_it_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2562_);
            crate::leanh::lean_dec(v_h__2_2561_);
            v_it_2563_ = crate::leanh::lean_ctor_get(v_x_2559_, 0);
            crate::leanh::lean_inc(v_it_2563_);
            v_out_2564_ = crate::leanh::lean_ctor_get(v_x_2559_, 1);
            crate::leanh::lean_inc(v_out_2564_);
            crate::leanh::lean_dec_ref_known(v_x_2559_, 2);
            v___x_2565_ = crate::leanh::lean_apply_3(
                v_h__1_2560_,
                v_it_2563_,
                v_out_2564_,
                crate::leanh::lean_box(0),
            );
            return v___x_2565_;
        }
        1 => {
            let mut v_it_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2562_);
            crate::leanh::lean_dec(v_h__1_2560_);
            v_it_2566_ = crate::leanh::lean_ctor_get(v_x_2559_, 0);
            crate::leanh::lean_inc(v_it_2566_);
            crate::leanh::lean_dec_ref_known(v_x_2559_, 1);
            v___x_2567_ =
                crate::leanh::lean_apply_2(v_h__2_2561_, v_it_2566_, crate::leanh::lean_box(0));
            return v___x_2567_;
        }
        _ => {
            let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2561_);
            crate::leanh::lean_dec(v_h__1_2560_);
            v___x_2568_ = crate::leanh::lean_apply_1(v_h__3_2562_, crate::leanh::lean_box(0));
            return v___x_2568_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_2569_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2570_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2571_: *mut crate::leanh::LeanObject,
    mut v_inst_2572_: *mut crate::leanh::LeanObject,
    mut v_it_2573_: *mut crate::leanh::LeanObject,
    mut v_motive_2574_: *mut crate::leanh::LeanObject,
    mut v_x_2575_: *mut crate::leanh::LeanObject,
    mut v_h__1_2576_: *mut crate::leanh::LeanObject,
    mut v_h__2_2577_: *mut crate::leanh::LeanObject,
    mut v_h__3_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2579_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_2569_, v_00_u03b1_2570_, v_00_u03b2_2571_, v_inst_2572_, v_it_2573_, v_motive_2574_, v_x_2575_, v_h__1_2576_, v_h__2_2577_, v_h__3_2578_);
    crate::leanh::lean_dec(v_it_2573_);
    crate::leanh::lean_dec(v_inst_2572_);
    return v_res_2579_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_2580_: *mut crate::leanh::LeanObject,
    mut v_h__1_2581_: *mut crate::leanh::LeanObject,
    mut v_h__2_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2580_) == 0 {
        let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2581_);
        v_a_2583_ = crate::leanh::lean_ctor_get(v_____do__lift_2580_, 0);
        crate::leanh::lean_inc(v_a_2583_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2580_, 1);
        v___x_2584_ =
            crate::leanh::lean_apply_2(v_h__2_2582_, v_a_2583_, crate::leanh::lean_box(0));
        return v___x_2584_;
    } else {
        let mut v_a_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2582_);
        v_a_2585_ = crate::leanh::lean_ctor_get(v_____do__lift_2580_, 0);
        crate::leanh::lean_inc(v_a_2585_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2580_, 1);
        v___x_2586_ =
            crate::leanh::lean_apply_2(v_h__1_2581_, v_a_2585_, crate::leanh::lean_box(0));
        return v___x_2586_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_2587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2588_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2589_: *mut crate::leanh::LeanObject,
    mut v_acc_2590_: *mut crate::leanh::LeanObject,
    mut v_out_2591_: *mut crate::leanh::LeanObject,
    mut v_motive_2592_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2593_: *mut crate::leanh::LeanObject,
    mut v_h__1_2594_: *mut crate::leanh::LeanObject,
    mut v_h__2_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2593_) == 0 {
        let mut v_a_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2594_);
        v_a_2596_ = crate::leanh::lean_ctor_get(v_____do__lift_2593_, 0);
        crate::leanh::lean_inc(v_a_2596_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2593_, 1);
        v___x_2597_ =
            crate::leanh::lean_apply_2(v_h__2_2595_, v_a_2596_, crate::leanh::lean_box(0));
        return v___x_2597_;
    } else {
        let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2595_);
        v_a_2598_ = crate::leanh::lean_ctor_get(v_____do__lift_2593_, 0);
        crate::leanh::lean_inc(v_a_2598_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2593_, 1);
        v___x_2599_ =
            crate::leanh::lean_apply_2(v_h__1_2594_, v_a_2598_, crate::leanh::lean_box(0));
        return v___x_2599_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_2600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2601_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_2602_: *mut crate::leanh::LeanObject,
    mut v_acc_2603_: *mut crate::leanh::LeanObject,
    mut v_out_2604_: *mut crate::leanh::LeanObject,
    mut v_motive_2605_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2606_: *mut crate::leanh::LeanObject,
    mut v_h__1_2607_: *mut crate::leanh::LeanObject,
    mut v_h__2_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2609_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_2600_, v_00_u03b3_2601_, v_PlausibleForInStep_2602_, v_acc_2603_, v_out_2604_, v_motive_2605_, v_____do__lift_2606_, v_h__1_2607_, v_h__2_2608_);
    crate::leanh::lean_dec(v_out_2604_);
    crate::leanh::lean_dec(v_acc_2603_);
    return v_res_2609_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(
    mut v_toPure_2610_: *mut crate::leanh::LeanObject,
    mut v_recur_2611_: *mut crate::leanh::LeanObject,
    mut v___y_2612_: *mut crate::leanh::LeanObject,
    mut v_acc_2613_: *mut crate::leanh::LeanObject,
    mut v_toBind_2614_: *mut crate::leanh::LeanObject,
    mut v_s_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_2615_) {
        0 => {
            let mut v_it_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_2616_ = crate::leanh::lean_ctor_get(v_s_2615_, 0);
            crate::leanh::lean_inc(v_it_2616_);
            v_out_2617_ = crate::leanh::lean_ctor_get(v_s_2615_, 1);
            crate::leanh::lean_inc(v_out_2617_);
            crate::leanh::lean_dec_ref_known(v_s_2615_, 2);
            v___f_2618_ = crate::leanh::lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_2618_, 0, v_toPure_2610_);
            crate::leanh::lean_closure_set(v___f_2618_, 1, v_recur_2611_);
            crate::leanh::lean_closure_set(v___f_2618_, 2, v_it_2616_);
            v___x_2619_ = crate::leanh::lean_apply_3(
                v___y_2612_,
                v_out_2617_,
                crate::leanh::lean_box(0),
                v_acc_2613_,
            );
            v___x_2620_ = crate::leanh::lean_apply_4(
                v_toBind_2614_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2619_,
                v___f_2618_,
            );
            return v___x_2620_;
        }
        1 => {
            let mut v_it_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2614_);
            crate::leanh::lean_dec(v___y_2612_);
            crate::leanh::lean_dec(v_toPure_2610_);
            v_it_2621_ = crate::leanh::lean_ctor_get(v_s_2615_, 0);
            crate::leanh::lean_inc(v_it_2621_);
            crate::leanh::lean_dec_ref_known(v_s_2615_, 1);
            v___x_2622_ = crate::leanh::lean_apply_4(
                v_recur_2611_,
                v_it_2621_,
                v_acc_2613_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_2622_;
        }
        _ => {
            let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_2614_);
            crate::leanh::lean_dec(v___y_2612_);
            crate::leanh::lean_dec(v_recur_2611_);
            v___x_2623_ =
                crate::leanh::lean_apply_2(v_toPure_2610_, crate::leanh::lean_box(0), v_acc_2613_);
            return v___x_2623_;
        }
    }
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(
    mut v_toPure_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v_toBind_2626_: *mut crate::leanh::LeanObject,
    mut v_inst_2627_: *mut crate::leanh::LeanObject,
    mut v_lift_2628_: *mut crate::leanh::LeanObject,
    mut v_it_2629_: *mut crate::leanh::LeanObject,
    mut v_acc_2630_: *mut crate::leanh::LeanObject,
    mut v_hP_2631_: *mut crate::leanh::LeanObject,
    mut v_recur_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2633_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2633_, 0, v_toPure_2624_);
    crate::leanh::lean_closure_set(v___f_2633_, 1, v_recur_2632_);
    crate::leanh::lean_closure_set(v___f_2633_, 2, v___y_2625_);
    crate::leanh::lean_closure_set(v___f_2633_, 3, v_acc_2630_);
    crate::leanh::lean_closure_set(v___f_2633_, 4, v_toBind_2626_);
    v___x_2634_ = crate::leanh::lean_apply_1(v_inst_2627_, v_it_2629_);
    v___x_2635_ = crate::leanh::lean_apply_4(
        v_lift_2628_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2633_,
        v___x_2634_,
    );
    return v___x_2635_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(
    mut v_inst_2636_: *mut crate::leanh::LeanObject,
    mut v_inst_2637_: *mut crate::leanh::LeanObject,
    mut v_lift_2638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2639_: *mut crate::leanh::LeanObject,
    mut v_Pl_2640_: *mut crate::leanh::LeanObject,
    mut v_it_2641_: *mut crate::leanh::LeanObject,
    mut v_init_2642_: *mut crate::leanh::LeanObject,
    mut v___y_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2644_ = crate::leanh::lean_ctor_get(v_inst_2636_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2644_);
    v_toBind_2645_ = crate::leanh::lean_ctor_get(v_inst_2636_, 1);
    crate::leanh::lean_inc(v_toBind_2645_);
    crate::leanh::lean_dec_ref(v_inst_2636_);
    v_toPure_2646_ = crate::leanh::lean_ctor_get(v_toApplicative_2644_, 1);
    crate::leanh::lean_inc(v_toPure_2646_);
    crate::leanh::lean_dec_ref(v_toApplicative_2644_);
    v___f_2647_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__0 as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2647_, 0, v_toPure_2646_);
    crate::leanh::lean_closure_set(v___f_2647_, 1, v___y_2643_);
    crate::leanh::lean_closure_set(v___f_2647_, 2, v_toBind_2645_);
    crate::leanh::lean_closure_set(v___f_2647_, 3, v_inst_2637_);
    crate::leanh::lean_closure_set(v___f_2647_, 4, v_lift_2638_);
    v___x_2648_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2647_,
        v_it_2641_,
        v_init_2642_,
        crate::leanh::lean_box(0),
    );
    return v___x_2648_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg(
    mut v_inst_2649_: *mut crate::leanh::LeanObject,
    mut v_inst_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2651_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2651_, 0, v_inst_2649_);
    crate::leanh::lean_closure_set(v___f_2651_, 1, v_inst_2650_);
    return v___f_2651_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation(
    mut v_00_u03b2_2652_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2653_: *mut crate::leanh::LeanObject,
    mut v_m_2654_: *mut crate::leanh::LeanObject,
    mut v_n_2655_: *mut crate::leanh::LeanObject,
    mut v_inst_2656_: *mut crate::leanh::LeanObject,
    mut v_inst_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2658_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2658_, 0, v_inst_2656_);
    crate::leanh::lean_closure_set(v___f_2658_, 1, v_inst_2657_);
    return v___f_2658_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(
    mut v_toPure_2659_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = crate::leanh::lean_apply_2(
        v_toPure_2659_,
        crate::leanh::lean_box(0),
        v_____do__lift_2660_,
    );
    return v___x_2661_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(
    mut v_f_2662_: *mut crate::leanh::LeanObject,
    mut v_toBind_2663_: *mut crate::leanh::LeanObject,
    mut v___f_2664_: *mut crate::leanh::LeanObject,
    mut v_x1_2665_: *mut crate::leanh::LeanObject,
    mut v_x2_2666_: *mut crate::leanh::LeanObject,
    mut v_x3_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ =
        crate::leanh::lean_apply_3(v_f_2662_, v_x1_2665_, crate::leanh::lean_box(0), v_x3_2667_);
    v___x_2669_ = crate::leanh::lean_apply_4(
        v_toBind_2663_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2668_,
        v___f_2664_,
    );
    return v___x_2669_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(
    mut v_toBind_2670_: *mut crate::leanh::LeanObject,
    mut v___f_2671_: *mut crate::leanh::LeanObject,
    mut v_inst_2672_: *mut crate::leanh::LeanObject,
    mut v_lift_2673_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2674_: *mut crate::leanh::LeanObject,
    mut v_it_2675_: *mut crate::leanh::LeanObject,
    mut v_init_2676_: *mut crate::leanh::LeanObject,
    mut v_f_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2678_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2678_, 0, v_f_2677_);
    crate::leanh::lean_closure_set(v___f_2678_, 1, v_toBind_2670_);
    crate::leanh::lean_closure_set(v___f_2678_, 2, v___f_2671_);
    v___x_2679_ = crate::leanh::lean_apply_6(
        v_inst_2672_,
        v_lift_2673_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_2675_,
        v_init_2676_,
        v___f_2678_,
    );
    return v___x_2679_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg(
    mut v_inst_2680_: *mut crate::leanh::LeanObject,
    mut v_inst_2681_: *mut crate::leanh::LeanObject,
    mut v_lift_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2683_ = crate::leanh::lean_ctor_get(v_inst_2681_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2683_);
    v_toBind_2684_ = crate::leanh::lean_ctor_get(v_inst_2681_, 1);
    crate::leanh::lean_inc(v_toBind_2684_);
    crate::leanh::lean_dec_ref(v_inst_2681_);
    v_toPure_2685_ = crate::leanh::lean_ctor_get(v_toApplicative_2683_, 1);
    crate::leanh::lean_inc(v_toPure_2685_);
    crate::leanh::lean_dec_ref(v_toApplicative_2683_);
    v___f_2686_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2686_, 0, v_toPure_2685_);
    v___f_2687_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2687_, 0, v_toBind_2684_);
    crate::leanh::lean_closure_set(v___f_2687_, 1, v___f_2686_);
    crate::leanh::lean_closure_set(v___f_2687_, 2, v_inst_2680_);
    crate::leanh::lean_closure_set(v___f_2687_, 3, v_lift_2682_);
    return v___f_2687_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27(
    mut v_m_2688_: *mut crate::leanh::LeanObject,
    mut v_n_2689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2690_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2691_: *mut crate::leanh::LeanObject,
    mut v_inst_2692_: *mut crate::leanh::LeanObject,
    mut v_inst_2693_: *mut crate::leanh::LeanObject,
    mut v_inst_2694_: *mut crate::leanh::LeanObject,
    mut v_lift_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2696_ = crate::leanh::lean_ctor_get(v_inst_2694_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2696_);
    v_toBind_2697_ = crate::leanh::lean_ctor_get(v_inst_2694_, 1);
    crate::leanh::lean_inc(v_toBind_2697_);
    crate::leanh::lean_dec_ref(v_inst_2694_);
    v_toPure_2698_ = crate::leanh::lean_ctor_get(v_toApplicative_2696_, 1);
    crate::leanh::lean_inc(v_toPure_2698_);
    crate::leanh::lean_dec_ref(v_toApplicative_2696_);
    v___f_2699_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2699_, 0, v_toPure_2698_);
    v___f_2700_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2700_, 0, v_toBind_2697_);
    crate::leanh::lean_closure_set(v___f_2700_, 1, v___f_2699_);
    crate::leanh::lean_closure_set(v___f_2700_, 2, v_inst_2693_);
    crate::leanh::lean_closure_set(v___f_2700_, 3, v_lift_2695_);
    return v___f_2700_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___boxed(
    mut v_m_2701_: *mut crate::leanh::LeanObject,
    mut v_n_2702_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2703_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2704_: *mut crate::leanh::LeanObject,
    mut v_inst_2705_: *mut crate::leanh::LeanObject,
    mut v_inst_2706_: *mut crate::leanh::LeanObject,
    mut v_inst_2707_: *mut crate::leanh::LeanObject,
    mut v_lift_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2709_ = l_Std_IteratorLoop_finiteForIn_x27(
        v_m_2701_,
        v_n_2702_,
        v_00_u03b1_2703_,
        v_00_u03b2_2704_,
        v_inst_2705_,
        v_inst_2706_,
        v_inst_2707_,
        v_lift_2708_,
    );
    crate::leanh::lean_dec(v_inst_2705_);
    return v_res_2709_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg___lam__0(
    mut v_inst_2710_: *mut crate::leanh::LeanObject,
    mut v_toBind_2711_: *mut crate::leanh::LeanObject,
    mut v_x_2712_: *mut crate::leanh::LeanObject,
    mut v_x_2713_: *mut crate::leanh::LeanObject,
    mut v_f_2714_: *mut crate::leanh::LeanObject,
    mut v_x_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = crate::leanh::lean_apply_2(v_inst_2710_, crate::leanh::lean_box(0), v_x_2715_);
    v___x_2717_ = crate::leanh::lean_apply_4(
        v_toBind_2711_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2716_,
        v_f_2714_,
    );
    return v___x_2717_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg___lam__3(
    mut v_toBind_2718_: *mut crate::leanh::LeanObject,
    mut v___f_2719_: *mut crate::leanh::LeanObject,
    mut v_inst_2720_: *mut crate::leanh::LeanObject,
    mut v___f_2721_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2722_: *mut crate::leanh::LeanObject,
    mut v_it_2723_: *mut crate::leanh::LeanObject,
    mut v_init_2724_: *mut crate::leanh::LeanObject,
    mut v_f_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2726_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2726_, 0, v_f_2725_);
    crate::leanh::lean_closure_set(v___f_2726_, 1, v_toBind_2718_);
    crate::leanh::lean_closure_set(v___f_2726_, 2, v___f_2719_);
    v___x_2727_ = crate::leanh::lean_apply_6(
        v_inst_2720_,
        v___f_2721_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_2723_,
        v_init_2724_,
        v___f_2726_,
    );
    return v___x_2727_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg(
    mut v_inst_2728_: *mut crate::leanh::LeanObject,
    mut v_inst_2729_: *mut crate::leanh::LeanObject,
    mut v_inst_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2731_ = crate::leanh::lean_ctor_get(v_inst_2729_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2731_);
    v_toBind_2732_ = crate::leanh::lean_ctor_get(v_inst_2729_, 1);
    crate::leanh::lean_inc_n(v_toBind_2732_, 2);
    crate::leanh::lean_dec_ref(v_inst_2729_);
    v_toPure_2733_ = crate::leanh::lean_ctor_get(v_toApplicative_2731_, 1);
    crate::leanh::lean_inc(v_toPure_2733_);
    crate::leanh::lean_dec_ref(v_toApplicative_2731_);
    v___f_2734_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2734_, 0, v_inst_2730_);
    crate::leanh::lean_closure_set(v___f_2734_, 1, v_toBind_2732_);
    v___f_2735_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2735_, 0, v_toPure_2733_);
    v___f_2736_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2736_, 0, v_toBind_2732_);
    crate::leanh::lean_closure_set(v___f_2736_, 1, v___f_2735_);
    crate::leanh::lean_closure_set(v___f_2736_, 2, v_inst_2728_);
    crate::leanh::lean_closure_set(v___f_2736_, 3, v___f_2734_);
    return v___f_2736_;
}
pub unsafe fn l_Std_IterM_instForIn_x27(
    mut v_m_2737_: *mut crate::leanh::LeanObject,
    mut v_n_2738_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2740_: *mut crate::leanh::LeanObject,
    mut v_inst_2741_: *mut crate::leanh::LeanObject,
    mut v_inst_2742_: *mut crate::leanh::LeanObject,
    mut v_inst_2743_: *mut crate::leanh::LeanObject,
    mut v_inst_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2745_ = crate::leanh::lean_ctor_get(v_inst_2743_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2745_);
    v_toBind_2746_ = crate::leanh::lean_ctor_get(v_inst_2743_, 1);
    crate::leanh::lean_inc_n(v_toBind_2746_, 2);
    crate::leanh::lean_dec_ref(v_inst_2743_);
    v_toPure_2747_ = crate::leanh::lean_ctor_get(v_toApplicative_2745_, 1);
    crate::leanh::lean_inc(v_toPure_2747_);
    crate::leanh::lean_dec_ref(v_toApplicative_2745_);
    v___f_2748_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2748_, 0, v_inst_2744_);
    crate::leanh::lean_closure_set(v___f_2748_, 1, v_toBind_2746_);
    v___f_2749_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2749_, 0, v_toPure_2747_);
    v___f_2750_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2750_, 0, v_toBind_2746_);
    crate::leanh::lean_closure_set(v___f_2750_, 1, v___f_2749_);
    crate::leanh::lean_closure_set(v___f_2750_, 2, v_inst_2742_);
    crate::leanh::lean_closure_set(v___f_2750_, 3, v___f_2748_);
    return v___f_2750_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___boxed(
    mut v_m_2751_: *mut crate::leanh::LeanObject,
    mut v_n_2752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2753_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2754_: *mut crate::leanh::LeanObject,
    mut v_inst_2755_: *mut crate::leanh::LeanObject,
    mut v_inst_2756_: *mut crate::leanh::LeanObject,
    mut v_inst_2757_: *mut crate::leanh::LeanObject,
    mut v_inst_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Std_IterM_instForIn_x27(
        v_m_2751_,
        v_n_2752_,
        v_00_u03b1_2753_,
        v_00_u03b2_2754_,
        v_inst_2755_,
        v_inst_2756_,
        v_inst_2757_,
        v_inst_2758_,
    );
    crate::leanh::lean_dec(v_inst_2755_);
    return v_res_2759_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop___redArg(
    mut v_inst_2760_: *mut crate::leanh::LeanObject,
    mut v_inst_2761_: *mut crate::leanh::LeanObject,
    mut v_inst_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2763_ = crate::leanh::lean_ctor_get(v_inst_2762_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2763_);
    v_toBind_2764_ = crate::leanh::lean_ctor_get(v_inst_2762_, 1);
    crate::leanh::lean_inc_n(v_toBind_2764_, 2);
    crate::leanh::lean_dec_ref(v_inst_2762_);
    v_toPure_2765_ = crate::leanh::lean_ctor_get(v_toApplicative_2763_, 1);
    crate::leanh::lean_inc(v_toPure_2765_);
    crate::leanh::lean_dec_ref(v_toApplicative_2763_);
    v___f_2766_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2766_, 0, v_inst_2761_);
    crate::leanh::lean_closure_set(v___f_2766_, 1, v_toBind_2764_);
    v___f_2767_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2767_, 0, v_toPure_2765_);
    v___f_2768_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2768_, 0, v_toBind_2764_);
    crate::leanh::lean_closure_set(v___f_2768_, 1, v___f_2767_);
    crate::leanh::lean_closure_set(v___f_2768_, 2, v_inst_2760_);
    crate::leanh::lean_closure_set(v___f_2768_, 3, v___f_2766_);
    v___f_2769_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2769_, 0, v___f_2768_);
    return v___f_2769_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop(
    mut v_m_2770_: *mut crate::leanh::LeanObject,
    mut v_n_2771_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2772_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2773_: *mut crate::leanh::LeanObject,
    mut v_inst_2774_: *mut crate::leanh::LeanObject,
    mut v_inst_2775_: *mut crate::leanh::LeanObject,
    mut v_inst_2776_: *mut crate::leanh::LeanObject,
    mut v_inst_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ =
        l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_2775_, v_inst_2776_, v_inst_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop___boxed(
    mut v_m_2779_: *mut crate::leanh::LeanObject,
    mut v_n_2780_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2781_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2782_: *mut crate::leanh::LeanObject,
    mut v_inst_2783_: *mut crate::leanh::LeanObject,
    mut v_inst_2784_: *mut crate::leanh::LeanObject,
    mut v_inst_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Std_IterM_instForInOfIteratorLoop(
        v_m_2779_,
        v_n_2780_,
        v_00_u03b1_2781_,
        v_00_u03b2_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_inst_2785_,
        v_inst_2786_,
    );
    crate::leanh::lean_dec(v_inst_2783_);
    return v_res_2787_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(
    mut v_toBind_2788_: *mut crate::leanh::LeanObject,
    mut v___f_2789_: *mut crate::leanh::LeanObject,
    mut v_inst_2790_: *mut crate::leanh::LeanObject,
    mut v___f_2791_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2792_: *mut crate::leanh::LeanObject,
    mut v_it_2793_: *mut crate::leanh::LeanObject,
    mut v_init_2794_: *mut crate::leanh::LeanObject,
    mut v_f_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2796_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2796_, 0, v_f_2795_);
    crate::leanh::lean_closure_set(v___f_2796_, 1, v_toBind_2788_);
    crate::leanh::lean_closure_set(v___f_2796_, 2, v___f_2789_);
    v___x_2797_ = crate::leanh::lean_apply_6(
        v_inst_2790_,
        v___f_2791_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_2793_,
        v_init_2794_,
        v___f_2796_,
    );
    return v___x_2797_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___redArg(
    mut v_inst_2798_: *mut crate::leanh::LeanObject,
    mut v_inst_2799_: *mut crate::leanh::LeanObject,
    mut v_inst_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2801_ = crate::leanh::lean_ctor_get(v_inst_2800_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2801_);
    v_toBind_2802_ = crate::leanh::lean_ctor_get(v_inst_2800_, 1);
    crate::leanh::lean_inc_n(v_toBind_2802_, 2);
    crate::leanh::lean_dec_ref(v_inst_2800_);
    v_toPure_2803_ = crate::leanh::lean_ctor_get(v_toApplicative_2801_, 1);
    crate::leanh::lean_inc(v_toPure_2803_);
    crate::leanh::lean_dec_ref(v_toApplicative_2801_);
    v___f_2804_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2804_, 0, v_inst_2799_);
    crate::leanh::lean_closure_set(v___f_2804_, 1, v_toBind_2802_);
    v___f_2805_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2805_, 0, v_toPure_2803_);
    v___f_2806_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2806_, 0, v_toBind_2802_);
    crate::leanh::lean_closure_set(v___f_2806_, 1, v___f_2805_);
    crate::leanh::lean_closure_set(v___f_2806_, 2, v_inst_2798_);
    crate::leanh::lean_closure_set(v___f_2806_, 3, v___f_2804_);
    return v___f_2806_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27(
    mut v_m_2807_: *mut crate::leanh::LeanObject,
    mut v_n_2808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2809_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2810_: *mut crate::leanh::LeanObject,
    mut v_inst_2811_: *mut crate::leanh::LeanObject,
    mut v_inst_2812_: *mut crate::leanh::LeanObject,
    mut v_inst_2813_: *mut crate::leanh::LeanObject,
    mut v_inst_2814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2815_ = crate::leanh::lean_ctor_get(v_inst_2814_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2815_);
    v_toBind_2816_ = crate::leanh::lean_ctor_get(v_inst_2814_, 1);
    crate::leanh::lean_inc_n(v_toBind_2816_, 2);
    crate::leanh::lean_dec_ref(v_inst_2814_);
    v_toPure_2817_ = crate::leanh::lean_ctor_get(v_toApplicative_2815_, 1);
    crate::leanh::lean_inc(v_toPure_2817_);
    crate::leanh::lean_dec_ref(v_toApplicative_2815_);
    v___f_2818_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2818_, 0, v_inst_2813_);
    crate::leanh::lean_closure_set(v___f_2818_, 1, v_toBind_2816_);
    v___f_2819_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2819_, 0, v_toPure_2817_);
    v___f_2820_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2820_, 0, v_toBind_2816_);
    crate::leanh::lean_closure_set(v___f_2820_, 1, v___f_2819_);
    crate::leanh::lean_closure_set(v___f_2820_, 2, v_inst_2812_);
    crate::leanh::lean_closure_set(v___f_2820_, 3, v___f_2818_);
    return v___f_2820_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___boxed(
    mut v_m_2821_: *mut crate::leanh::LeanObject,
    mut v_n_2822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2824_: *mut crate::leanh::LeanObject,
    mut v_inst_2825_: *mut crate::leanh::LeanObject,
    mut v_inst_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_inst_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Std_IterM_Partial_instForIn_x27(
        v_m_2821_,
        v_n_2822_,
        v_00_u03b1_2823_,
        v_00_u03b2_2824_,
        v_inst_2825_,
        v_inst_2826_,
        v_inst_2827_,
        v_inst_2828_,
    );
    crate::leanh::lean_dec(v_inst_2825_);
    return v_res_2829_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27___redArg(
    mut v_inst_2830_: *mut crate::leanh::LeanObject,
    mut v_inst_2831_: *mut crate::leanh::LeanObject,
    mut v_inst_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2833_ = crate::leanh::lean_ctor_get(v_inst_2832_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2833_);
    v_toBind_2834_ = crate::leanh::lean_ctor_get(v_inst_2832_, 1);
    crate::leanh::lean_inc_n(v_toBind_2834_, 2);
    crate::leanh::lean_dec_ref(v_inst_2832_);
    v_toPure_2835_ = crate::leanh::lean_ctor_get(v_toApplicative_2833_, 1);
    crate::leanh::lean_inc(v_toPure_2835_);
    crate::leanh::lean_dec_ref(v_toApplicative_2833_);
    v___f_2836_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2836_, 0, v_inst_2831_);
    crate::leanh::lean_closure_set(v___f_2836_, 1, v_toBind_2834_);
    v___f_2837_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2837_, 0, v_toPure_2835_);
    v___f_2838_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2838_, 0, v_toBind_2834_);
    crate::leanh::lean_closure_set(v___f_2838_, 1, v___f_2837_);
    crate::leanh::lean_closure_set(v___f_2838_, 2, v_inst_2830_);
    crate::leanh::lean_closure_set(v___f_2838_, 3, v___f_2836_);
    return v___f_2838_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27(
    mut v_m_2839_: *mut crate::leanh::LeanObject,
    mut v_n_2840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2841_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2842_: *mut crate::leanh::LeanObject,
    mut v_inst_2843_: *mut crate::leanh::LeanObject,
    mut v_inst_2844_: *mut crate::leanh::LeanObject,
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
    mut v_inst_2846_: *mut crate::leanh::LeanObject,
    mut v_inst_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2848_ = crate::leanh::lean_ctor_get(v_inst_2846_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2848_);
    v_toBind_2849_ = crate::leanh::lean_ctor_get(v_inst_2846_, 1);
    crate::leanh::lean_inc_n(v_toBind_2849_, 2);
    crate::leanh::lean_dec_ref(v_inst_2846_);
    v_toPure_2850_ = crate::leanh::lean_ctor_get(v_toApplicative_2848_, 1);
    crate::leanh::lean_inc(v_toPure_2850_);
    crate::leanh::lean_dec_ref(v_toApplicative_2848_);
    v___f_2851_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2851_, 0, v_inst_2845_);
    crate::leanh::lean_closure_set(v___f_2851_, 1, v_toBind_2849_);
    v___f_2852_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2852_, 0, v_toPure_2850_);
    v___f_2853_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2853_, 0, v_toBind_2849_);
    crate::leanh::lean_closure_set(v___f_2853_, 1, v___f_2852_);
    crate::leanh::lean_closure_set(v___f_2853_, 2, v_inst_2844_);
    crate::leanh::lean_closure_set(v___f_2853_, 3, v___f_2851_);
    return v___f_2853_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27___boxed(
    mut v_m_2854_: *mut crate::leanh::LeanObject,
    mut v_n_2855_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2856_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2857_: *mut crate::leanh::LeanObject,
    mut v_inst_2858_: *mut crate::leanh::LeanObject,
    mut v_inst_2859_: *mut crate::leanh::LeanObject,
    mut v_inst_2860_: *mut crate::leanh::LeanObject,
    mut v_inst_2861_: *mut crate::leanh::LeanObject,
    mut v_inst_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Std_IterM_Total_instForIn_x27(
        v_m_2854_,
        v_n_2855_,
        v_00_u03b1_2856_,
        v_00_u03b2_2857_,
        v_inst_2858_,
        v_inst_2859_,
        v_inst_2860_,
        v_inst_2861_,
        v_inst_2862_,
    );
    crate::leanh::lean_dec(v_inst_2858_);
    return v_res_2863_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(
    mut v_inst_2864_: *mut crate::leanh::LeanObject,
    mut v_inst_2865_: *mut crate::leanh::LeanObject,
    mut v_inst_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2867_ = crate::leanh::lean_ctor_get(v_inst_2866_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2867_);
    v_toBind_2868_ = crate::leanh::lean_ctor_get(v_inst_2866_, 1);
    crate::leanh::lean_inc_n(v_toBind_2868_, 2);
    crate::leanh::lean_dec_ref(v_inst_2866_);
    v_toPure_2869_ = crate::leanh::lean_ctor_get(v_toApplicative_2867_, 1);
    crate::leanh::lean_inc(v_toPure_2869_);
    crate::leanh::lean_dec_ref(v_toApplicative_2867_);
    v___f_2870_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2870_, 0, v_inst_2865_);
    crate::leanh::lean_closure_set(v___f_2870_, 1, v_toBind_2868_);
    v___f_2871_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2871_, 0, v_toPure_2869_);
    v___f_2872_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2872_, 0, v_toBind_2868_);
    crate::leanh::lean_closure_set(v___f_2872_, 1, v___f_2871_);
    crate::leanh::lean_closure_set(v___f_2872_, 2, v_inst_2864_);
    crate::leanh::lean_closure_set(v___f_2872_, 3, v___f_2870_);
    v___f_2873_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2873_, 0, v___f_2872_);
    return v___f_2873_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop(
    mut v_m_2874_: *mut crate::leanh::LeanObject,
    mut v_n_2875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2876_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2877_: *mut crate::leanh::LeanObject,
    mut v_inst_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
    mut v_inst_2880_: *mut crate::leanh::LeanObject,
    mut v_inst_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(
        v_inst_2879_,
        v_inst_2880_,
        v_inst_2881_,
    );
    return v___x_2882_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(
    mut v_m_2883_: *mut crate::leanh::LeanObject,
    mut v_n_2884_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2885_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2886_: *mut crate::leanh::LeanObject,
    mut v_inst_2887_: *mut crate::leanh::LeanObject,
    mut v_inst_2888_: *mut crate::leanh::LeanObject,
    mut v_inst_2889_: *mut crate::leanh::LeanObject,
    mut v_inst_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Std_IterM_Partial_instForInOfIteratorLoop(
        v_m_2883_,
        v_n_2884_,
        v_00_u03b1_2885_,
        v_00_u03b2_2886_,
        v_inst_2887_,
        v_inst_2888_,
        v_inst_2889_,
        v_inst_2890_,
    );
    crate::leanh::lean_dec(v_inst_2887_);
    return v_res_2891_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(
    mut v_inst_2892_: *mut crate::leanh::LeanObject,
    mut v_inst_2893_: *mut crate::leanh::LeanObject,
    mut v_inst_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2895_ = crate::leanh::lean_ctor_get(v_inst_2894_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2895_);
    v_toBind_2896_ = crate::leanh::lean_ctor_get(v_inst_2894_, 1);
    crate::leanh::lean_inc_n(v_toBind_2896_, 2);
    crate::leanh::lean_dec_ref(v_inst_2894_);
    v_toPure_2897_ = crate::leanh::lean_ctor_get(v_toApplicative_2895_, 1);
    crate::leanh::lean_inc(v_toPure_2897_);
    crate::leanh::lean_dec_ref(v_toApplicative_2895_);
    v___f_2898_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2898_, 0, v_inst_2893_);
    crate::leanh::lean_closure_set(v___f_2898_, 1, v_toBind_2896_);
    v___f_2899_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2899_, 0, v_toPure_2897_);
    v___f_2900_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2900_, 0, v_toBind_2896_);
    crate::leanh::lean_closure_set(v___f_2900_, 1, v___f_2899_);
    crate::leanh::lean_closure_set(v___f_2900_, 2, v_inst_2892_);
    crate::leanh::lean_closure_set(v___f_2900_, 3, v___f_2898_);
    v___f_2901_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2901_, 0, v___f_2900_);
    return v___f_2901_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(
    mut v_m_2902_: *mut crate::leanh::LeanObject,
    mut v_n_2903_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2904_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2905_: *mut crate::leanh::LeanObject,
    mut v_inst_2906_: *mut crate::leanh::LeanObject,
    mut v_inst_2907_: *mut crate::leanh::LeanObject,
    mut v_inst_2908_: *mut crate::leanh::LeanObject,
    mut v_inst_2909_: *mut crate::leanh::LeanObject,
    mut v_inst_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2911_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(
        v_inst_2907_,
        v_inst_2908_,
        v_inst_2909_,
    );
    return v___x_2911_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(
    mut v_m_2912_: *mut crate::leanh::LeanObject,
    mut v_n_2913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2914_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2915_: *mut crate::leanh::LeanObject,
    mut v_inst_2916_: *mut crate::leanh::LeanObject,
    mut v_inst_2917_: *mut crate::leanh::LeanObject,
    mut v_inst_2918_: *mut crate::leanh::LeanObject,
    mut v_inst_2919_: *mut crate::leanh::LeanObject,
    mut v_inst_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(
        v_m_2912_,
        v_n_2913_,
        v_00_u03b1_2914_,
        v_00_u03b2_2915_,
        v_inst_2916_,
        v_inst_2917_,
        v_inst_2918_,
        v_inst_2919_,
        v_inst_2920_,
    );
    crate::leanh::lean_dec(v_inst_2916_);
    return v_res_2921_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(
    mut v_toPure_2922_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = crate::leanh::lean_apply_2(
        v_toPure_2922_,
        crate::leanh::lean_box(0),
        v_____do__lift_2923_,
    );
    return v___x_2924_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(
    mut v___x_2925_: *mut crate::leanh::LeanObject,
    mut v_toPure_2926_: *mut crate::leanh::LeanObject,
    mut v_____r_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2928_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2928_, 0, v___x_2925_);
    v___x_2929_ =
        crate::leanh::lean_apply_2(v_toPure_2926_, crate::leanh::lean_box(0), v___x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(
    mut v_f_2930_: *mut crate::leanh::LeanObject,
    mut v_toBind_2931_: *mut crate::leanh::LeanObject,
    mut v___f_2932_: *mut crate::leanh::LeanObject,
    mut v___f_2933_: *mut crate::leanh::LeanObject,
    mut v_x1_2934_: *mut crate::leanh::LeanObject,
    mut v_x2_2935_: *mut crate::leanh::LeanObject,
    mut v_x3_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = crate::leanh::lean_apply_1(v_f_2930_, v_x1_2934_);
    crate::leanh::lean_inc(v_toBind_2931_);
    v___x_2938_ = crate::leanh::lean_apply_4(
        v_toBind_2931_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2937_,
        v___f_2932_,
    );
    v___x_2939_ = crate::leanh::lean_apply_4(
        v_toBind_2931_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2938_,
        v___f_2933_,
    );
    return v___x_2939_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(
    mut v_toPure_2940_: *mut crate::leanh::LeanObject,
    mut v_toBind_2941_: *mut crate::leanh::LeanObject,
    mut v___f_2942_: *mut crate::leanh::LeanObject,
    mut v_inst_2943_: *mut crate::leanh::LeanObject,
    mut v___f_2944_: *mut crate::leanh::LeanObject,
    mut v_it_2945_: *mut crate::leanh::LeanObject,
    mut v_f_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = crate::leanh::lean_box(0);
    v___f_2948_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2948_, 0, v___x_2947_);
    crate::leanh::lean_closure_set(v___f_2948_, 1, v_toPure_2940_);
    v___f_2949_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2949_, 0, v_f_2946_);
    crate::leanh::lean_closure_set(v___f_2949_, 1, v_toBind_2941_);
    crate::leanh::lean_closure_set(v___f_2949_, 2, v___f_2948_);
    crate::leanh::lean_closure_set(v___f_2949_, 3, v___f_2942_);
    v___x_2950_ = crate::leanh::lean_apply_6(
        v_inst_2943_,
        v___f_2944_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_2945_,
        v___x_2947_,
        v___f_2949_,
    );
    return v___x_2950_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg(
    mut v_inst_2951_: *mut crate::leanh::LeanObject,
    mut v_inst_2952_: *mut crate::leanh::LeanObject,
    mut v_inst_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2954_ = crate::leanh::lean_ctor_get(v_inst_2952_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2954_);
    v_toBind_2955_ = crate::leanh::lean_ctor_get(v_inst_2952_, 1);
    crate::leanh::lean_inc_n(v_toBind_2955_, 2);
    crate::leanh::lean_dec_ref(v_inst_2952_);
    v_toPure_2956_ = crate::leanh::lean_ctor_get(v_toApplicative_2954_, 1);
    crate::leanh::lean_inc_n(v_toPure_2956_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2954_);
    v___f_2957_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2957_, 0, v_inst_2953_);
    crate::leanh::lean_closure_set(v___f_2957_, 1, v_toBind_2955_);
    v___f_2958_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2958_, 0, v_toPure_2956_);
    v___f_2959_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2959_, 0, v_toPure_2956_);
    crate::leanh::lean_closure_set(v___f_2959_, 1, v_toBind_2955_);
    crate::leanh::lean_closure_set(v___f_2959_, 2, v___f_2958_);
    crate::leanh::lean_closure_set(v___f_2959_, 3, v_inst_2951_);
    crate::leanh::lean_closure_set(v___f_2959_, 4, v___f_2957_);
    return v___f_2959_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop(
    mut v_m_2960_: *mut crate::leanh::LeanObject,
    mut v_n_2961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2963_: *mut crate::leanh::LeanObject,
    mut v_inst_2964_: *mut crate::leanh::LeanObject,
    mut v_inst_2965_: *mut crate::leanh::LeanObject,
    mut v_inst_2966_: *mut crate::leanh::LeanObject,
    mut v_inst_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ =
        l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_2965_, v_inst_2966_, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___boxed(
    mut v_m_2969_: *mut crate::leanh::LeanObject,
    mut v_n_2970_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2971_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2972_: *mut crate::leanh::LeanObject,
    mut v_inst_2973_: *mut crate::leanh::LeanObject,
    mut v_inst_2974_: *mut crate::leanh::LeanObject,
    mut v_inst_2975_: *mut crate::leanh::LeanObject,
    mut v_inst_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Std_IterM_instForMOfIteratorLoop(
        v_m_2969_,
        v_n_2970_,
        v_00_u03b1_2971_,
        v_00_u03b2_2972_,
        v_inst_2973_,
        v_inst_2974_,
        v_inst_2975_,
        v_inst_2976_,
    );
    crate::leanh::lean_dec(v_inst_2973_);
    return v_res_2977_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(
    mut v_inst_2978_: *mut crate::leanh::LeanObject,
    mut v_inst_2979_: *mut crate::leanh::LeanObject,
    mut v_inst_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2981_ = crate::leanh::lean_ctor_get(v_inst_2978_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2981_);
    v_toBind_2982_ = crate::leanh::lean_ctor_get(v_inst_2978_, 1);
    crate::leanh::lean_inc_n(v_toBind_2982_, 2);
    crate::leanh::lean_dec_ref(v_inst_2978_);
    v_toPure_2983_ = crate::leanh::lean_ctor_get(v_toApplicative_2981_, 1);
    crate::leanh::lean_inc_n(v_toPure_2983_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2981_);
    v___f_2984_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2984_, 0, v_inst_2980_);
    crate::leanh::lean_closure_set(v___f_2984_, 1, v_toBind_2982_);
    v___f_2985_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2985_, 0, v_toPure_2983_);
    v___f_2986_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2986_, 0, v_toPure_2983_);
    crate::leanh::lean_closure_set(v___f_2986_, 1, v_toBind_2982_);
    crate::leanh::lean_closure_set(v___f_2986_, 2, v___f_2985_);
    crate::leanh::lean_closure_set(v___f_2986_, 3, v_inst_2979_);
    crate::leanh::lean_closure_set(v___f_2986_, 4, v___f_2984_);
    return v___f_2986_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop(
    mut v_m_2987_: *mut crate::leanh::LeanObject,
    mut v_n_2988_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2989_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2990_: *mut crate::leanh::LeanObject,
    mut v_inst_2991_: *mut crate::leanh::LeanObject,
    mut v_inst_2992_: *mut crate::leanh::LeanObject,
    mut v_inst_2993_: *mut crate::leanh::LeanObject,
    mut v_inst_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(
        v_inst_2991_,
        v_inst_2993_,
        v_inst_2994_,
    );
    return v___x_2995_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(
    mut v_m_2996_: *mut crate::leanh::LeanObject,
    mut v_n_2997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2998_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2999_: *mut crate::leanh::LeanObject,
    mut v_inst_3000_: *mut crate::leanh::LeanObject,
    mut v_inst_3001_: *mut crate::leanh::LeanObject,
    mut v_inst_3002_: *mut crate::leanh::LeanObject,
    mut v_inst_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3004_ = l_Std_IterM_Partial_instForMOfItreratorLoop(
        v_m_2996_,
        v_n_2997_,
        v_00_u03b1_2998_,
        v_00_u03b2_2999_,
        v_inst_3000_,
        v_inst_3001_,
        v_inst_3002_,
        v_inst_3003_,
    );
    crate::leanh::lean_dec(v_inst_3001_);
    return v_res_3004_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(
    mut v_inst_3005_: *mut crate::leanh::LeanObject,
    mut v_inst_3006_: *mut crate::leanh::LeanObject,
    mut v_inst_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3008_ = crate::leanh::lean_ctor_get(v_inst_3006_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3008_);
    v_toBind_3009_ = crate::leanh::lean_ctor_get(v_inst_3006_, 1);
    crate::leanh::lean_inc_n(v_toBind_3009_, 2);
    crate::leanh::lean_dec_ref(v_inst_3006_);
    v_toPure_3010_ = crate::leanh::lean_ctor_get(v_toApplicative_3008_, 1);
    crate::leanh::lean_inc_n(v_toPure_3010_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3008_);
    v___f_3011_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3011_, 0, v_inst_3007_);
    crate::leanh::lean_closure_set(v___f_3011_, 1, v_toBind_3009_);
    v___f_3012_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3012_, 0, v_toPure_3010_);
    v___f_3013_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3013_, 0, v_toPure_3010_);
    crate::leanh::lean_closure_set(v___f_3013_, 1, v_toBind_3009_);
    crate::leanh::lean_closure_set(v___f_3013_, 2, v___f_3012_);
    crate::leanh::lean_closure_set(v___f_3013_, 3, v_inst_3005_);
    crate::leanh::lean_closure_set(v___f_3013_, 4, v___f_3011_);
    return v___f_3013_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(
    mut v_m_3014_: *mut crate::leanh::LeanObject,
    mut v_n_3015_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3016_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3017_: *mut crate::leanh::LeanObject,
    mut v_inst_3018_: *mut crate::leanh::LeanObject,
    mut v_inst_3019_: *mut crate::leanh::LeanObject,
    mut v_inst_3020_: *mut crate::leanh::LeanObject,
    mut v_inst_3021_: *mut crate::leanh::LeanObject,
    mut v_inst_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3023_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(
        v_inst_3019_,
        v_inst_3020_,
        v_inst_3021_,
    );
    return v___x_3023_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(
    mut v_m_3024_: *mut crate::leanh::LeanObject,
    mut v_n_3025_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3026_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3027_: *mut crate::leanh::LeanObject,
    mut v_inst_3028_: *mut crate::leanh::LeanObject,
    mut v_inst_3029_: *mut crate::leanh::LeanObject,
    mut v_inst_3030_: *mut crate::leanh::LeanObject,
    mut v_inst_3031_: *mut crate::leanh::LeanObject,
    mut v_inst_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(
        v_m_3024_,
        v_n_3025_,
        v_00_u03b1_3026_,
        v_00_u03b2_3027_,
        v_inst_3028_,
        v_inst_3029_,
        v_inst_3030_,
        v_inst_3031_,
        v_inst_3032_,
    );
    crate::leanh::lean_dec(v_inst_3028_);
    return v_res_3033_;
}
pub unsafe fn l_Std_IterM_foldM___redArg___lam__0(
    mut v_a_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3035_, 0, v_a_3034_);
    return v___x_3035_;
}
pub unsafe fn l_Std_IterM_foldM___redArg___lam__3(
    mut v_toFunctor_3036_: *mut crate::leanh::LeanObject,
    mut v_f_3037_: *mut crate::leanh::LeanObject,
    mut v___f_3038_: *mut crate::leanh::LeanObject,
    mut v_toBind_3039_: *mut crate::leanh::LeanObject,
    mut v___f_3040_: *mut crate::leanh::LeanObject,
    mut v_x1_3041_: *mut crate::leanh::LeanObject,
    mut v_x2_3042_: *mut crate::leanh::LeanObject,
    mut v_x3_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_3044_ = crate::leanh::lean_ctor_get(v_toFunctor_3036_, 0);
    crate::leanh::lean_inc(v_map_3044_);
    crate::leanh::lean_dec_ref(v_toFunctor_3036_);
    v___x_3045_ = crate::leanh::lean_apply_2(v_f_3037_, v_x3_3043_, v_x1_3041_);
    v___x_3046_ = crate::leanh::lean_apply_4(
        v_map_3044_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_3038_,
        v___x_3045_,
    );
    v___x_3047_ = crate::leanh::lean_apply_4(
        v_toBind_3039_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3046_,
        v___f_3040_,
    );
    return v___x_3047_;
}
pub unsafe fn l_Std_IterM_foldM___redArg(
    mut v_inst_3049_: *mut crate::leanh::LeanObject,
    mut v_inst_3050_: *mut crate::leanh::LeanObject,
    mut v_inst_3051_: *mut crate::leanh::LeanObject,
    mut v_f_3052_: *mut crate::leanh::LeanObject,
    mut v_init_3053_: *mut crate::leanh::LeanObject,
    mut v_it_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3055_ = crate::leanh::lean_ctor_get(v_inst_3049_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3055_);
    v_toBind_3056_ = crate::leanh::lean_ctor_get(v_inst_3049_, 1);
    crate::leanh::lean_inc_n(v_toBind_3056_, 2);
    crate::leanh::lean_dec_ref(v_inst_3049_);
    v_toFunctor_3057_ = crate::leanh::lean_ctor_get(v_toApplicative_3055_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3057_);
    v_toPure_3058_ = crate::leanh::lean_ctor_get(v_toApplicative_3055_, 1);
    crate::leanh::lean_inc(v_toPure_3058_);
    crate::leanh::lean_dec_ref(v_toApplicative_3055_);
    v___f_3059_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3060_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3060_, 0, v_inst_3051_);
    crate::leanh::lean_closure_set(v___f_3060_, 1, v_toBind_3056_);
    v___f_3061_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3061_, 0, v_toPure_3058_);
    v___f_3062_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3062_, 0, v_toFunctor_3057_);
    crate::leanh::lean_closure_set(v___f_3062_, 1, v_f_3052_);
    crate::leanh::lean_closure_set(v___f_3062_, 2, v___f_3059_);
    crate::leanh::lean_closure_set(v___f_3062_, 3, v_toBind_3056_);
    crate::leanh::lean_closure_set(v___f_3062_, 4, v___f_3061_);
    v___x_3063_ = crate::leanh::lean_apply_6(
        v_inst_3050_,
        v___f_3060_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3054_,
        v_init_3053_,
        v___f_3062_,
    );
    return v___x_3063_;
}
pub unsafe fn l_Std_IterM_foldM(
    mut v_m_3064_: *mut crate::leanh::LeanObject,
    mut v_n_3065_: *mut crate::leanh::LeanObject,
    mut v_inst_3066_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3067_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3069_: *mut crate::leanh::LeanObject,
    mut v_inst_3070_: *mut crate::leanh::LeanObject,
    mut v_inst_3071_: *mut crate::leanh::LeanObject,
    mut v_inst_3072_: *mut crate::leanh::LeanObject,
    mut v_f_3073_: *mut crate::leanh::LeanObject,
    mut v_init_3074_: *mut crate::leanh::LeanObject,
    mut v_it_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3076_ = crate::leanh::lean_ctor_get(v_inst_3066_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3076_);
    v_toBind_3077_ = crate::leanh::lean_ctor_get(v_inst_3066_, 1);
    crate::leanh::lean_inc_n(v_toBind_3077_, 2);
    crate::leanh::lean_dec_ref(v_inst_3066_);
    v_toFunctor_3078_ = crate::leanh::lean_ctor_get(v_toApplicative_3076_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3078_);
    v_toPure_3079_ = crate::leanh::lean_ctor_get(v_toApplicative_3076_, 1);
    crate::leanh::lean_inc(v_toPure_3079_);
    crate::leanh::lean_dec_ref(v_toApplicative_3076_);
    v___f_3080_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3081_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3081_, 0, v_inst_3072_);
    crate::leanh::lean_closure_set(v___f_3081_, 1, v_toBind_3077_);
    v___f_3082_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3082_, 0, v_toPure_3079_);
    v___f_3083_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3083_, 0, v_toFunctor_3078_);
    crate::leanh::lean_closure_set(v___f_3083_, 1, v_f_3073_);
    crate::leanh::lean_closure_set(v___f_3083_, 2, v___f_3080_);
    crate::leanh::lean_closure_set(v___f_3083_, 3, v_toBind_3077_);
    crate::leanh::lean_closure_set(v___f_3083_, 4, v___f_3082_);
    v___x_3084_ = crate::leanh::lean_apply_6(
        v_inst_3071_,
        v___f_3081_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3075_,
        v_init_3074_,
        v___f_3083_,
    );
    return v___x_3084_;
}
pub unsafe fn l_Std_IterM_foldM___boxed(
    mut v_m_3085_: *mut crate::leanh::LeanObject,
    mut v_n_3086_: *mut crate::leanh::LeanObject,
    mut v_inst_3087_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3090_: *mut crate::leanh::LeanObject,
    mut v_inst_3091_: *mut crate::leanh::LeanObject,
    mut v_inst_3092_: *mut crate::leanh::LeanObject,
    mut v_inst_3093_: *mut crate::leanh::LeanObject,
    mut v_f_3094_: *mut crate::leanh::LeanObject,
    mut v_init_3095_: *mut crate::leanh::LeanObject,
    mut v_it_3096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Std_IterM_foldM(
        v_m_3085_,
        v_n_3086_,
        v_inst_3087_,
        v_00_u03b1_3088_,
        v_00_u03b2_3089_,
        v_00_u03b3_3090_,
        v_inst_3091_,
        v_inst_3092_,
        v_inst_3093_,
        v_f_3094_,
        v_init_3095_,
        v_it_3096_,
    );
    crate::leanh::lean_dec(v_inst_3091_);
    return v_res_3097_;
}
pub unsafe fn l_Std_IterM_Partial_foldM___redArg(
    mut v_inst_3098_: *mut crate::leanh::LeanObject,
    mut v_inst_3099_: *mut crate::leanh::LeanObject,
    mut v_inst_3100_: *mut crate::leanh::LeanObject,
    mut v_f_3101_: *mut crate::leanh::LeanObject,
    mut v_init_3102_: *mut crate::leanh::LeanObject,
    mut v_it_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3104_ = crate::leanh::lean_ctor_get(v_inst_3098_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3104_);
    v_toBind_3105_ = crate::leanh::lean_ctor_get(v_inst_3098_, 1);
    crate::leanh::lean_inc_n(v_toBind_3105_, 2);
    crate::leanh::lean_dec_ref(v_inst_3098_);
    v_toFunctor_3106_ = crate::leanh::lean_ctor_get(v_toApplicative_3104_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3106_);
    v_toPure_3107_ = crate::leanh::lean_ctor_get(v_toApplicative_3104_, 1);
    crate::leanh::lean_inc(v_toPure_3107_);
    crate::leanh::lean_dec_ref(v_toApplicative_3104_);
    v___f_3108_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3109_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3109_, 0, v_inst_3100_);
    crate::leanh::lean_closure_set(v___f_3109_, 1, v_toBind_3105_);
    v___f_3110_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3110_, 0, v_toPure_3107_);
    v___f_3111_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3111_, 0, v_toFunctor_3106_);
    crate::leanh::lean_closure_set(v___f_3111_, 1, v_f_3101_);
    crate::leanh::lean_closure_set(v___f_3111_, 2, v___f_3108_);
    crate::leanh::lean_closure_set(v___f_3111_, 3, v_toBind_3105_);
    crate::leanh::lean_closure_set(v___f_3111_, 4, v___f_3110_);
    v___x_3112_ = crate::leanh::lean_apply_6(
        v_inst_3099_,
        v___f_3109_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3103_,
        v_init_3102_,
        v___f_3111_,
    );
    return v___x_3112_;
}
pub unsafe fn l_Std_IterM_Partial_foldM(
    mut v_m_3113_: *mut crate::leanh::LeanObject,
    mut v_n_3114_: *mut crate::leanh::LeanObject,
    mut v_inst_3115_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3116_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3118_: *mut crate::leanh::LeanObject,
    mut v_inst_3119_: *mut crate::leanh::LeanObject,
    mut v_inst_3120_: *mut crate::leanh::LeanObject,
    mut v_inst_3121_: *mut crate::leanh::LeanObject,
    mut v_f_3122_: *mut crate::leanh::LeanObject,
    mut v_init_3123_: *mut crate::leanh::LeanObject,
    mut v_it_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3125_ = crate::leanh::lean_ctor_get(v_inst_3115_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3125_);
    v_toBind_3126_ = crate::leanh::lean_ctor_get(v_inst_3115_, 1);
    crate::leanh::lean_inc_n(v_toBind_3126_, 2);
    crate::leanh::lean_dec_ref(v_inst_3115_);
    v_toFunctor_3127_ = crate::leanh::lean_ctor_get(v_toApplicative_3125_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3127_);
    v_toPure_3128_ = crate::leanh::lean_ctor_get(v_toApplicative_3125_, 1);
    crate::leanh::lean_inc(v_toPure_3128_);
    crate::leanh::lean_dec_ref(v_toApplicative_3125_);
    v___f_3129_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3130_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3130_, 0, v_inst_3121_);
    crate::leanh::lean_closure_set(v___f_3130_, 1, v_toBind_3126_);
    v___f_3131_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3131_, 0, v_toPure_3128_);
    v___f_3132_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3132_, 0, v_toFunctor_3127_);
    crate::leanh::lean_closure_set(v___f_3132_, 1, v_f_3122_);
    crate::leanh::lean_closure_set(v___f_3132_, 2, v___f_3129_);
    crate::leanh::lean_closure_set(v___f_3132_, 3, v_toBind_3126_);
    crate::leanh::lean_closure_set(v___f_3132_, 4, v___f_3131_);
    v___x_3133_ = crate::leanh::lean_apply_6(
        v_inst_3120_,
        v___f_3130_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3124_,
        v_init_3123_,
        v___f_3132_,
    );
    return v___x_3133_;
}
pub unsafe fn l_Std_IterM_Partial_foldM___boxed(
    mut v_m_3134_: *mut crate::leanh::LeanObject,
    mut v_n_3135_: *mut crate::leanh::LeanObject,
    mut v_inst_3136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3139_: *mut crate::leanh::LeanObject,
    mut v_inst_3140_: *mut crate::leanh::LeanObject,
    mut v_inst_3141_: *mut crate::leanh::LeanObject,
    mut v_inst_3142_: *mut crate::leanh::LeanObject,
    mut v_f_3143_: *mut crate::leanh::LeanObject,
    mut v_init_3144_: *mut crate::leanh::LeanObject,
    mut v_it_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Std_IterM_Partial_foldM(
        v_m_3134_,
        v_n_3135_,
        v_inst_3136_,
        v_00_u03b1_3137_,
        v_00_u03b2_3138_,
        v_00_u03b3_3139_,
        v_inst_3140_,
        v_inst_3141_,
        v_inst_3142_,
        v_f_3143_,
        v_init_3144_,
        v_it_3145_,
    );
    crate::leanh::lean_dec(v_inst_3140_);
    return v_res_3146_;
}
pub unsafe fn l_Std_IterM_Total_foldM___redArg(
    mut v_inst_3147_: *mut crate::leanh::LeanObject,
    mut v_inst_3148_: *mut crate::leanh::LeanObject,
    mut v_inst_3149_: *mut crate::leanh::LeanObject,
    mut v_f_3150_: *mut crate::leanh::LeanObject,
    mut v_init_3151_: *mut crate::leanh::LeanObject,
    mut v_it_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3153_ = crate::leanh::lean_ctor_get(v_inst_3147_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3153_);
    v_toBind_3154_ = crate::leanh::lean_ctor_get(v_inst_3147_, 1);
    crate::leanh::lean_inc_n(v_toBind_3154_, 2);
    crate::leanh::lean_dec_ref(v_inst_3147_);
    v_toFunctor_3155_ = crate::leanh::lean_ctor_get(v_toApplicative_3153_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3155_);
    v_toPure_3156_ = crate::leanh::lean_ctor_get(v_toApplicative_3153_, 1);
    crate::leanh::lean_inc(v_toPure_3156_);
    crate::leanh::lean_dec_ref(v_toApplicative_3153_);
    v___f_3157_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3158_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3158_, 0, v_inst_3149_);
    crate::leanh::lean_closure_set(v___f_3158_, 1, v_toBind_3154_);
    v___f_3159_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3159_, 0, v_toPure_3156_);
    v___f_3160_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3160_, 0, v_toFunctor_3155_);
    crate::leanh::lean_closure_set(v___f_3160_, 1, v_f_3150_);
    crate::leanh::lean_closure_set(v___f_3160_, 2, v___f_3157_);
    crate::leanh::lean_closure_set(v___f_3160_, 3, v_toBind_3154_);
    crate::leanh::lean_closure_set(v___f_3160_, 4, v___f_3159_);
    v___x_3161_ = crate::leanh::lean_apply_6(
        v_inst_3148_,
        v___f_3158_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3152_,
        v_init_3151_,
        v___f_3160_,
    );
    return v___x_3161_;
}
pub unsafe fn l_Std_IterM_Total_foldM(
    mut v_m_3162_: *mut crate::leanh::LeanObject,
    mut v_n_3163_: *mut crate::leanh::LeanObject,
    mut v_inst_3164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3165_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3167_: *mut crate::leanh::LeanObject,
    mut v_inst_3168_: *mut crate::leanh::LeanObject,
    mut v_inst_3169_: *mut crate::leanh::LeanObject,
    mut v_inst_3170_: *mut crate::leanh::LeanObject,
    mut v_inst_3171_: *mut crate::leanh::LeanObject,
    mut v_f_3172_: *mut crate::leanh::LeanObject,
    mut v_init_3173_: *mut crate::leanh::LeanObject,
    mut v_it_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3175_ = crate::leanh::lean_ctor_get(v_inst_3164_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3175_);
    v_toBind_3176_ = crate::leanh::lean_ctor_get(v_inst_3164_, 1);
    crate::leanh::lean_inc_n(v_toBind_3176_, 2);
    crate::leanh::lean_dec_ref(v_inst_3164_);
    v_toFunctor_3177_ = crate::leanh::lean_ctor_get(v_toApplicative_3175_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3177_);
    v_toPure_3178_ = crate::leanh::lean_ctor_get(v_toApplicative_3175_, 1);
    crate::leanh::lean_inc(v_toPure_3178_);
    crate::leanh::lean_dec_ref(v_toApplicative_3175_);
    v___f_3179_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3180_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3180_, 0, v_inst_3170_);
    crate::leanh::lean_closure_set(v___f_3180_, 1, v_toBind_3176_);
    v___f_3181_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3181_, 0, v_toPure_3178_);
    v___f_3182_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3182_, 0, v_toFunctor_3177_);
    crate::leanh::lean_closure_set(v___f_3182_, 1, v_f_3172_);
    crate::leanh::lean_closure_set(v___f_3182_, 2, v___f_3179_);
    crate::leanh::lean_closure_set(v___f_3182_, 3, v_toBind_3176_);
    crate::leanh::lean_closure_set(v___f_3182_, 4, v___f_3181_);
    v___x_3183_ = crate::leanh::lean_apply_6(
        v_inst_3169_,
        v___f_3180_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3174_,
        v_init_3173_,
        v___f_3182_,
    );
    return v___x_3183_;
}
pub unsafe fn l_Std_IterM_Total_foldM___boxed(
    mut v_m_3184_: *mut crate::leanh::LeanObject,
    mut v_n_3185_: *mut crate::leanh::LeanObject,
    mut v_inst_3186_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3187_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3188_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3189_: *mut crate::leanh::LeanObject,
    mut v_inst_3190_: *mut crate::leanh::LeanObject,
    mut v_inst_3191_: *mut crate::leanh::LeanObject,
    mut v_inst_3192_: *mut crate::leanh::LeanObject,
    mut v_inst_3193_: *mut crate::leanh::LeanObject,
    mut v_f_3194_: *mut crate::leanh::LeanObject,
    mut v_init_3195_: *mut crate::leanh::LeanObject,
    mut v_it_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Std_IterM_Total_foldM(
        v_m_3184_,
        v_n_3185_,
        v_inst_3186_,
        v_00_u03b1_3187_,
        v_00_u03b2_3188_,
        v_00_u03b3_3189_,
        v_inst_3190_,
        v_inst_3191_,
        v_inst_3192_,
        v_inst_3193_,
        v_f_3194_,
        v_init_3195_,
        v_it_3196_,
    );
    crate::leanh::lean_dec(v_inst_3190_);
    return v_res_3197_;
}
pub unsafe fn l_Std_IterM_fold___redArg___lam__0(
    mut v_toBind_3198_: *mut crate::leanh::LeanObject,
    mut v_x_3199_: *mut crate::leanh::LeanObject,
    mut v_x_3200_: *mut crate::leanh::LeanObject,
    mut v_f_3201_: *mut crate::leanh::LeanObject,
    mut v_x_3202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = crate::leanh::lean_apply_4(
        v_toBind_3198_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_3202_,
        v_f_3201_,
    );
    return v___x_3203_;
}
pub unsafe fn l_Std_IterM_fold___redArg___lam__2(
    mut v_f_3204_: *mut crate::leanh::LeanObject,
    mut v_toPure_3205_: *mut crate::leanh::LeanObject,
    mut v_toBind_3206_: *mut crate::leanh::LeanObject,
    mut v___f_3207_: *mut crate::leanh::LeanObject,
    mut v_x1_3208_: *mut crate::leanh::LeanObject,
    mut v_x2_3209_: *mut crate::leanh::LeanObject,
    mut v_x3_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3211_ = crate::leanh::lean_apply_2(v_f_3204_, v_x3_3210_, v_x1_3208_);
    v___x_3212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3212_, 0, v___x_3211_);
    v___x_3213_ =
        crate::leanh::lean_apply_2(v_toPure_3205_, crate::leanh::lean_box(0), v___x_3212_);
    v___x_3214_ = crate::leanh::lean_apply_4(
        v_toBind_3206_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3213_,
        v___f_3207_,
    );
    return v___x_3214_;
}
pub unsafe fn l_Std_IterM_fold___redArg(
    mut v_inst_3215_: *mut crate::leanh::LeanObject,
    mut v_inst_3216_: *mut crate::leanh::LeanObject,
    mut v_f_3217_: *mut crate::leanh::LeanObject,
    mut v_init_3218_: *mut crate::leanh::LeanObject,
    mut v_it_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3220_ = crate::leanh::lean_ctor_get(v_inst_3215_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3220_);
    v_toBind_3221_ = crate::leanh::lean_ctor_get(v_inst_3215_, 1);
    crate::leanh::lean_inc_n(v_toBind_3221_, 2);
    crate::leanh::lean_dec_ref(v_inst_3215_);
    v_toPure_3222_ = crate::leanh::lean_ctor_get(v_toApplicative_3220_, 1);
    crate::leanh::lean_inc_n(v_toPure_3222_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3220_);
    v___f_3223_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3223_, 0, v_toBind_3221_);
    v___f_3224_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3224_, 0, v_toPure_3222_);
    v___f_3225_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3225_, 0, v_f_3217_);
    crate::leanh::lean_closure_set(v___f_3225_, 1, v_toPure_3222_);
    crate::leanh::lean_closure_set(v___f_3225_, 2, v_toBind_3221_);
    crate::leanh::lean_closure_set(v___f_3225_, 3, v___f_3224_);
    v___x_3226_ = crate::leanh::lean_apply_6(
        v_inst_3216_,
        v___f_3223_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3219_,
        v_init_3218_,
        v___f_3225_,
    );
    return v___x_3226_;
}
pub unsafe fn l_Std_IterM_fold(
    mut v_m_3227_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3230_: *mut crate::leanh::LeanObject,
    mut v_inst_3231_: *mut crate::leanh::LeanObject,
    mut v_inst_3232_: *mut crate::leanh::LeanObject,
    mut v_inst_3233_: *mut crate::leanh::LeanObject,
    mut v_f_3234_: *mut crate::leanh::LeanObject,
    mut v_init_3235_: *mut crate::leanh::LeanObject,
    mut v_it_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3237_ = crate::leanh::lean_ctor_get(v_inst_3231_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3237_);
    v_toBind_3238_ = crate::leanh::lean_ctor_get(v_inst_3231_, 1);
    crate::leanh::lean_inc_n(v_toBind_3238_, 2);
    crate::leanh::lean_dec_ref(v_inst_3231_);
    v_toPure_3239_ = crate::leanh::lean_ctor_get(v_toApplicative_3237_, 1);
    crate::leanh::lean_inc_n(v_toPure_3239_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3237_);
    v___f_3240_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3240_, 0, v_toBind_3238_);
    v___f_3241_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3241_, 0, v_toPure_3239_);
    v___f_3242_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3242_, 0, v_f_3234_);
    crate::leanh::lean_closure_set(v___f_3242_, 1, v_toPure_3239_);
    crate::leanh::lean_closure_set(v___f_3242_, 2, v_toBind_3238_);
    crate::leanh::lean_closure_set(v___f_3242_, 3, v___f_3241_);
    v___x_3243_ = crate::leanh::lean_apply_6(
        v_inst_3233_,
        v___f_3240_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3236_,
        v_init_3235_,
        v___f_3242_,
    );
    return v___x_3243_;
}
pub unsafe fn l_Std_IterM_fold___boxed(
    mut v_m_3244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3245_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3247_: *mut crate::leanh::LeanObject,
    mut v_inst_3248_: *mut crate::leanh::LeanObject,
    mut v_inst_3249_: *mut crate::leanh::LeanObject,
    mut v_inst_3250_: *mut crate::leanh::LeanObject,
    mut v_f_3251_: *mut crate::leanh::LeanObject,
    mut v_init_3252_: *mut crate::leanh::LeanObject,
    mut v_it_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3254_ = l_Std_IterM_fold(
        v_m_3244_,
        v_00_u03b1_3245_,
        v_00_u03b2_3246_,
        v_00_u03b3_3247_,
        v_inst_3248_,
        v_inst_3249_,
        v_inst_3250_,
        v_f_3251_,
        v_init_3252_,
        v_it_3253_,
    );
    crate::leanh::lean_dec(v_inst_3249_);
    return v_res_3254_;
}
pub unsafe fn l_Std_IterM_Partial_fold___redArg(
    mut v_inst_3255_: *mut crate::leanh::LeanObject,
    mut v_inst_3256_: *mut crate::leanh::LeanObject,
    mut v_f_3257_: *mut crate::leanh::LeanObject,
    mut v_init_3258_: *mut crate::leanh::LeanObject,
    mut v_it_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3260_ = crate::leanh::lean_ctor_get(v_inst_3255_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3260_);
    v_toBind_3261_ = crate::leanh::lean_ctor_get(v_inst_3255_, 1);
    crate::leanh::lean_inc_n(v_toBind_3261_, 2);
    crate::leanh::lean_dec_ref(v_inst_3255_);
    v_toPure_3262_ = crate::leanh::lean_ctor_get(v_toApplicative_3260_, 1);
    crate::leanh::lean_inc_n(v_toPure_3262_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3260_);
    v___f_3263_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3263_, 0, v_toBind_3261_);
    v___f_3264_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3264_, 0, v_toPure_3262_);
    v___f_3265_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3265_, 0, v_f_3257_);
    crate::leanh::lean_closure_set(v___f_3265_, 1, v_toPure_3262_);
    crate::leanh::lean_closure_set(v___f_3265_, 2, v_toBind_3261_);
    crate::leanh::lean_closure_set(v___f_3265_, 3, v___f_3264_);
    v___x_3266_ = crate::leanh::lean_apply_6(
        v_inst_3256_,
        v___f_3263_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3259_,
        v_init_3258_,
        v___f_3265_,
    );
    return v___x_3266_;
}
pub unsafe fn l_Std_IterM_Partial_fold(
    mut v_m_3267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3270_: *mut crate::leanh::LeanObject,
    mut v_inst_3271_: *mut crate::leanh::LeanObject,
    mut v_inst_3272_: *mut crate::leanh::LeanObject,
    mut v_inst_3273_: *mut crate::leanh::LeanObject,
    mut v_f_3274_: *mut crate::leanh::LeanObject,
    mut v_init_3275_: *mut crate::leanh::LeanObject,
    mut v_it_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3277_ = crate::leanh::lean_ctor_get(v_inst_3271_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3277_);
    v_toBind_3278_ = crate::leanh::lean_ctor_get(v_inst_3271_, 1);
    crate::leanh::lean_inc_n(v_toBind_3278_, 2);
    crate::leanh::lean_dec_ref(v_inst_3271_);
    v_toPure_3279_ = crate::leanh::lean_ctor_get(v_toApplicative_3277_, 1);
    crate::leanh::lean_inc_n(v_toPure_3279_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3277_);
    v___f_3280_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3280_, 0, v_toBind_3278_);
    v___f_3281_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3281_, 0, v_toPure_3279_);
    v___f_3282_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3282_, 0, v_f_3274_);
    crate::leanh::lean_closure_set(v___f_3282_, 1, v_toPure_3279_);
    crate::leanh::lean_closure_set(v___f_3282_, 2, v_toBind_3278_);
    crate::leanh::lean_closure_set(v___f_3282_, 3, v___f_3281_);
    v___x_3283_ = crate::leanh::lean_apply_6(
        v_inst_3273_,
        v___f_3280_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3276_,
        v_init_3275_,
        v___f_3282_,
    );
    return v___x_3283_;
}
pub unsafe fn l_Std_IterM_Partial_fold___boxed(
    mut v_m_3284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3286_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3287_: *mut crate::leanh::LeanObject,
    mut v_inst_3288_: *mut crate::leanh::LeanObject,
    mut v_inst_3289_: *mut crate::leanh::LeanObject,
    mut v_inst_3290_: *mut crate::leanh::LeanObject,
    mut v_f_3291_: *mut crate::leanh::LeanObject,
    mut v_init_3292_: *mut crate::leanh::LeanObject,
    mut v_it_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Std_IterM_Partial_fold(
        v_m_3284_,
        v_00_u03b1_3285_,
        v_00_u03b2_3286_,
        v_00_u03b3_3287_,
        v_inst_3288_,
        v_inst_3289_,
        v_inst_3290_,
        v_f_3291_,
        v_init_3292_,
        v_it_3293_,
    );
    crate::leanh::lean_dec(v_inst_3289_);
    return v_res_3294_;
}
pub unsafe fn l_Std_IterM_Total_fold___redArg(
    mut v_inst_3295_: *mut crate::leanh::LeanObject,
    mut v_inst_3296_: *mut crate::leanh::LeanObject,
    mut v_f_3297_: *mut crate::leanh::LeanObject,
    mut v_init_3298_: *mut crate::leanh::LeanObject,
    mut v_it_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3300_ = crate::leanh::lean_ctor_get(v_inst_3295_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3300_);
    v_toBind_3301_ = crate::leanh::lean_ctor_get(v_inst_3295_, 1);
    crate::leanh::lean_inc_n(v_toBind_3301_, 2);
    crate::leanh::lean_dec_ref(v_inst_3295_);
    v_toPure_3302_ = crate::leanh::lean_ctor_get(v_toApplicative_3300_, 1);
    crate::leanh::lean_inc_n(v_toPure_3302_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3300_);
    v___f_3303_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3303_, 0, v_toBind_3301_);
    v___f_3304_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3304_, 0, v_toPure_3302_);
    v___f_3305_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3305_, 0, v_f_3297_);
    crate::leanh::lean_closure_set(v___f_3305_, 1, v_toPure_3302_);
    crate::leanh::lean_closure_set(v___f_3305_, 2, v_toBind_3301_);
    crate::leanh::lean_closure_set(v___f_3305_, 3, v___f_3304_);
    v___x_3306_ = crate::leanh::lean_apply_6(
        v_inst_3296_,
        v___f_3303_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3299_,
        v_init_3298_,
        v___f_3305_,
    );
    return v___x_3306_;
}
pub unsafe fn l_Std_IterM_Total_fold(
    mut v_m_3307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3310_: *mut crate::leanh::LeanObject,
    mut v_inst_3311_: *mut crate::leanh::LeanObject,
    mut v_inst_3312_: *mut crate::leanh::LeanObject,
    mut v_inst_3313_: *mut crate::leanh::LeanObject,
    mut v_inst_3314_: *mut crate::leanh::LeanObject,
    mut v_f_3315_: *mut crate::leanh::LeanObject,
    mut v_init_3316_: *mut crate::leanh::LeanObject,
    mut v_it_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3318_ = crate::leanh::lean_ctor_get(v_inst_3311_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3318_);
    v_toBind_3319_ = crate::leanh::lean_ctor_get(v_inst_3311_, 1);
    crate::leanh::lean_inc_n(v_toBind_3319_, 2);
    crate::leanh::lean_dec_ref(v_inst_3311_);
    v_toPure_3320_ = crate::leanh::lean_ctor_get(v_toApplicative_3318_, 1);
    crate::leanh::lean_inc_n(v_toPure_3320_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3318_);
    v___f_3321_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3321_, 0, v_toBind_3319_);
    v___f_3322_ = crate::leanh::lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3322_, 0, v_toPure_3320_);
    v___f_3323_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3323_, 0, v_f_3315_);
    crate::leanh::lean_closure_set(v___f_3323_, 1, v_toPure_3320_);
    crate::leanh::lean_closure_set(v___f_3323_, 2, v_toBind_3319_);
    crate::leanh::lean_closure_set(v___f_3323_, 3, v___f_3322_);
    v___x_3324_ = crate::leanh::lean_apply_6(
        v_inst_3313_,
        v___f_3321_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3317_,
        v_init_3316_,
        v___f_3323_,
    );
    return v___x_3324_;
}
pub unsafe fn l_Std_IterM_Total_fold___boxed(
    mut v_m_3325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3326_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3327_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3328_: *mut crate::leanh::LeanObject,
    mut v_inst_3329_: *mut crate::leanh::LeanObject,
    mut v_inst_3330_: *mut crate::leanh::LeanObject,
    mut v_inst_3331_: *mut crate::leanh::LeanObject,
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_f_3333_: *mut crate::leanh::LeanObject,
    mut v_init_3334_: *mut crate::leanh::LeanObject,
    mut v_it_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Std_IterM_Total_fold(
        v_m_3325_,
        v_00_u03b1_3326_,
        v_00_u03b2_3327_,
        v_00_u03b3_3328_,
        v_inst_3329_,
        v_inst_3330_,
        v_inst_3331_,
        v_inst_3332_,
        v_f_3333_,
        v_init_3334_,
        v_it_3335_,
    );
    crate::leanh::lean_dec(v_inst_3330_);
    return v_res_3336_;
}
pub unsafe fn l_Std_IterM_drain___redArg___lam__2(
    mut v___x_3337_: *mut crate::leanh::LeanObject,
    mut v_toPure_3338_: *mut crate::leanh::LeanObject,
    mut v_toBind_3339_: *mut crate::leanh::LeanObject,
    mut v___f_3340_: *mut crate::leanh::LeanObject,
    mut v_x1_3341_: *mut crate::leanh::LeanObject,
    mut v_x2_3342_: *mut crate::leanh::LeanObject,
    mut v_x3_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3337_);
    v___x_3345_ =
        crate::leanh::lean_apply_2(v_toPure_3338_, crate::leanh::lean_box(0), v___x_3344_);
    v___x_3346_ = crate::leanh::lean_apply_4(
        v_toBind_3339_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3345_,
        v___f_3340_,
    );
    return v___x_3346_;
}
pub unsafe fn l_Std_IterM_drain___redArg___lam__2___boxed(
    mut v___x_3347_: *mut crate::leanh::LeanObject,
    mut v_toPure_3348_: *mut crate::leanh::LeanObject,
    mut v_toBind_3349_: *mut crate::leanh::LeanObject,
    mut v___f_3350_: *mut crate::leanh::LeanObject,
    mut v_x1_3351_: *mut crate::leanh::LeanObject,
    mut v_x2_3352_: *mut crate::leanh::LeanObject,
    mut v_x3_3353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3354_ = l_Std_IterM_drain___redArg___lam__2(
        v___x_3347_,
        v_toPure_3348_,
        v_toBind_3349_,
        v___f_3350_,
        v_x1_3351_,
        v_x2_3352_,
        v_x3_3353_,
    );
    crate::leanh::lean_dec(v_x1_3351_);
    return v_res_3354_;
}
pub unsafe fn l_Std_IterM_drain___redArg(
    mut v_inst_3355_: *mut crate::leanh::LeanObject,
    mut v_it_3356_: *mut crate::leanh::LeanObject,
    mut v_inst_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3358_ = crate::leanh::lean_ctor_get(v_inst_3355_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3358_);
    v_toBind_3359_ = crate::leanh::lean_ctor_get(v_inst_3355_, 1);
    crate::leanh::lean_inc_n(v_toBind_3359_, 2);
    crate::leanh::lean_dec_ref(v_inst_3355_);
    v_toPure_3360_ = crate::leanh::lean_ctor_get(v_toApplicative_3358_, 1);
    crate::leanh::lean_inc_n(v_toPure_3360_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3358_);
    v___x_3361_ = crate::leanh::lean_box(0);
    v___f_3362_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3362_, 0, v_toBind_3359_);
    v___f_3363_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3363_, 0, v_toPure_3360_);
    v___f_3364_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3364_, 0, v___x_3361_);
    crate::leanh::lean_closure_set(v___f_3364_, 1, v_toPure_3360_);
    crate::leanh::lean_closure_set(v___f_3364_, 2, v_toBind_3359_);
    crate::leanh::lean_closure_set(v___f_3364_, 3, v___f_3363_);
    v___x_3365_ = crate::leanh::lean_apply_6(
        v_inst_3357_,
        v___f_3362_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3356_,
        v___x_3361_,
        v___f_3364_,
    );
    return v___x_3365_;
}
pub unsafe fn l_Std_IterM_drain(
    mut v_00_u03b1_3366_: *mut crate::leanh::LeanObject,
    mut v_m_3367_: *mut crate::leanh::LeanObject,
    mut v_inst_3368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3369_: *mut crate::leanh::LeanObject,
    mut v_inst_3370_: *mut crate::leanh::LeanObject,
    mut v_it_3371_: *mut crate::leanh::LeanObject,
    mut v_inst_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3373_ = crate::leanh::lean_ctor_get(v_inst_3368_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3373_);
    v_toBind_3374_ = crate::leanh::lean_ctor_get(v_inst_3368_, 1);
    crate::leanh::lean_inc_n(v_toBind_3374_, 2);
    crate::leanh::lean_dec_ref(v_inst_3368_);
    v_toPure_3375_ = crate::leanh::lean_ctor_get(v_toApplicative_3373_, 1);
    crate::leanh::lean_inc_n(v_toPure_3375_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3373_);
    v___x_3376_ = crate::leanh::lean_box(0);
    v___f_3377_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3377_, 0, v_toBind_3374_);
    v___f_3378_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3378_, 0, v_toPure_3375_);
    v___f_3379_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3379_, 0, v___x_3376_);
    crate::leanh::lean_closure_set(v___f_3379_, 1, v_toPure_3375_);
    crate::leanh::lean_closure_set(v___f_3379_, 2, v_toBind_3374_);
    crate::leanh::lean_closure_set(v___f_3379_, 3, v___f_3378_);
    v___x_3380_ = crate::leanh::lean_apply_6(
        v_inst_3372_,
        v___f_3377_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3371_,
        v___x_3376_,
        v___f_3379_,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_IterM_drain___boxed(
    mut v_00_u03b1_3381_: *mut crate::leanh::LeanObject,
    mut v_m_3382_: *mut crate::leanh::LeanObject,
    mut v_inst_3383_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3384_: *mut crate::leanh::LeanObject,
    mut v_inst_3385_: *mut crate::leanh::LeanObject,
    mut v_it_3386_: *mut crate::leanh::LeanObject,
    mut v_inst_3387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Std_IterM_drain(
        v_00_u03b1_3381_,
        v_m_3382_,
        v_inst_3383_,
        v_00_u03b2_3384_,
        v_inst_3385_,
        v_it_3386_,
        v_inst_3387_,
    );
    crate::leanh::lean_dec(v_inst_3385_);
    return v_res_3388_;
}
pub unsafe fn l_Std_IterM_Partial_drain___redArg(
    mut v_inst_3389_: *mut crate::leanh::LeanObject,
    mut v_it_3390_: *mut crate::leanh::LeanObject,
    mut v_inst_3391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3392_ = crate::leanh::lean_ctor_get(v_inst_3389_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3392_);
    v_toBind_3393_ = crate::leanh::lean_ctor_get(v_inst_3389_, 1);
    crate::leanh::lean_inc_n(v_toBind_3393_, 2);
    crate::leanh::lean_dec_ref(v_inst_3389_);
    v_toPure_3394_ = crate::leanh::lean_ctor_get(v_toApplicative_3392_, 1);
    crate::leanh::lean_inc_n(v_toPure_3394_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3392_);
    v___x_3395_ = crate::leanh::lean_box(0);
    v___f_3396_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3396_, 0, v_toBind_3393_);
    v___f_3397_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3397_, 0, v_toPure_3394_);
    v___f_3398_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3398_, 0, v___x_3395_);
    crate::leanh::lean_closure_set(v___f_3398_, 1, v_toPure_3394_);
    crate::leanh::lean_closure_set(v___f_3398_, 2, v_toBind_3393_);
    crate::leanh::lean_closure_set(v___f_3398_, 3, v___f_3397_);
    v___x_3399_ = crate::leanh::lean_apply_6(
        v_inst_3391_,
        v___f_3396_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3390_,
        v___x_3395_,
        v___f_3398_,
    );
    return v___x_3399_;
}
pub unsafe fn l_Std_IterM_Partial_drain(
    mut v_00_u03b1_3400_: *mut crate::leanh::LeanObject,
    mut v_m_3401_: *mut crate::leanh::LeanObject,
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3403_: *mut crate::leanh::LeanObject,
    mut v_inst_3404_: *mut crate::leanh::LeanObject,
    mut v_it_3405_: *mut crate::leanh::LeanObject,
    mut v_inst_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3407_ = crate::leanh::lean_ctor_get(v_inst_3402_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3407_);
    v_toBind_3408_ = crate::leanh::lean_ctor_get(v_inst_3402_, 1);
    crate::leanh::lean_inc_n(v_toBind_3408_, 2);
    crate::leanh::lean_dec_ref(v_inst_3402_);
    v_toPure_3409_ = crate::leanh::lean_ctor_get(v_toApplicative_3407_, 1);
    crate::leanh::lean_inc_n(v_toPure_3409_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3407_);
    v___x_3410_ = crate::leanh::lean_box(0);
    v___f_3411_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3411_, 0, v_toBind_3408_);
    v___f_3412_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3412_, 0, v_toPure_3409_);
    v___f_3413_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3413_, 0, v___x_3410_);
    crate::leanh::lean_closure_set(v___f_3413_, 1, v_toPure_3409_);
    crate::leanh::lean_closure_set(v___f_3413_, 2, v_toBind_3408_);
    crate::leanh::lean_closure_set(v___f_3413_, 3, v___f_3412_);
    v___x_3414_ = crate::leanh::lean_apply_6(
        v_inst_3406_,
        v___f_3411_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3405_,
        v___x_3410_,
        v___f_3413_,
    );
    return v___x_3414_;
}
pub unsafe fn l_Std_IterM_Partial_drain___boxed(
    mut v_00_u03b1_3415_: *mut crate::leanh::LeanObject,
    mut v_m_3416_: *mut crate::leanh::LeanObject,
    mut v_inst_3417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3418_: *mut crate::leanh::LeanObject,
    mut v_inst_3419_: *mut crate::leanh::LeanObject,
    mut v_it_3420_: *mut crate::leanh::LeanObject,
    mut v_inst_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Std_IterM_Partial_drain(
        v_00_u03b1_3415_,
        v_m_3416_,
        v_inst_3417_,
        v_00_u03b2_3418_,
        v_inst_3419_,
        v_it_3420_,
        v_inst_3421_,
    );
    crate::leanh::lean_dec(v_inst_3419_);
    return v_res_3422_;
}
pub unsafe fn l_Std_IterM_Total_drain___redArg(
    mut v_inst_3423_: *mut crate::leanh::LeanObject,
    mut v_it_3424_: *mut crate::leanh::LeanObject,
    mut v_inst_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3426_ = crate::leanh::lean_ctor_get(v_inst_3423_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3426_);
    v_toBind_3427_ = crate::leanh::lean_ctor_get(v_inst_3423_, 1);
    crate::leanh::lean_inc_n(v_toBind_3427_, 2);
    crate::leanh::lean_dec_ref(v_inst_3423_);
    v_toPure_3428_ = crate::leanh::lean_ctor_get(v_toApplicative_3426_, 1);
    crate::leanh::lean_inc_n(v_toPure_3428_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3426_);
    v___x_3429_ = crate::leanh::lean_box(0);
    v___f_3430_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3430_, 0, v_toBind_3427_);
    v___f_3431_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3431_, 0, v_toPure_3428_);
    v___f_3432_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3432_, 0, v___x_3429_);
    crate::leanh::lean_closure_set(v___f_3432_, 1, v_toPure_3428_);
    crate::leanh::lean_closure_set(v___f_3432_, 2, v_toBind_3427_);
    crate::leanh::lean_closure_set(v___f_3432_, 3, v___f_3431_);
    v___x_3433_ = crate::leanh::lean_apply_6(
        v_inst_3425_,
        v___f_3430_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3424_,
        v___x_3429_,
        v___f_3432_,
    );
    return v___x_3433_;
}
pub unsafe fn l_Std_IterM_Total_drain(
    mut v_00_u03b1_3434_: *mut crate::leanh::LeanObject,
    mut v_m_3435_: *mut crate::leanh::LeanObject,
    mut v_inst_3436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3437_: *mut crate::leanh::LeanObject,
    mut v_inst_3438_: *mut crate::leanh::LeanObject,
    mut v_inst_3439_: *mut crate::leanh::LeanObject,
    mut v_it_3440_: *mut crate::leanh::LeanObject,
    mut v_inst_3441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3442_ = crate::leanh::lean_ctor_get(v_inst_3436_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3442_);
    v_toBind_3443_ = crate::leanh::lean_ctor_get(v_inst_3436_, 1);
    crate::leanh::lean_inc_n(v_toBind_3443_, 2);
    crate::leanh::lean_dec_ref(v_inst_3436_);
    v_toPure_3444_ = crate::leanh::lean_ctor_get(v_toApplicative_3442_, 1);
    crate::leanh::lean_inc_n(v_toPure_3444_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3442_);
    v___x_3445_ = crate::leanh::lean_box(0);
    v___f_3446_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3446_, 0, v_toBind_3443_);
    v___f_3447_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3447_, 0, v_toPure_3444_);
    v___f_3448_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3448_, 0, v___x_3445_);
    crate::leanh::lean_closure_set(v___f_3448_, 1, v_toPure_3444_);
    crate::leanh::lean_closure_set(v___f_3448_, 2, v_toBind_3443_);
    crate::leanh::lean_closure_set(v___f_3448_, 3, v___f_3447_);
    v___x_3449_ = crate::leanh::lean_apply_6(
        v_inst_3441_,
        v___f_3446_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3440_,
        v___x_3445_,
        v___f_3448_,
    );
    return v___x_3449_;
}
pub unsafe fn l_Std_IterM_Total_drain___boxed(
    mut v_00_u03b1_3450_: *mut crate::leanh::LeanObject,
    mut v_m_3451_: *mut crate::leanh::LeanObject,
    mut v_inst_3452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3453_: *mut crate::leanh::LeanObject,
    mut v_inst_3454_: *mut crate::leanh::LeanObject,
    mut v_inst_3455_: *mut crate::leanh::LeanObject,
    mut v_it_3456_: *mut crate::leanh::LeanObject,
    mut v_inst_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Std_IterM_Total_drain(
        v_00_u03b1_3450_,
        v_m_3451_,
        v_inst_3452_,
        v_00_u03b2_3453_,
        v_inst_3454_,
        v_inst_3455_,
        v_it_3456_,
        v_inst_3457_,
    );
    crate::leanh::lean_dec(v_inst_3454_);
    return v_res_3458_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__1(
    mut v_toPure_3459_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = crate::leanh::lean_apply_2(
        v_toPure_3459_,
        crate::leanh::lean_box(0),
        v_____do__lift_3460_,
    );
    return v___x_3461_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__0(
    mut v___x_3462_: u8,
    mut v_toPure_3463_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3464_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_3464_ == 0 {
        let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3465_ = crate::leanh::lean_box((v___x_3462_) as usize);
        v___x_3466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3466_, 0, v___x_3465_);
        v___x_3467_ =
            crate::leanh::lean_apply_2(v_toPure_3463_, crate::leanh::lean_box(0), v___x_3466_);
        return v___x_3467_;
    } else {
        let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3468_ = crate::leanh::lean_box((v_____do__lift_3464_) as usize);
        v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3468_);
        v___x_3470_ =
            crate::leanh::lean_apply_2(v_toPure_3463_, crate::leanh::lean_box(0), v___x_3469_);
        return v___x_3470_;
    }
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__0___boxed(
    mut v___x_3471_: *mut crate::leanh::LeanObject,
    mut v_toPure_3472_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_203__boxed_3474_: u8 = 0;
    let mut v_____do__lift_204__boxed_3475_: u8 = 0;
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_203__boxed_3474_ = (crate::leanh::lean_unbox(v___x_3471_) as u8);
    v_____do__lift_204__boxed_3475_ = (crate::leanh::lean_unbox(v_____do__lift_3473_) as u8);
    v_res_3476_ = l_Std_IterM_anyM___redArg___lam__0(
        v___x_203__boxed_3474_,
        v_toPure_3472_,
        v_____do__lift_204__boxed_3475_,
    );
    return v_res_3476_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__2(
    mut v_p_3477_: *mut crate::leanh::LeanObject,
    mut v_toBind_3478_: *mut crate::leanh::LeanObject,
    mut v___f_3479_: *mut crate::leanh::LeanObject,
    mut v___f_3480_: *mut crate::leanh::LeanObject,
    mut v_x1_3481_: *mut crate::leanh::LeanObject,
    mut v_x2_3482_: *mut crate::leanh::LeanObject,
    mut v_x3_3483_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = crate::leanh::lean_apply_1(v_p_3477_, v_x1_3481_);
    crate::leanh::lean_inc(v_toBind_3478_);
    v___x_3485_ = crate::leanh::lean_apply_4(
        v_toBind_3478_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3484_,
        v___f_3479_,
    );
    v___x_3486_ = crate::leanh::lean_apply_4(
        v_toBind_3478_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3485_,
        v___f_3480_,
    );
    return v___x_3486_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__2___boxed(
    mut v_p_3487_: *mut crate::leanh::LeanObject,
    mut v_toBind_3488_: *mut crate::leanh::LeanObject,
    mut v___f_3489_: *mut crate::leanh::LeanObject,
    mut v___f_3490_: *mut crate::leanh::LeanObject,
    mut v_x1_3491_: *mut crate::leanh::LeanObject,
    mut v_x2_3492_: *mut crate::leanh::LeanObject,
    mut v_x3_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x3_225__boxed_3494_: u8 = 0;
    let mut v_res_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x3_225__boxed_3494_ = (crate::leanh::lean_unbox(v_x3_3493_) as u8);
    v_res_3495_ = l_Std_IterM_anyM___redArg___lam__2(
        v_p_3487_,
        v_toBind_3488_,
        v___f_3489_,
        v___f_3490_,
        v_x1_3491_,
        v_x2_3492_,
        v_x3_225__boxed_3494_,
    );
    return v_res_3495_;
}
pub unsafe fn l_Std_IterM_anyM___redArg(
    mut v_inst_3496_: *mut crate::leanh::LeanObject,
    mut v_inst_3497_: *mut crate::leanh::LeanObject,
    mut v_p_3498_: *mut crate::leanh::LeanObject,
    mut v_it_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3500_ = crate::leanh::lean_ctor_get(v_inst_3496_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3500_);
    v_toBind_3501_ = crate::leanh::lean_ctor_get(v_inst_3496_, 1);
    crate::leanh::lean_inc_n(v_toBind_3501_, 2);
    crate::leanh::lean_dec_ref(v_inst_3496_);
    v_toPure_3502_ = crate::leanh::lean_ctor_get(v_toApplicative_3500_, 1);
    crate::leanh::lean_inc_n(v_toPure_3502_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3500_);
    v___f_3503_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3503_, 0, v_toBind_3501_);
    v___f_3504_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3504_, 0, v_toPure_3502_);
    v___x_3505_ = 0;
    v___x_3506_ = crate::leanh::lean_box((v___x_3505_) as usize);
    v___f_3507_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3507_, 0, v___x_3506_);
    crate::leanh::lean_closure_set(v___f_3507_, 1, v_toPure_3502_);
    v___f_3508_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3508_, 0, v_p_3498_);
    crate::leanh::lean_closure_set(v___f_3508_, 1, v_toBind_3501_);
    crate::leanh::lean_closure_set(v___f_3508_, 2, v___f_3507_);
    crate::leanh::lean_closure_set(v___f_3508_, 3, v___f_3504_);
    v___x_3509_ = crate::leanh::lean_box((v___x_3505_) as usize);
    v___x_3510_ = crate::leanh::lean_apply_6(
        v_inst_3497_,
        v___f_3503_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3499_,
        v___x_3509_,
        v___f_3508_,
    );
    return v___x_3510_;
}
pub unsafe fn l_Std_IterM_anyM(
    mut v_00_u03b1_3511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3512_: *mut crate::leanh::LeanObject,
    mut v_m_3513_: *mut crate::leanh::LeanObject,
    mut v_inst_3514_: *mut crate::leanh::LeanObject,
    mut v_inst_3515_: *mut crate::leanh::LeanObject,
    mut v_inst_3516_: *mut crate::leanh::LeanObject,
    mut v_p_3517_: *mut crate::leanh::LeanObject,
    mut v_it_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Std_IterM_anyM___redArg(v_inst_3514_, v_inst_3516_, v_p_3517_, v_it_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Std_IterM_anyM___boxed(
    mut v_00_u03b1_3520_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3521_: *mut crate::leanh::LeanObject,
    mut v_m_3522_: *mut crate::leanh::LeanObject,
    mut v_inst_3523_: *mut crate::leanh::LeanObject,
    mut v_inst_3524_: *mut crate::leanh::LeanObject,
    mut v_inst_3525_: *mut crate::leanh::LeanObject,
    mut v_p_3526_: *mut crate::leanh::LeanObject,
    mut v_it_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3528_ = l_Std_IterM_anyM(
        v_00_u03b1_3520_,
        v_00_u03b2_3521_,
        v_m_3522_,
        v_inst_3523_,
        v_inst_3524_,
        v_inst_3525_,
        v_p_3526_,
        v_it_3527_,
    );
    crate::leanh::lean_dec(v_inst_3524_);
    return v_res_3528_;
}
pub unsafe fn l_Std_IterM_Partial_anyM___redArg(
    mut v_inst_3529_: *mut crate::leanh::LeanObject,
    mut v_inst_3530_: *mut crate::leanh::LeanObject,
    mut v_p_3531_: *mut crate::leanh::LeanObject,
    mut v_it_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3533_ = l_Std_IterM_anyM___redArg(v_inst_3529_, v_inst_3530_, v_p_3531_, v_it_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Std_IterM_Partial_anyM(
    mut v_00_u03b1_3534_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3535_: *mut crate::leanh::LeanObject,
    mut v_m_3536_: *mut crate::leanh::LeanObject,
    mut v_inst_3537_: *mut crate::leanh::LeanObject,
    mut v_inst_3538_: *mut crate::leanh::LeanObject,
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_p_3540_: *mut crate::leanh::LeanObject,
    mut v_it_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3542_ = l_Std_IterM_anyM___redArg(v_inst_3537_, v_inst_3539_, v_p_3540_, v_it_3541_);
    return v___x_3542_;
}
pub unsafe fn l_Std_IterM_Partial_anyM___boxed(
    mut v_00_u03b1_3543_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3544_: *mut crate::leanh::LeanObject,
    mut v_m_3545_: *mut crate::leanh::LeanObject,
    mut v_inst_3546_: *mut crate::leanh::LeanObject,
    mut v_inst_3547_: *mut crate::leanh::LeanObject,
    mut v_inst_3548_: *mut crate::leanh::LeanObject,
    mut v_p_3549_: *mut crate::leanh::LeanObject,
    mut v_it_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l_Std_IterM_Partial_anyM(
        v_00_u03b1_3543_,
        v_00_u03b2_3544_,
        v_m_3545_,
        v_inst_3546_,
        v_inst_3547_,
        v_inst_3548_,
        v_p_3549_,
        v_it_3550_,
    );
    crate::leanh::lean_dec(v_inst_3547_);
    return v_res_3551_;
}
pub unsafe fn l_Std_IterM_Total_anyM___redArg(
    mut v_inst_3552_: *mut crate::leanh::LeanObject,
    mut v_inst_3553_: *mut crate::leanh::LeanObject,
    mut v_p_3554_: *mut crate::leanh::LeanObject,
    mut v_it_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = l_Std_IterM_anyM___redArg(v_inst_3552_, v_inst_3553_, v_p_3554_, v_it_3555_);
    return v___x_3556_;
}
pub unsafe fn l_Std_IterM_Total_anyM(
    mut v_00_u03b1_3557_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3558_: *mut crate::leanh::LeanObject,
    mut v_m_3559_: *mut crate::leanh::LeanObject,
    mut v_inst_3560_: *mut crate::leanh::LeanObject,
    mut v_inst_3561_: *mut crate::leanh::LeanObject,
    mut v_inst_3562_: *mut crate::leanh::LeanObject,
    mut v_inst_3563_: *mut crate::leanh::LeanObject,
    mut v_p_3564_: *mut crate::leanh::LeanObject,
    mut v_it_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = l_Std_IterM_anyM___redArg(v_inst_3560_, v_inst_3562_, v_p_3564_, v_it_3565_);
    return v___x_3566_;
}
pub unsafe fn l_Std_IterM_Total_anyM___boxed(
    mut v_00_u03b1_3567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3568_: *mut crate::leanh::LeanObject,
    mut v_m_3569_: *mut crate::leanh::LeanObject,
    mut v_inst_3570_: *mut crate::leanh::LeanObject,
    mut v_inst_3571_: *mut crate::leanh::LeanObject,
    mut v_inst_3572_: *mut crate::leanh::LeanObject,
    mut v_inst_3573_: *mut crate::leanh::LeanObject,
    mut v_p_3574_: *mut crate::leanh::LeanObject,
    mut v_it_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3576_ = l_Std_IterM_Total_anyM(
        v_00_u03b1_3567_,
        v_00_u03b2_3568_,
        v_m_3569_,
        v_inst_3570_,
        v_inst_3571_,
        v_inst_3572_,
        v_inst_3573_,
        v_p_3574_,
        v_it_3575_,
    );
    crate::leanh::lean_dec(v_inst_3571_);
    return v_res_3576_;
}
pub unsafe fn l_Std_IterM_any___redArg___lam__0(
    mut v_p_3577_: *mut crate::leanh::LeanObject,
    mut v_toPure_3578_: *mut crate::leanh::LeanObject,
    mut v_x_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = crate::leanh::lean_apply_1(v_p_3577_, v_x_3579_);
    v___x_3581_ =
        crate::leanh::lean_apply_2(v_toPure_3578_, crate::leanh::lean_box(0), v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn l_Std_IterM_any___redArg(
    mut v_inst_3582_: *mut crate::leanh::LeanObject,
    mut v_inst_3583_: *mut crate::leanh::LeanObject,
    mut v_p_3584_: *mut crate::leanh::LeanObject,
    mut v_it_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3586_ = crate::leanh::lean_ctor_get(v_inst_3582_, 0);
    v_toPure_3587_ = crate::leanh::lean_ctor_get(v_toApplicative_3586_, 1);
    crate::leanh::lean_inc(v_toPure_3587_);
    v___f_3588_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3588_, 0, v_p_3584_);
    crate::leanh::lean_closure_set(v___f_3588_, 1, v_toPure_3587_);
    v___x_3589_ = l_Std_IterM_anyM___redArg(v_inst_3582_, v_inst_3583_, v___f_3588_, v_it_3585_);
    return v___x_3589_;
}
pub unsafe fn l_Std_IterM_any(
    mut v_00_u03b1_3590_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3591_: *mut crate::leanh::LeanObject,
    mut v_m_3592_: *mut crate::leanh::LeanObject,
    mut v_inst_3593_: *mut crate::leanh::LeanObject,
    mut v_inst_3594_: *mut crate::leanh::LeanObject,
    mut v_inst_3595_: *mut crate::leanh::LeanObject,
    mut v_p_3596_: *mut crate::leanh::LeanObject,
    mut v_it_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3598_ = crate::leanh::lean_ctor_get(v_inst_3593_, 0);
    v_toPure_3599_ = crate::leanh::lean_ctor_get(v_toApplicative_3598_, 1);
    crate::leanh::lean_inc(v_toPure_3599_);
    v___f_3600_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3600_, 0, v_p_3596_);
    crate::leanh::lean_closure_set(v___f_3600_, 1, v_toPure_3599_);
    v___x_3601_ = l_Std_IterM_anyM___redArg(v_inst_3593_, v_inst_3595_, v___f_3600_, v_it_3597_);
    return v___x_3601_;
}
pub unsafe fn l_Std_IterM_any___boxed(
    mut v_00_u03b1_3602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3603_: *mut crate::leanh::LeanObject,
    mut v_m_3604_: *mut crate::leanh::LeanObject,
    mut v_inst_3605_: *mut crate::leanh::LeanObject,
    mut v_inst_3606_: *mut crate::leanh::LeanObject,
    mut v_inst_3607_: *mut crate::leanh::LeanObject,
    mut v_p_3608_: *mut crate::leanh::LeanObject,
    mut v_it_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3610_ = l_Std_IterM_any(
        v_00_u03b1_3602_,
        v_00_u03b2_3603_,
        v_m_3604_,
        v_inst_3605_,
        v_inst_3606_,
        v_inst_3607_,
        v_p_3608_,
        v_it_3609_,
    );
    crate::leanh::lean_dec(v_inst_3606_);
    return v_res_3610_;
}
pub unsafe fn l_Std_IterM_Partial_any___redArg(
    mut v_inst_3611_: *mut crate::leanh::LeanObject,
    mut v_inst_3612_: *mut crate::leanh::LeanObject,
    mut v_p_3613_: *mut crate::leanh::LeanObject,
    mut v_it_3614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3615_ = crate::leanh::lean_ctor_get(v_inst_3611_, 0);
    v_toPure_3616_ = crate::leanh::lean_ctor_get(v_toApplicative_3615_, 1);
    crate::leanh::lean_inc(v_toPure_3616_);
    v___f_3617_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3617_, 0, v_p_3613_);
    crate::leanh::lean_closure_set(v___f_3617_, 1, v_toPure_3616_);
    v___x_3618_ = l_Std_IterM_anyM___redArg(v_inst_3611_, v_inst_3612_, v___f_3617_, v_it_3614_);
    return v___x_3618_;
}
pub unsafe fn l_Std_IterM_Partial_any(
    mut v_00_u03b1_3619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3620_: *mut crate::leanh::LeanObject,
    mut v_m_3621_: *mut crate::leanh::LeanObject,
    mut v_inst_3622_: *mut crate::leanh::LeanObject,
    mut v_inst_3623_: *mut crate::leanh::LeanObject,
    mut v_inst_3624_: *mut crate::leanh::LeanObject,
    mut v_p_3625_: *mut crate::leanh::LeanObject,
    mut v_it_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3627_ = crate::leanh::lean_ctor_get(v_inst_3622_, 0);
    v_toPure_3628_ = crate::leanh::lean_ctor_get(v_toApplicative_3627_, 1);
    crate::leanh::lean_inc(v_toPure_3628_);
    v___f_3629_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3629_, 0, v_p_3625_);
    crate::leanh::lean_closure_set(v___f_3629_, 1, v_toPure_3628_);
    v___x_3630_ = l_Std_IterM_anyM___redArg(v_inst_3622_, v_inst_3624_, v___f_3629_, v_it_3626_);
    return v___x_3630_;
}
pub unsafe fn l_Std_IterM_Partial_any___boxed(
    mut v_00_u03b1_3631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3632_: *mut crate::leanh::LeanObject,
    mut v_m_3633_: *mut crate::leanh::LeanObject,
    mut v_inst_3634_: *mut crate::leanh::LeanObject,
    mut v_inst_3635_: *mut crate::leanh::LeanObject,
    mut v_inst_3636_: *mut crate::leanh::LeanObject,
    mut v_p_3637_: *mut crate::leanh::LeanObject,
    mut v_it_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Std_IterM_Partial_any(
        v_00_u03b1_3631_,
        v_00_u03b2_3632_,
        v_m_3633_,
        v_inst_3634_,
        v_inst_3635_,
        v_inst_3636_,
        v_p_3637_,
        v_it_3638_,
    );
    crate::leanh::lean_dec(v_inst_3635_);
    return v_res_3639_;
}
pub unsafe fn l_Std_IterM_Total_any___redArg(
    mut v_inst_3640_: *mut crate::leanh::LeanObject,
    mut v_inst_3641_: *mut crate::leanh::LeanObject,
    mut v_p_3642_: *mut crate::leanh::LeanObject,
    mut v_it_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3644_ = crate::leanh::lean_ctor_get(v_inst_3640_, 0);
    v_toPure_3645_ = crate::leanh::lean_ctor_get(v_toApplicative_3644_, 1);
    crate::leanh::lean_inc(v_toPure_3645_);
    v___f_3646_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3646_, 0, v_p_3642_);
    crate::leanh::lean_closure_set(v___f_3646_, 1, v_toPure_3645_);
    v___x_3647_ = l_Std_IterM_anyM___redArg(v_inst_3640_, v_inst_3641_, v___f_3646_, v_it_3643_);
    return v___x_3647_;
}
pub unsafe fn l_Std_IterM_Total_any(
    mut v_00_u03b1_3648_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3649_: *mut crate::leanh::LeanObject,
    mut v_m_3650_: *mut crate::leanh::LeanObject,
    mut v_inst_3651_: *mut crate::leanh::LeanObject,
    mut v_inst_3652_: *mut crate::leanh::LeanObject,
    mut v_inst_3653_: *mut crate::leanh::LeanObject,
    mut v_inst_3654_: *mut crate::leanh::LeanObject,
    mut v_p_3655_: *mut crate::leanh::LeanObject,
    mut v_it_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3657_ = crate::leanh::lean_ctor_get(v_inst_3651_, 0);
    v_toPure_3658_ = crate::leanh::lean_ctor_get(v_toApplicative_3657_, 1);
    crate::leanh::lean_inc(v_toPure_3658_);
    v___f_3659_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3659_, 0, v_p_3655_);
    crate::leanh::lean_closure_set(v___f_3659_, 1, v_toPure_3658_);
    v___x_3660_ = l_Std_IterM_anyM___redArg(v_inst_3651_, v_inst_3653_, v___f_3659_, v_it_3656_);
    return v___x_3660_;
}
pub unsafe fn l_Std_IterM_Total_any___boxed(
    mut v_00_u03b1_3661_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3662_: *mut crate::leanh::LeanObject,
    mut v_m_3663_: *mut crate::leanh::LeanObject,
    mut v_inst_3664_: *mut crate::leanh::LeanObject,
    mut v_inst_3665_: *mut crate::leanh::LeanObject,
    mut v_inst_3666_: *mut crate::leanh::LeanObject,
    mut v_inst_3667_: *mut crate::leanh::LeanObject,
    mut v_p_3668_: *mut crate::leanh::LeanObject,
    mut v_it_3669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3670_ = l_Std_IterM_Total_any(
        v_00_u03b1_3661_,
        v_00_u03b2_3662_,
        v_m_3663_,
        v_inst_3664_,
        v_inst_3665_,
        v_inst_3666_,
        v_inst_3667_,
        v_p_3668_,
        v_it_3669_,
    );
    crate::leanh::lean_dec(v_inst_3665_);
    return v_res_3670_;
}
pub unsafe fn l_Std_IterM_allM___redArg___lam__2(
    mut v_toPure_3671_: *mut crate::leanh::LeanObject,
    mut v___x_3672_: u8,
    mut v_____do__lift_3673_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_3673_ == 0 {
        let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3674_ = crate::leanh::lean_box((v_____do__lift_3673_) as usize);
        v___x_3675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3675_, 0, v___x_3674_);
        v___x_3676_ =
            crate::leanh::lean_apply_2(v_toPure_3671_, crate::leanh::lean_box(0), v___x_3675_);
        return v___x_3676_;
    } else {
        let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3677_ = crate::leanh::lean_box((v___x_3672_) as usize);
        v___x_3678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
        v___x_3679_ =
            crate::leanh::lean_apply_2(v_toPure_3671_, crate::leanh::lean_box(0), v___x_3678_);
        return v___x_3679_;
    }
}
pub unsafe fn l_Std_IterM_allM___redArg___lam__2___boxed(
    mut v_toPure_3680_: *mut crate::leanh::LeanObject,
    mut v___x_3681_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_201__boxed_3683_: u8 = 0;
    let mut v_____do__lift_202__boxed_3684_: u8 = 0;
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_201__boxed_3683_ = (crate::leanh::lean_unbox(v___x_3681_) as u8);
    v_____do__lift_202__boxed_3684_ = (crate::leanh::lean_unbox(v_____do__lift_3682_) as u8);
    v_res_3685_ = l_Std_IterM_allM___redArg___lam__2(
        v_toPure_3680_,
        v___x_201__boxed_3683_,
        v_____do__lift_202__boxed_3684_,
    );
    return v_res_3685_;
}
pub unsafe fn l_Std_IterM_allM___redArg(
    mut v_inst_3686_: *mut crate::leanh::LeanObject,
    mut v_inst_3687_: *mut crate::leanh::LeanObject,
    mut v_p_3688_: *mut crate::leanh::LeanObject,
    mut v_it_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3690_ = crate::leanh::lean_ctor_get(v_inst_3686_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3690_);
    v_toBind_3691_ = crate::leanh::lean_ctor_get(v_inst_3686_, 1);
    crate::leanh::lean_inc_n(v_toBind_3691_, 2);
    crate::leanh::lean_dec_ref(v_inst_3686_);
    v_toPure_3692_ = crate::leanh::lean_ctor_get(v_toApplicative_3690_, 1);
    crate::leanh::lean_inc_n(v_toPure_3692_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3690_);
    v___f_3693_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3693_, 0, v_toBind_3691_);
    v___f_3694_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3694_, 0, v_toPure_3692_);
    v___x_3695_ = 1;
    v___x_3696_ = crate::leanh::lean_box((v___x_3695_) as usize);
    v___f_3697_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_allM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3697_, 0, v_toPure_3692_);
    crate::leanh::lean_closure_set(v___f_3697_, 1, v___x_3696_);
    v___f_3698_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3698_, 0, v_p_3688_);
    crate::leanh::lean_closure_set(v___f_3698_, 1, v_toBind_3691_);
    crate::leanh::lean_closure_set(v___f_3698_, 2, v___f_3697_);
    crate::leanh::lean_closure_set(v___f_3698_, 3, v___f_3694_);
    v___x_3699_ = crate::leanh::lean_box((v___x_3695_) as usize);
    v___x_3700_ = crate::leanh::lean_apply_6(
        v_inst_3687_,
        v___f_3693_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3689_,
        v___x_3699_,
        v___f_3698_,
    );
    return v___x_3700_;
}
pub unsafe fn l_Std_IterM_allM(
    mut v_00_u03b1_3701_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3702_: *mut crate::leanh::LeanObject,
    mut v_m_3703_: *mut crate::leanh::LeanObject,
    mut v_inst_3704_: *mut crate::leanh::LeanObject,
    mut v_inst_3705_: *mut crate::leanh::LeanObject,
    mut v_inst_3706_: *mut crate::leanh::LeanObject,
    mut v_p_3707_: *mut crate::leanh::LeanObject,
    mut v_it_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3709_ = l_Std_IterM_allM___redArg(v_inst_3704_, v_inst_3706_, v_p_3707_, v_it_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Std_IterM_allM___boxed(
    mut v_00_u03b1_3710_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3711_: *mut crate::leanh::LeanObject,
    mut v_m_3712_: *mut crate::leanh::LeanObject,
    mut v_inst_3713_: *mut crate::leanh::LeanObject,
    mut v_inst_3714_: *mut crate::leanh::LeanObject,
    mut v_inst_3715_: *mut crate::leanh::LeanObject,
    mut v_p_3716_: *mut crate::leanh::LeanObject,
    mut v_it_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3718_ = l_Std_IterM_allM(
        v_00_u03b1_3710_,
        v_00_u03b2_3711_,
        v_m_3712_,
        v_inst_3713_,
        v_inst_3714_,
        v_inst_3715_,
        v_p_3716_,
        v_it_3717_,
    );
    crate::leanh::lean_dec(v_inst_3714_);
    return v_res_3718_;
}
pub unsafe fn l_Std_IterM_Partial_allM___redArg(
    mut v_inst_3719_: *mut crate::leanh::LeanObject,
    mut v_inst_3720_: *mut crate::leanh::LeanObject,
    mut v_p_3721_: *mut crate::leanh::LeanObject,
    mut v_it_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_Std_IterM_allM___redArg(v_inst_3719_, v_inst_3720_, v_p_3721_, v_it_3722_);
    return v___x_3723_;
}
pub unsafe fn l_Std_IterM_Partial_allM(
    mut v_00_u03b1_3724_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3725_: *mut crate::leanh::LeanObject,
    mut v_m_3726_: *mut crate::leanh::LeanObject,
    mut v_inst_3727_: *mut crate::leanh::LeanObject,
    mut v_inst_3728_: *mut crate::leanh::LeanObject,
    mut v_inst_3729_: *mut crate::leanh::LeanObject,
    mut v_p_3730_: *mut crate::leanh::LeanObject,
    mut v_it_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = l_Std_IterM_allM___redArg(v_inst_3727_, v_inst_3729_, v_p_3730_, v_it_3731_);
    return v___x_3732_;
}
pub unsafe fn l_Std_IterM_Partial_allM___boxed(
    mut v_00_u03b1_3733_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3734_: *mut crate::leanh::LeanObject,
    mut v_m_3735_: *mut crate::leanh::LeanObject,
    mut v_inst_3736_: *mut crate::leanh::LeanObject,
    mut v_inst_3737_: *mut crate::leanh::LeanObject,
    mut v_inst_3738_: *mut crate::leanh::LeanObject,
    mut v_p_3739_: *mut crate::leanh::LeanObject,
    mut v_it_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Std_IterM_Partial_allM(
        v_00_u03b1_3733_,
        v_00_u03b2_3734_,
        v_m_3735_,
        v_inst_3736_,
        v_inst_3737_,
        v_inst_3738_,
        v_p_3739_,
        v_it_3740_,
    );
    crate::leanh::lean_dec(v_inst_3737_);
    return v_res_3741_;
}
pub unsafe fn l_Std_IterM_Total_allM___redArg(
    mut v_inst_3742_: *mut crate::leanh::LeanObject,
    mut v_inst_3743_: *mut crate::leanh::LeanObject,
    mut v_p_3744_: *mut crate::leanh::LeanObject,
    mut v_it_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Std_IterM_allM___redArg(v_inst_3742_, v_inst_3743_, v_p_3744_, v_it_3745_);
    return v___x_3746_;
}
pub unsafe fn l_Std_IterM_Total_allM(
    mut v_00_u03b1_3747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3748_: *mut crate::leanh::LeanObject,
    mut v_m_3749_: *mut crate::leanh::LeanObject,
    mut v_inst_3750_: *mut crate::leanh::LeanObject,
    mut v_inst_3751_: *mut crate::leanh::LeanObject,
    mut v_inst_3752_: *mut crate::leanh::LeanObject,
    mut v_inst_3753_: *mut crate::leanh::LeanObject,
    mut v_p_3754_: *mut crate::leanh::LeanObject,
    mut v_it_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3756_ = l_Std_IterM_allM___redArg(v_inst_3750_, v_inst_3752_, v_p_3754_, v_it_3755_);
    return v___x_3756_;
}
pub unsafe fn l_Std_IterM_Total_allM___boxed(
    mut v_00_u03b1_3757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3758_: *mut crate::leanh::LeanObject,
    mut v_m_3759_: *mut crate::leanh::LeanObject,
    mut v_inst_3760_: *mut crate::leanh::LeanObject,
    mut v_inst_3761_: *mut crate::leanh::LeanObject,
    mut v_inst_3762_: *mut crate::leanh::LeanObject,
    mut v_inst_3763_: *mut crate::leanh::LeanObject,
    mut v_p_3764_: *mut crate::leanh::LeanObject,
    mut v_it_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l_Std_IterM_Total_allM(
        v_00_u03b1_3757_,
        v_00_u03b2_3758_,
        v_m_3759_,
        v_inst_3760_,
        v_inst_3761_,
        v_inst_3762_,
        v_inst_3763_,
        v_p_3764_,
        v_it_3765_,
    );
    crate::leanh::lean_dec(v_inst_3761_);
    return v_res_3766_;
}
pub unsafe fn l_Std_IterM_all___redArg(
    mut v_inst_3767_: *mut crate::leanh::LeanObject,
    mut v_inst_3768_: *mut crate::leanh::LeanObject,
    mut v_p_3769_: *mut crate::leanh::LeanObject,
    mut v_it_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3771_ = crate::leanh::lean_ctor_get(v_inst_3767_, 0);
    v_toPure_3772_ = crate::leanh::lean_ctor_get(v_toApplicative_3771_, 1);
    crate::leanh::lean_inc(v_toPure_3772_);
    v___f_3773_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3773_, 0, v_p_3769_);
    crate::leanh::lean_closure_set(v___f_3773_, 1, v_toPure_3772_);
    v___x_3774_ = l_Std_IterM_allM___redArg(v_inst_3767_, v_inst_3768_, v___f_3773_, v_it_3770_);
    return v___x_3774_;
}
pub unsafe fn l_Std_IterM_all(
    mut v_00_u03b1_3775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3776_: *mut crate::leanh::LeanObject,
    mut v_m_3777_: *mut crate::leanh::LeanObject,
    mut v_inst_3778_: *mut crate::leanh::LeanObject,
    mut v_inst_3779_: *mut crate::leanh::LeanObject,
    mut v_inst_3780_: *mut crate::leanh::LeanObject,
    mut v_p_3781_: *mut crate::leanh::LeanObject,
    mut v_it_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3783_ = crate::leanh::lean_ctor_get(v_inst_3778_, 0);
    v_toPure_3784_ = crate::leanh::lean_ctor_get(v_toApplicative_3783_, 1);
    crate::leanh::lean_inc(v_toPure_3784_);
    v___f_3785_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3785_, 0, v_p_3781_);
    crate::leanh::lean_closure_set(v___f_3785_, 1, v_toPure_3784_);
    v___x_3786_ = l_Std_IterM_allM___redArg(v_inst_3778_, v_inst_3780_, v___f_3785_, v_it_3782_);
    return v___x_3786_;
}
pub unsafe fn l_Std_IterM_all___boxed(
    mut v_00_u03b1_3787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3788_: *mut crate::leanh::LeanObject,
    mut v_m_3789_: *mut crate::leanh::LeanObject,
    mut v_inst_3790_: *mut crate::leanh::LeanObject,
    mut v_inst_3791_: *mut crate::leanh::LeanObject,
    mut v_inst_3792_: *mut crate::leanh::LeanObject,
    mut v_p_3793_: *mut crate::leanh::LeanObject,
    mut v_it_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Std_IterM_all(
        v_00_u03b1_3787_,
        v_00_u03b2_3788_,
        v_m_3789_,
        v_inst_3790_,
        v_inst_3791_,
        v_inst_3792_,
        v_p_3793_,
        v_it_3794_,
    );
    crate::leanh::lean_dec(v_inst_3791_);
    return v_res_3795_;
}
pub unsafe fn l_Std_IterM_Partial_all___redArg(
    mut v_inst_3796_: *mut crate::leanh::LeanObject,
    mut v_inst_3797_: *mut crate::leanh::LeanObject,
    mut v_p_3798_: *mut crate::leanh::LeanObject,
    mut v_it_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3800_ = crate::leanh::lean_ctor_get(v_inst_3796_, 0);
    v_toPure_3801_ = crate::leanh::lean_ctor_get(v_toApplicative_3800_, 1);
    crate::leanh::lean_inc(v_toPure_3801_);
    v___f_3802_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3802_, 0, v_p_3798_);
    crate::leanh::lean_closure_set(v___f_3802_, 1, v_toPure_3801_);
    v___x_3803_ = l_Std_IterM_allM___redArg(v_inst_3796_, v_inst_3797_, v___f_3802_, v_it_3799_);
    return v___x_3803_;
}
pub unsafe fn l_Std_IterM_Partial_all(
    mut v_00_u03b1_3804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3805_: *mut crate::leanh::LeanObject,
    mut v_m_3806_: *mut crate::leanh::LeanObject,
    mut v_inst_3807_: *mut crate::leanh::LeanObject,
    mut v_inst_3808_: *mut crate::leanh::LeanObject,
    mut v_inst_3809_: *mut crate::leanh::LeanObject,
    mut v_p_3810_: *mut crate::leanh::LeanObject,
    mut v_it_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3812_ = crate::leanh::lean_ctor_get(v_inst_3807_, 0);
    v_toPure_3813_ = crate::leanh::lean_ctor_get(v_toApplicative_3812_, 1);
    crate::leanh::lean_inc(v_toPure_3813_);
    v___f_3814_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3814_, 0, v_p_3810_);
    crate::leanh::lean_closure_set(v___f_3814_, 1, v_toPure_3813_);
    v___x_3815_ = l_Std_IterM_allM___redArg(v_inst_3807_, v_inst_3809_, v___f_3814_, v_it_3811_);
    return v___x_3815_;
}
pub unsafe fn l_Std_IterM_Partial_all___boxed(
    mut v_00_u03b1_3816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3817_: *mut crate::leanh::LeanObject,
    mut v_m_3818_: *mut crate::leanh::LeanObject,
    mut v_inst_3819_: *mut crate::leanh::LeanObject,
    mut v_inst_3820_: *mut crate::leanh::LeanObject,
    mut v_inst_3821_: *mut crate::leanh::LeanObject,
    mut v_p_3822_: *mut crate::leanh::LeanObject,
    mut v_it_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_Std_IterM_Partial_all(
        v_00_u03b1_3816_,
        v_00_u03b2_3817_,
        v_m_3818_,
        v_inst_3819_,
        v_inst_3820_,
        v_inst_3821_,
        v_p_3822_,
        v_it_3823_,
    );
    crate::leanh::lean_dec(v_inst_3820_);
    return v_res_3824_;
}
pub unsafe fn l_Std_IterM_Total_all___redArg(
    mut v_inst_3825_: *mut crate::leanh::LeanObject,
    mut v_inst_3826_: *mut crate::leanh::LeanObject,
    mut v_p_3827_: *mut crate::leanh::LeanObject,
    mut v_it_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3829_ = crate::leanh::lean_ctor_get(v_inst_3825_, 0);
    v_toPure_3830_ = crate::leanh::lean_ctor_get(v_toApplicative_3829_, 1);
    crate::leanh::lean_inc(v_toPure_3830_);
    v___f_3831_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3831_, 0, v_p_3827_);
    crate::leanh::lean_closure_set(v___f_3831_, 1, v_toPure_3830_);
    v___x_3832_ = l_Std_IterM_allM___redArg(v_inst_3825_, v_inst_3826_, v___f_3831_, v_it_3828_);
    return v___x_3832_;
}
pub unsafe fn l_Std_IterM_Total_all(
    mut v_00_u03b1_3833_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3834_: *mut crate::leanh::LeanObject,
    mut v_m_3835_: *mut crate::leanh::LeanObject,
    mut v_inst_3836_: *mut crate::leanh::LeanObject,
    mut v_inst_3837_: *mut crate::leanh::LeanObject,
    mut v_inst_3838_: *mut crate::leanh::LeanObject,
    mut v_inst_3839_: *mut crate::leanh::LeanObject,
    mut v_p_3840_: *mut crate::leanh::LeanObject,
    mut v_it_3841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3842_ = crate::leanh::lean_ctor_get(v_inst_3836_, 0);
    v_toPure_3843_ = crate::leanh::lean_ctor_get(v_toApplicative_3842_, 1);
    crate::leanh::lean_inc(v_toPure_3843_);
    v___f_3844_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3844_, 0, v_p_3840_);
    crate::leanh::lean_closure_set(v___f_3844_, 1, v_toPure_3843_);
    v___x_3845_ = l_Std_IterM_allM___redArg(v_inst_3836_, v_inst_3838_, v___f_3844_, v_it_3841_);
    return v___x_3845_;
}
pub unsafe fn l_Std_IterM_Total_all___boxed(
    mut v_00_u03b1_3846_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3847_: *mut crate::leanh::LeanObject,
    mut v_m_3848_: *mut crate::leanh::LeanObject,
    mut v_inst_3849_: *mut crate::leanh::LeanObject,
    mut v_inst_3850_: *mut crate::leanh::LeanObject,
    mut v_inst_3851_: *mut crate::leanh::LeanObject,
    mut v_inst_3852_: *mut crate::leanh::LeanObject,
    mut v_p_3853_: *mut crate::leanh::LeanObject,
    mut v_it_3854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3855_ = l_Std_IterM_Total_all(
        v_00_u03b1_3846_,
        v_00_u03b2_3847_,
        v_m_3848_,
        v_inst_3849_,
        v_inst_3850_,
        v_inst_3851_,
        v_inst_3852_,
        v_p_3853_,
        v_it_3854_,
    );
    crate::leanh::lean_dec(v_inst_3850_);
    return v_res_3855_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__1(
    mut v_toPure_3856_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = crate::leanh::lean_apply_2(
        v_toPure_3856_,
        crate::leanh::lean_box(0),
        v_____do__lift_3857_,
    );
    return v___x_3858_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__0(
    mut v___x_3859_: *mut crate::leanh::LeanObject,
    mut v_toPure_3860_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_3861_) == 0 {
        let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3862_, 0, v___x_3859_);
        v___x_3863_ =
            crate::leanh::lean_apply_2(v_toPure_3860_, crate::leanh::lean_box(0), v___x_3862_);
        return v___x_3863_;
    } else {
        let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3859_);
        v___x_3864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3864_, 0, v_____do__lift_3861_);
        v___x_3865_ =
            crate::leanh::lean_apply_2(v_toPure_3860_, crate::leanh::lean_box(0), v___x_3864_);
        return v___x_3865_;
    }
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__2(
    mut v_f_3866_: *mut crate::leanh::LeanObject,
    mut v_toBind_3867_: *mut crate::leanh::LeanObject,
    mut v___f_3868_: *mut crate::leanh::LeanObject,
    mut v___f_3869_: *mut crate::leanh::LeanObject,
    mut v_x1_3870_: *mut crate::leanh::LeanObject,
    mut v_x2_3871_: *mut crate::leanh::LeanObject,
    mut v_x3_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = crate::leanh::lean_apply_1(v_f_3866_, v_x1_3870_);
    crate::leanh::lean_inc(v_toBind_3867_);
    v___x_3874_ = crate::leanh::lean_apply_4(
        v_toBind_3867_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3873_,
        v___f_3868_,
    );
    v___x_3875_ = crate::leanh::lean_apply_4(
        v_toBind_3867_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3874_,
        v___f_3869_,
    );
    return v___x_3875_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(
    mut v_f_3876_: *mut crate::leanh::LeanObject,
    mut v_toBind_3877_: *mut crate::leanh::LeanObject,
    mut v___f_3878_: *mut crate::leanh::LeanObject,
    mut v___f_3879_: *mut crate::leanh::LeanObject,
    mut v_x1_3880_: *mut crate::leanh::LeanObject,
    mut v_x2_3881_: *mut crate::leanh::LeanObject,
    mut v_x3_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3883_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(
        v_f_3876_,
        v_toBind_3877_,
        v___f_3878_,
        v___f_3879_,
        v_x1_3880_,
        v_x2_3881_,
        v_x3_3882_,
    );
    crate::leanh::lean_dec(v_x3_3882_);
    return v_res_3883_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg(
    mut v_inst_3884_: *mut crate::leanh::LeanObject,
    mut v_inst_3885_: *mut crate::leanh::LeanObject,
    mut v_it_3886_: *mut crate::leanh::LeanObject,
    mut v_f_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3888_ = crate::leanh::lean_ctor_get(v_inst_3884_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3888_);
    v_toBind_3889_ = crate::leanh::lean_ctor_get(v_inst_3884_, 1);
    crate::leanh::lean_inc_n(v_toBind_3889_, 2);
    crate::leanh::lean_dec_ref(v_inst_3884_);
    v_toPure_3890_ = crate::leanh::lean_ctor_get(v_toApplicative_3888_, 1);
    crate::leanh::lean_inc_n(v_toPure_3890_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3888_);
    v___f_3891_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3891_, 0, v_toBind_3889_);
    v___f_3892_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3892_, 0, v_toPure_3890_);
    v___x_3893_ = crate::leanh::lean_box(0);
    v___f_3894_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3894_, 0, v___x_3893_);
    crate::leanh::lean_closure_set(v___f_3894_, 1, v_toPure_3890_);
    v___f_3895_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3895_, 0, v_f_3887_);
    crate::leanh::lean_closure_set(v___f_3895_, 1, v_toBind_3889_);
    crate::leanh::lean_closure_set(v___f_3895_, 2, v___f_3894_);
    crate::leanh::lean_closure_set(v___f_3895_, 3, v___f_3892_);
    v___x_3896_ = crate::leanh::lean_apply_6(
        v_inst_3885_,
        v___f_3891_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3886_,
        v___x_3893_,
        v___f_3895_,
    );
    return v___x_3896_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f(
    mut v_00_u03b1_3897_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3898_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3899_: *mut crate::leanh::LeanObject,
    mut v_m_3900_: *mut crate::leanh::LeanObject,
    mut v_inst_3901_: *mut crate::leanh::LeanObject,
    mut v_inst_3902_: *mut crate::leanh::LeanObject,
    mut v_inst_3903_: *mut crate::leanh::LeanObject,
    mut v_it_3904_: *mut crate::leanh::LeanObject,
    mut v_f_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3906_ = crate::leanh::lean_ctor_get(v_inst_3901_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3906_);
    v_toBind_3907_ = crate::leanh::lean_ctor_get(v_inst_3901_, 1);
    crate::leanh::lean_inc_n(v_toBind_3907_, 2);
    crate::leanh::lean_dec_ref(v_inst_3901_);
    v_toPure_3908_ = crate::leanh::lean_ctor_get(v_toApplicative_3906_, 1);
    crate::leanh::lean_inc_n(v_toPure_3908_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3906_);
    v___f_3909_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3909_, 0, v_toBind_3907_);
    v___f_3910_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3910_, 0, v_toPure_3908_);
    v___x_3911_ = crate::leanh::lean_box(0);
    v___f_3912_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3912_, 0, v___x_3911_);
    crate::leanh::lean_closure_set(v___f_3912_, 1, v_toPure_3908_);
    v___f_3913_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3913_, 0, v_f_3905_);
    crate::leanh::lean_closure_set(v___f_3913_, 1, v_toBind_3907_);
    crate::leanh::lean_closure_set(v___f_3913_, 2, v___f_3912_);
    crate::leanh::lean_closure_set(v___f_3913_, 3, v___f_3910_);
    v___x_3914_ = crate::leanh::lean_apply_6(
        v_inst_3903_,
        v___f_3909_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3904_,
        v___x_3911_,
        v___f_3913_,
    );
    return v___x_3914_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___boxed(
    mut v_00_u03b1_3915_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3917_: *mut crate::leanh::LeanObject,
    mut v_m_3918_: *mut crate::leanh::LeanObject,
    mut v_inst_3919_: *mut crate::leanh::LeanObject,
    mut v_inst_3920_: *mut crate::leanh::LeanObject,
    mut v_inst_3921_: *mut crate::leanh::LeanObject,
    mut v_it_3922_: *mut crate::leanh::LeanObject,
    mut v_f_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3924_ = l_Std_IterM_findSomeM_x3f(
        v_00_u03b1_3915_,
        v_00_u03b2_3916_,
        v_00_u03b3_3917_,
        v_m_3918_,
        v_inst_3919_,
        v_inst_3920_,
        v_inst_3921_,
        v_it_3922_,
        v_f_3923_,
    );
    crate::leanh::lean_dec(v_inst_3920_);
    return v_res_3924_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f___redArg(
    mut v_inst_3925_: *mut crate::leanh::LeanObject,
    mut v_inst_3926_: *mut crate::leanh::LeanObject,
    mut v_it_3927_: *mut crate::leanh::LeanObject,
    mut v_f_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3929_ = crate::leanh::lean_ctor_get(v_inst_3925_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3929_);
    v_toBind_3930_ = crate::leanh::lean_ctor_get(v_inst_3925_, 1);
    crate::leanh::lean_inc_n(v_toBind_3930_, 2);
    crate::leanh::lean_dec_ref(v_inst_3925_);
    v_toPure_3931_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 1);
    crate::leanh::lean_inc_n(v_toPure_3931_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3929_);
    v___f_3932_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3932_, 0, v_toBind_3930_);
    v___f_3933_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3933_, 0, v_toPure_3931_);
    v___x_3934_ = crate::leanh::lean_box(0);
    v___f_3935_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3935_, 0, v___x_3934_);
    crate::leanh::lean_closure_set(v___f_3935_, 1, v_toPure_3931_);
    v___f_3936_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3936_, 0, v_f_3928_);
    crate::leanh::lean_closure_set(v___f_3936_, 1, v_toBind_3930_);
    crate::leanh::lean_closure_set(v___f_3936_, 2, v___f_3935_);
    crate::leanh::lean_closure_set(v___f_3936_, 3, v___f_3933_);
    v___x_3937_ = crate::leanh::lean_apply_6(
        v_inst_3926_,
        v___f_3932_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3927_,
        v___x_3934_,
        v___f_3936_,
    );
    return v___x_3937_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f(
    mut v_00_u03b1_3938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3939_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3940_: *mut crate::leanh::LeanObject,
    mut v_m_3941_: *mut crate::leanh::LeanObject,
    mut v_inst_3942_: *mut crate::leanh::LeanObject,
    mut v_inst_3943_: *mut crate::leanh::LeanObject,
    mut v_inst_3944_: *mut crate::leanh::LeanObject,
    mut v_it_3945_: *mut crate::leanh::LeanObject,
    mut v_f_3946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3947_ = crate::leanh::lean_ctor_get(v_inst_3942_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3947_);
    v_toBind_3948_ = crate::leanh::lean_ctor_get(v_inst_3942_, 1);
    crate::leanh::lean_inc_n(v_toBind_3948_, 2);
    crate::leanh::lean_dec_ref(v_inst_3942_);
    v_toPure_3949_ = crate::leanh::lean_ctor_get(v_toApplicative_3947_, 1);
    crate::leanh::lean_inc_n(v_toPure_3949_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3947_);
    v___f_3950_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3950_, 0, v_toBind_3948_);
    v___f_3951_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3951_, 0, v_toPure_3949_);
    v___x_3952_ = crate::leanh::lean_box(0);
    v___f_3953_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3953_, 0, v___x_3952_);
    crate::leanh::lean_closure_set(v___f_3953_, 1, v_toPure_3949_);
    v___f_3954_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3954_, 0, v_f_3946_);
    crate::leanh::lean_closure_set(v___f_3954_, 1, v_toBind_3948_);
    crate::leanh::lean_closure_set(v___f_3954_, 2, v___f_3953_);
    crate::leanh::lean_closure_set(v___f_3954_, 3, v___f_3951_);
    v___x_3955_ = crate::leanh::lean_apply_6(
        v_inst_3944_,
        v___f_3950_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3945_,
        v___x_3952_,
        v___f_3954_,
    );
    return v___x_3955_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f___boxed(
    mut v_00_u03b1_3956_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3957_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3958_: *mut crate::leanh::LeanObject,
    mut v_m_3959_: *mut crate::leanh::LeanObject,
    mut v_inst_3960_: *mut crate::leanh::LeanObject,
    mut v_inst_3961_: *mut crate::leanh::LeanObject,
    mut v_inst_3962_: *mut crate::leanh::LeanObject,
    mut v_it_3963_: *mut crate::leanh::LeanObject,
    mut v_f_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3965_ = l_Std_IterM_Partial_findSomeM_x3f(
        v_00_u03b1_3956_,
        v_00_u03b2_3957_,
        v_00_u03b3_3958_,
        v_m_3959_,
        v_inst_3960_,
        v_inst_3961_,
        v_inst_3962_,
        v_it_3963_,
        v_f_3964_,
    );
    crate::leanh::lean_dec(v_inst_3961_);
    return v_res_3965_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f___redArg(
    mut v_inst_3966_: *mut crate::leanh::LeanObject,
    mut v_inst_3967_: *mut crate::leanh::LeanObject,
    mut v_it_3968_: *mut crate::leanh::LeanObject,
    mut v_f_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3970_ = crate::leanh::lean_ctor_get(v_inst_3966_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3970_);
    v_toBind_3971_ = crate::leanh::lean_ctor_get(v_inst_3966_, 1);
    crate::leanh::lean_inc_n(v_toBind_3971_, 2);
    crate::leanh::lean_dec_ref(v_inst_3966_);
    v_toPure_3972_ = crate::leanh::lean_ctor_get(v_toApplicative_3970_, 1);
    crate::leanh::lean_inc_n(v_toPure_3972_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3970_);
    v___f_3973_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3973_, 0, v_toBind_3971_);
    v___f_3974_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3974_, 0, v_toPure_3972_);
    v___x_3975_ = crate::leanh::lean_box(0);
    v___f_3976_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3976_, 0, v___x_3975_);
    crate::leanh::lean_closure_set(v___f_3976_, 1, v_toPure_3972_);
    v___f_3977_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3977_, 0, v_f_3969_);
    crate::leanh::lean_closure_set(v___f_3977_, 1, v_toBind_3971_);
    crate::leanh::lean_closure_set(v___f_3977_, 2, v___f_3976_);
    crate::leanh::lean_closure_set(v___f_3977_, 3, v___f_3974_);
    v___x_3978_ = crate::leanh::lean_apply_6(
        v_inst_3967_,
        v___f_3973_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3968_,
        v___x_3975_,
        v___f_3977_,
    );
    return v___x_3978_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f(
    mut v_00_u03b1_3979_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3980_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3981_: *mut crate::leanh::LeanObject,
    mut v_m_3982_: *mut crate::leanh::LeanObject,
    mut v_inst_3983_: *mut crate::leanh::LeanObject,
    mut v_inst_3984_: *mut crate::leanh::LeanObject,
    mut v_inst_3985_: *mut crate::leanh::LeanObject,
    mut v_inst_3986_: *mut crate::leanh::LeanObject,
    mut v_it_3987_: *mut crate::leanh::LeanObject,
    mut v_f_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3989_ = crate::leanh::lean_ctor_get(v_inst_3983_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3989_);
    v_toBind_3990_ = crate::leanh::lean_ctor_get(v_inst_3983_, 1);
    crate::leanh::lean_inc_n(v_toBind_3990_, 2);
    crate::leanh::lean_dec_ref(v_inst_3983_);
    v_toPure_3991_ = crate::leanh::lean_ctor_get(v_toApplicative_3989_, 1);
    crate::leanh::lean_inc_n(v_toPure_3991_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3989_);
    v___f_3992_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3992_, 0, v_toBind_3990_);
    v___f_3993_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3993_, 0, v_toPure_3991_);
    v___x_3994_ = crate::leanh::lean_box(0);
    v___f_3995_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3995_, 0, v___x_3994_);
    crate::leanh::lean_closure_set(v___f_3995_, 1, v_toPure_3991_);
    v___f_3996_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3996_, 0, v_f_3988_);
    crate::leanh::lean_closure_set(v___f_3996_, 1, v_toBind_3990_);
    crate::leanh::lean_closure_set(v___f_3996_, 2, v___f_3995_);
    crate::leanh::lean_closure_set(v___f_3996_, 3, v___f_3993_);
    v___x_3997_ = crate::leanh::lean_apply_6(
        v_inst_3985_,
        v___f_3992_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_3987_,
        v___x_3994_,
        v___f_3996_,
    );
    return v___x_3997_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f___boxed(
    mut v_00_u03b1_3998_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3999_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4000_: *mut crate::leanh::LeanObject,
    mut v_m_4001_: *mut crate::leanh::LeanObject,
    mut v_inst_4002_: *mut crate::leanh::LeanObject,
    mut v_inst_4003_: *mut crate::leanh::LeanObject,
    mut v_inst_4004_: *mut crate::leanh::LeanObject,
    mut v_inst_4005_: *mut crate::leanh::LeanObject,
    mut v_it_4006_: *mut crate::leanh::LeanObject,
    mut v_f_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4008_ = l_Std_IterM_Total_findSomeM_x3f(
        v_00_u03b1_3998_,
        v_00_u03b2_3999_,
        v_00_u03b3_4000_,
        v_m_4001_,
        v_inst_4002_,
        v_inst_4003_,
        v_inst_4004_,
        v_inst_4005_,
        v_it_4006_,
        v_f_4007_,
    );
    crate::leanh::lean_dec(v_inst_4003_);
    return v_res_4008_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg___lam__3(
    mut v_f_4009_: *mut crate::leanh::LeanObject,
    mut v_toPure_4010_: *mut crate::leanh::LeanObject,
    mut v_toBind_4011_: *mut crate::leanh::LeanObject,
    mut v___f_4012_: *mut crate::leanh::LeanObject,
    mut v___f_4013_: *mut crate::leanh::LeanObject,
    mut v_x1_4014_: *mut crate::leanh::LeanObject,
    mut v_x2_4015_: *mut crate::leanh::LeanObject,
    mut v_x3_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = crate::leanh::lean_apply_1(v_f_4009_, v_x1_4014_);
    v___x_4018_ =
        crate::leanh::lean_apply_2(v_toPure_4010_, crate::leanh::lean_box(0), v___x_4017_);
    crate::leanh::lean_inc(v_toBind_4011_);
    v___x_4019_ = crate::leanh::lean_apply_4(
        v_toBind_4011_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4018_,
        v___f_4012_,
    );
    v___x_4020_ = crate::leanh::lean_apply_4(
        v_toBind_4011_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4019_,
        v___f_4013_,
    );
    return v___x_4020_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(
    mut v_f_4021_: *mut crate::leanh::LeanObject,
    mut v_toPure_4022_: *mut crate::leanh::LeanObject,
    mut v_toBind_4023_: *mut crate::leanh::LeanObject,
    mut v___f_4024_: *mut crate::leanh::LeanObject,
    mut v___f_4025_: *mut crate::leanh::LeanObject,
    mut v_x1_4026_: *mut crate::leanh::LeanObject,
    mut v_x2_4027_: *mut crate::leanh::LeanObject,
    mut v_x3_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_Std_IterM_findSome_x3f___redArg___lam__3(
        v_f_4021_,
        v_toPure_4022_,
        v_toBind_4023_,
        v___f_4024_,
        v___f_4025_,
        v_x1_4026_,
        v_x2_4027_,
        v_x3_4028_,
    );
    crate::leanh::lean_dec(v_x3_4028_);
    return v_res_4029_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg(
    mut v_inst_4030_: *mut crate::leanh::LeanObject,
    mut v_inst_4031_: *mut crate::leanh::LeanObject,
    mut v_it_4032_: *mut crate::leanh::LeanObject,
    mut v_f_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4034_ = crate::leanh::lean_ctor_get(v_inst_4030_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4034_);
    v_toBind_4035_ = crate::leanh::lean_ctor_get(v_inst_4030_, 1);
    crate::leanh::lean_inc_n(v_toBind_4035_, 2);
    crate::leanh::lean_dec_ref(v_inst_4030_);
    v_toPure_4036_ = crate::leanh::lean_ctor_get(v_toApplicative_4034_, 1);
    crate::leanh::lean_inc_n(v_toPure_4036_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4034_);
    v___f_4037_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4037_, 0, v_toBind_4035_);
    v___f_4038_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4038_, 0, v_toPure_4036_);
    v___x_4039_ = crate::leanh::lean_box(0);
    v___f_4040_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4040_, 0, v___x_4039_);
    crate::leanh::lean_closure_set(v___f_4040_, 1, v_toPure_4036_);
    v___f_4041_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4041_, 0, v_f_4033_);
    crate::leanh::lean_closure_set(v___f_4041_, 1, v_toPure_4036_);
    crate::leanh::lean_closure_set(v___f_4041_, 2, v_toBind_4035_);
    crate::leanh::lean_closure_set(v___f_4041_, 3, v___f_4040_);
    crate::leanh::lean_closure_set(v___f_4041_, 4, v___f_4038_);
    v___x_4042_ = crate::leanh::lean_apply_6(
        v_inst_4031_,
        v___f_4037_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4032_,
        v___x_4039_,
        v___f_4041_,
    );
    return v___x_4042_;
}
pub unsafe fn l_Std_IterM_findSome_x3f(
    mut v_00_u03b1_4043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4044_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4045_: *mut crate::leanh::LeanObject,
    mut v_m_4046_: *mut crate::leanh::LeanObject,
    mut v_inst_4047_: *mut crate::leanh::LeanObject,
    mut v_inst_4048_: *mut crate::leanh::LeanObject,
    mut v_inst_4049_: *mut crate::leanh::LeanObject,
    mut v_it_4050_: *mut crate::leanh::LeanObject,
    mut v_f_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4052_ = crate::leanh::lean_ctor_get(v_inst_4047_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4052_);
    v_toBind_4053_ = crate::leanh::lean_ctor_get(v_inst_4047_, 1);
    crate::leanh::lean_inc_n(v_toBind_4053_, 2);
    crate::leanh::lean_dec_ref(v_inst_4047_);
    v_toPure_4054_ = crate::leanh::lean_ctor_get(v_toApplicative_4052_, 1);
    crate::leanh::lean_inc_n(v_toPure_4054_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4052_);
    v___f_4055_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4055_, 0, v_toBind_4053_);
    v___f_4056_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4056_, 0, v_toPure_4054_);
    v___x_4057_ = crate::leanh::lean_box(0);
    v___f_4058_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4058_, 0, v___x_4057_);
    crate::leanh::lean_closure_set(v___f_4058_, 1, v_toPure_4054_);
    v___f_4059_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4059_, 0, v_f_4051_);
    crate::leanh::lean_closure_set(v___f_4059_, 1, v_toPure_4054_);
    crate::leanh::lean_closure_set(v___f_4059_, 2, v_toBind_4053_);
    crate::leanh::lean_closure_set(v___f_4059_, 3, v___f_4058_);
    crate::leanh::lean_closure_set(v___f_4059_, 4, v___f_4056_);
    v___x_4060_ = crate::leanh::lean_apply_6(
        v_inst_4049_,
        v___f_4055_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4050_,
        v___x_4057_,
        v___f_4059_,
    );
    return v___x_4060_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___boxed(
    mut v_00_u03b1_4061_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4062_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4063_: *mut crate::leanh::LeanObject,
    mut v_m_4064_: *mut crate::leanh::LeanObject,
    mut v_inst_4065_: *mut crate::leanh::LeanObject,
    mut v_inst_4066_: *mut crate::leanh::LeanObject,
    mut v_inst_4067_: *mut crate::leanh::LeanObject,
    mut v_it_4068_: *mut crate::leanh::LeanObject,
    mut v_f_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4070_ = l_Std_IterM_findSome_x3f(
        v_00_u03b1_4061_,
        v_00_u03b2_4062_,
        v_00_u03b3_4063_,
        v_m_4064_,
        v_inst_4065_,
        v_inst_4066_,
        v_inst_4067_,
        v_it_4068_,
        v_f_4069_,
    );
    crate::leanh::lean_dec(v_inst_4066_);
    return v_res_4070_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f___redArg(
    mut v_inst_4071_: *mut crate::leanh::LeanObject,
    mut v_inst_4072_: *mut crate::leanh::LeanObject,
    mut v_it_4073_: *mut crate::leanh::LeanObject,
    mut v_f_4074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4075_ = crate::leanh::lean_ctor_get(v_inst_4071_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4075_);
    v_toBind_4076_ = crate::leanh::lean_ctor_get(v_inst_4071_, 1);
    crate::leanh::lean_inc_n(v_toBind_4076_, 2);
    crate::leanh::lean_dec_ref(v_inst_4071_);
    v_toPure_4077_ = crate::leanh::lean_ctor_get(v_toApplicative_4075_, 1);
    crate::leanh::lean_inc_n(v_toPure_4077_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4075_);
    v___f_4078_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4078_, 0, v_toBind_4076_);
    v___f_4079_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4079_, 0, v_toPure_4077_);
    v___x_4080_ = crate::leanh::lean_box(0);
    v___f_4081_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4081_, 0, v___x_4080_);
    crate::leanh::lean_closure_set(v___f_4081_, 1, v_toPure_4077_);
    v___f_4082_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4082_, 0, v_f_4074_);
    crate::leanh::lean_closure_set(v___f_4082_, 1, v_toPure_4077_);
    crate::leanh::lean_closure_set(v___f_4082_, 2, v_toBind_4076_);
    crate::leanh::lean_closure_set(v___f_4082_, 3, v___f_4081_);
    crate::leanh::lean_closure_set(v___f_4082_, 4, v___f_4079_);
    v___x_4083_ = crate::leanh::lean_apply_6(
        v_inst_4072_,
        v___f_4078_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4073_,
        v___x_4080_,
        v___f_4082_,
    );
    return v___x_4083_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f(
    mut v_00_u03b1_4084_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4085_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4086_: *mut crate::leanh::LeanObject,
    mut v_m_4087_: *mut crate::leanh::LeanObject,
    mut v_inst_4088_: *mut crate::leanh::LeanObject,
    mut v_inst_4089_: *mut crate::leanh::LeanObject,
    mut v_inst_4090_: *mut crate::leanh::LeanObject,
    mut v_it_4091_: *mut crate::leanh::LeanObject,
    mut v_f_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4093_ = crate::leanh::lean_ctor_get(v_inst_4088_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4093_);
    v_toBind_4094_ = crate::leanh::lean_ctor_get(v_inst_4088_, 1);
    crate::leanh::lean_inc_n(v_toBind_4094_, 2);
    crate::leanh::lean_dec_ref(v_inst_4088_);
    v_toPure_4095_ = crate::leanh::lean_ctor_get(v_toApplicative_4093_, 1);
    crate::leanh::lean_inc_n(v_toPure_4095_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4093_);
    v___f_4096_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4096_, 0, v_toBind_4094_);
    v___f_4097_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4097_, 0, v_toPure_4095_);
    v___x_4098_ = crate::leanh::lean_box(0);
    v___f_4099_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4099_, 0, v___x_4098_);
    crate::leanh::lean_closure_set(v___f_4099_, 1, v_toPure_4095_);
    v___f_4100_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4100_, 0, v_f_4092_);
    crate::leanh::lean_closure_set(v___f_4100_, 1, v_toPure_4095_);
    crate::leanh::lean_closure_set(v___f_4100_, 2, v_toBind_4094_);
    crate::leanh::lean_closure_set(v___f_4100_, 3, v___f_4099_);
    crate::leanh::lean_closure_set(v___f_4100_, 4, v___f_4097_);
    v___x_4101_ = crate::leanh::lean_apply_6(
        v_inst_4090_,
        v___f_4096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4091_,
        v___x_4098_,
        v___f_4100_,
    );
    return v___x_4101_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f___boxed(
    mut v_00_u03b1_4102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4103_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4104_: *mut crate::leanh::LeanObject,
    mut v_m_4105_: *mut crate::leanh::LeanObject,
    mut v_inst_4106_: *mut crate::leanh::LeanObject,
    mut v_inst_4107_: *mut crate::leanh::LeanObject,
    mut v_inst_4108_: *mut crate::leanh::LeanObject,
    mut v_it_4109_: *mut crate::leanh::LeanObject,
    mut v_f_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_Std_IterM_Partial_findSome_x3f(
        v_00_u03b1_4102_,
        v_00_u03b2_4103_,
        v_00_u03b3_4104_,
        v_m_4105_,
        v_inst_4106_,
        v_inst_4107_,
        v_inst_4108_,
        v_it_4109_,
        v_f_4110_,
    );
    crate::leanh::lean_dec(v_inst_4107_);
    return v_res_4111_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f___redArg(
    mut v_inst_4112_: *mut crate::leanh::LeanObject,
    mut v_inst_4113_: *mut crate::leanh::LeanObject,
    mut v_it_4114_: *mut crate::leanh::LeanObject,
    mut v_f_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4116_ = crate::leanh::lean_ctor_get(v_inst_4112_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4116_);
    v_toBind_4117_ = crate::leanh::lean_ctor_get(v_inst_4112_, 1);
    crate::leanh::lean_inc_n(v_toBind_4117_, 2);
    crate::leanh::lean_dec_ref(v_inst_4112_);
    v_toPure_4118_ = crate::leanh::lean_ctor_get(v_toApplicative_4116_, 1);
    crate::leanh::lean_inc_n(v_toPure_4118_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4116_);
    v___f_4119_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4119_, 0, v_toBind_4117_);
    v___f_4120_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4120_, 0, v_toPure_4118_);
    v___x_4121_ = crate::leanh::lean_box(0);
    v___f_4122_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4122_, 0, v___x_4121_);
    crate::leanh::lean_closure_set(v___f_4122_, 1, v_toPure_4118_);
    v___f_4123_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4123_, 0, v_f_4115_);
    crate::leanh::lean_closure_set(v___f_4123_, 1, v_toPure_4118_);
    crate::leanh::lean_closure_set(v___f_4123_, 2, v_toBind_4117_);
    crate::leanh::lean_closure_set(v___f_4123_, 3, v___f_4122_);
    crate::leanh::lean_closure_set(v___f_4123_, 4, v___f_4120_);
    v___x_4124_ = crate::leanh::lean_apply_6(
        v_inst_4113_,
        v___f_4119_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4114_,
        v___x_4121_,
        v___f_4123_,
    );
    return v___x_4124_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f(
    mut v_00_u03b1_4125_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4126_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4127_: *mut crate::leanh::LeanObject,
    mut v_m_4128_: *mut crate::leanh::LeanObject,
    mut v_inst_4129_: *mut crate::leanh::LeanObject,
    mut v_inst_4130_: *mut crate::leanh::LeanObject,
    mut v_inst_4131_: *mut crate::leanh::LeanObject,
    mut v_inst_4132_: *mut crate::leanh::LeanObject,
    mut v_it_4133_: *mut crate::leanh::LeanObject,
    mut v_f_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4135_ = crate::leanh::lean_ctor_get(v_inst_4129_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4135_);
    v_toBind_4136_ = crate::leanh::lean_ctor_get(v_inst_4129_, 1);
    crate::leanh::lean_inc_n(v_toBind_4136_, 2);
    crate::leanh::lean_dec_ref(v_inst_4129_);
    v_toPure_4137_ = crate::leanh::lean_ctor_get(v_toApplicative_4135_, 1);
    crate::leanh::lean_inc_n(v_toPure_4137_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4135_);
    v___f_4138_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4138_, 0, v_toBind_4136_);
    v___f_4139_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4139_, 0, v_toPure_4137_);
    v___x_4140_ = crate::leanh::lean_box(0);
    v___f_4141_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4141_, 0, v___x_4140_);
    crate::leanh::lean_closure_set(v___f_4141_, 1, v_toPure_4137_);
    v___f_4142_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4142_, 0, v_f_4134_);
    crate::leanh::lean_closure_set(v___f_4142_, 1, v_toPure_4137_);
    crate::leanh::lean_closure_set(v___f_4142_, 2, v_toBind_4136_);
    crate::leanh::lean_closure_set(v___f_4142_, 3, v___f_4141_);
    crate::leanh::lean_closure_set(v___f_4142_, 4, v___f_4139_);
    v___x_4143_ = crate::leanh::lean_apply_6(
        v_inst_4131_,
        v___f_4138_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4133_,
        v___x_4140_,
        v___f_4142_,
    );
    return v___x_4143_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f___boxed(
    mut v_00_u03b1_4144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4145_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4146_: *mut crate::leanh::LeanObject,
    mut v_m_4147_: *mut crate::leanh::LeanObject,
    mut v_inst_4148_: *mut crate::leanh::LeanObject,
    mut v_inst_4149_: *mut crate::leanh::LeanObject,
    mut v_inst_4150_: *mut crate::leanh::LeanObject,
    mut v_inst_4151_: *mut crate::leanh::LeanObject,
    mut v_it_4152_: *mut crate::leanh::LeanObject,
    mut v_f_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Std_IterM_Total_findSome_x3f(
        v_00_u03b1_4144_,
        v_00_u03b2_4145_,
        v_00_u03b3_4146_,
        v_m_4147_,
        v_inst_4148_,
        v_inst_4149_,
        v_inst_4150_,
        v_inst_4151_,
        v_it_4152_,
        v_f_4153_,
    );
    crate::leanh::lean_dec(v_inst_4149_);
    return v_res_4154_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__3(
    mut v_toPure_4155_: *mut crate::leanh::LeanObject,
    mut v___x_4156_: *mut crate::leanh::LeanObject,
    mut v_x1_4157_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4158_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_4158_ == 0 {
        let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x1_4157_);
        v___x_4159_ =
            crate::leanh::lean_apply_2(v_toPure_4155_, crate::leanh::lean_box(0), v___x_4156_);
        return v___x_4159_;
    } else {
        let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4156_);
        v___x_4160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4160_, 0, v_x1_4157_);
        v___x_4161_ =
            crate::leanh::lean_apply_2(v_toPure_4155_, crate::leanh::lean_box(0), v___x_4160_);
        return v___x_4161_;
    }
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__3___boxed(
    mut v_toPure_4162_: *mut crate::leanh::LeanObject,
    mut v___x_4163_: *mut crate::leanh::LeanObject,
    mut v_x1_4164_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_191__boxed_4166_: u8 = 0;
    let mut v_res_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_4166_ = (crate::leanh::lean_unbox(v_____do__lift_4165_) as u8);
    v_res_4167_ = l_Std_IterM_findM_x3f___redArg___lam__3(
        v_toPure_4162_,
        v___x_4163_,
        v_x1_4164_,
        v_____do__lift_191__boxed_4166_,
    );
    return v_res_4167_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__0(
    mut v_toPure_4168_: *mut crate::leanh::LeanObject,
    mut v___x_4169_: *mut crate::leanh::LeanObject,
    mut v_f_4170_: *mut crate::leanh::LeanObject,
    mut v_toBind_4171_: *mut crate::leanh::LeanObject,
    mut v___f_4172_: *mut crate::leanh::LeanObject,
    mut v___f_4173_: *mut crate::leanh::LeanObject,
    mut v_x1_4174_: *mut crate::leanh::LeanObject,
    mut v_x2_4175_: *mut crate::leanh::LeanObject,
    mut v_x3_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x1_4174_);
    v___f_4177_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4177_, 0, v_toPure_4168_);
    crate::leanh::lean_closure_set(v___f_4177_, 1, v___x_4169_);
    crate::leanh::lean_closure_set(v___f_4177_, 2, v_x1_4174_);
    v___x_4178_ = crate::leanh::lean_apply_1(v_f_4170_, v_x1_4174_);
    crate::leanh::lean_inc_n(v_toBind_4171_, 2);
    v___x_4179_ = crate::leanh::lean_apply_4(
        v_toBind_4171_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4178_,
        v___f_4177_,
    );
    v___x_4180_ = crate::leanh::lean_apply_4(
        v_toBind_4171_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4179_,
        v___f_4172_,
    );
    v___x_4181_ = crate::leanh::lean_apply_4(
        v_toBind_4171_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4180_,
        v___f_4173_,
    );
    return v___x_4181_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__0___boxed(
    mut v_toPure_4182_: *mut crate::leanh::LeanObject,
    mut v___x_4183_: *mut crate::leanh::LeanObject,
    mut v_f_4184_: *mut crate::leanh::LeanObject,
    mut v_toBind_4185_: *mut crate::leanh::LeanObject,
    mut v___f_4186_: *mut crate::leanh::LeanObject,
    mut v___f_4187_: *mut crate::leanh::LeanObject,
    mut v_x1_4188_: *mut crate::leanh::LeanObject,
    mut v_x2_4189_: *mut crate::leanh::LeanObject,
    mut v_x3_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Std_IterM_findM_x3f___redArg___lam__0(
        v_toPure_4182_,
        v___x_4183_,
        v_f_4184_,
        v_toBind_4185_,
        v___f_4186_,
        v___f_4187_,
        v_x1_4188_,
        v_x2_4189_,
        v_x3_4190_,
    );
    crate::leanh::lean_dec(v_x3_4190_);
    return v_res_4191_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg(
    mut v_inst_4192_: *mut crate::leanh::LeanObject,
    mut v_inst_4193_: *mut crate::leanh::LeanObject,
    mut v_it_4194_: *mut crate::leanh::LeanObject,
    mut v_f_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4196_ = crate::leanh::lean_ctor_get(v_inst_4192_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4196_);
    v_toBind_4197_ = crate::leanh::lean_ctor_get(v_inst_4192_, 1);
    crate::leanh::lean_inc_n(v_toBind_4197_, 2);
    crate::leanh::lean_dec_ref(v_inst_4192_);
    v_toPure_4198_ = crate::leanh::lean_ctor_get(v_toApplicative_4196_, 1);
    crate::leanh::lean_inc_n(v_toPure_4198_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4196_);
    v___f_4199_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4199_, 0, v_toBind_4197_);
    v___f_4200_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4200_, 0, v_toPure_4198_);
    v___x_4201_ = crate::leanh::lean_box(0);
    v___f_4202_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4202_, 0, v___x_4201_);
    crate::leanh::lean_closure_set(v___f_4202_, 1, v_toPure_4198_);
    v___f_4203_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4203_, 0, v_toPure_4198_);
    crate::leanh::lean_closure_set(v___f_4203_, 1, v___x_4201_);
    crate::leanh::lean_closure_set(v___f_4203_, 2, v_f_4195_);
    crate::leanh::lean_closure_set(v___f_4203_, 3, v_toBind_4197_);
    crate::leanh::lean_closure_set(v___f_4203_, 4, v___f_4202_);
    crate::leanh::lean_closure_set(v___f_4203_, 5, v___f_4200_);
    v___x_4204_ = crate::leanh::lean_apply_6(
        v_inst_4193_,
        v___f_4199_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4194_,
        v___x_4201_,
        v___f_4203_,
    );
    return v___x_4204_;
}
pub unsafe fn l_Std_IterM_findM_x3f(
    mut v_00_u03b1_4205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4206_: *mut crate::leanh::LeanObject,
    mut v_m_4207_: *mut crate::leanh::LeanObject,
    mut v_inst_4208_: *mut crate::leanh::LeanObject,
    mut v_inst_4209_: *mut crate::leanh::LeanObject,
    mut v_inst_4210_: *mut crate::leanh::LeanObject,
    mut v_it_4211_: *mut crate::leanh::LeanObject,
    mut v_f_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4213_ = crate::leanh::lean_ctor_get(v_inst_4208_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4213_);
    v_toBind_4214_ = crate::leanh::lean_ctor_get(v_inst_4208_, 1);
    crate::leanh::lean_inc_n(v_toBind_4214_, 2);
    crate::leanh::lean_dec_ref(v_inst_4208_);
    v_toPure_4215_ = crate::leanh::lean_ctor_get(v_toApplicative_4213_, 1);
    crate::leanh::lean_inc_n(v_toPure_4215_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4213_);
    v___f_4216_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4216_, 0, v_toBind_4214_);
    v___f_4217_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4217_, 0, v_toPure_4215_);
    v___x_4218_ = crate::leanh::lean_box(0);
    v___f_4219_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4219_, 0, v___x_4218_);
    crate::leanh::lean_closure_set(v___f_4219_, 1, v_toPure_4215_);
    v___f_4220_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4220_, 0, v_toPure_4215_);
    crate::leanh::lean_closure_set(v___f_4220_, 1, v___x_4218_);
    crate::leanh::lean_closure_set(v___f_4220_, 2, v_f_4212_);
    crate::leanh::lean_closure_set(v___f_4220_, 3, v_toBind_4214_);
    crate::leanh::lean_closure_set(v___f_4220_, 4, v___f_4219_);
    crate::leanh::lean_closure_set(v___f_4220_, 5, v___f_4217_);
    v___x_4221_ = crate::leanh::lean_apply_6(
        v_inst_4210_,
        v___f_4216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4211_,
        v___x_4218_,
        v___f_4220_,
    );
    return v___x_4221_;
}
pub unsafe fn l_Std_IterM_findM_x3f___boxed(
    mut v_00_u03b1_4222_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4223_: *mut crate::leanh::LeanObject,
    mut v_m_4224_: *mut crate::leanh::LeanObject,
    mut v_inst_4225_: *mut crate::leanh::LeanObject,
    mut v_inst_4226_: *mut crate::leanh::LeanObject,
    mut v_inst_4227_: *mut crate::leanh::LeanObject,
    mut v_it_4228_: *mut crate::leanh::LeanObject,
    mut v_f_4229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4230_ = l_Std_IterM_findM_x3f(
        v_00_u03b1_4222_,
        v_00_u03b2_4223_,
        v_m_4224_,
        v_inst_4225_,
        v_inst_4226_,
        v_inst_4227_,
        v_it_4228_,
        v_f_4229_,
    );
    crate::leanh::lean_dec(v_inst_4226_);
    return v_res_4230_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f___redArg(
    mut v_inst_4231_: *mut crate::leanh::LeanObject,
    mut v_inst_4232_: *mut crate::leanh::LeanObject,
    mut v_it_4233_: *mut crate::leanh::LeanObject,
    mut v_f_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4235_ = crate::leanh::lean_ctor_get(v_inst_4231_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4235_);
    v_toBind_4236_ = crate::leanh::lean_ctor_get(v_inst_4231_, 1);
    crate::leanh::lean_inc_n(v_toBind_4236_, 2);
    crate::leanh::lean_dec_ref(v_inst_4231_);
    v_toPure_4237_ = crate::leanh::lean_ctor_get(v_toApplicative_4235_, 1);
    crate::leanh::lean_inc_n(v_toPure_4237_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4235_);
    v___f_4238_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4238_, 0, v_toBind_4236_);
    v___f_4239_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4239_, 0, v_toPure_4237_);
    v___x_4240_ = crate::leanh::lean_box(0);
    v___f_4241_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4241_, 0, v___x_4240_);
    crate::leanh::lean_closure_set(v___f_4241_, 1, v_toPure_4237_);
    v___f_4242_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4242_, 0, v_toPure_4237_);
    crate::leanh::lean_closure_set(v___f_4242_, 1, v___x_4240_);
    crate::leanh::lean_closure_set(v___f_4242_, 2, v_f_4234_);
    crate::leanh::lean_closure_set(v___f_4242_, 3, v_toBind_4236_);
    crate::leanh::lean_closure_set(v___f_4242_, 4, v___f_4241_);
    crate::leanh::lean_closure_set(v___f_4242_, 5, v___f_4239_);
    v___x_4243_ = crate::leanh::lean_apply_6(
        v_inst_4232_,
        v___f_4238_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4233_,
        v___x_4240_,
        v___f_4242_,
    );
    return v___x_4243_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f(
    mut v_00_u03b1_4244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4245_: *mut crate::leanh::LeanObject,
    mut v_m_4246_: *mut crate::leanh::LeanObject,
    mut v_inst_4247_: *mut crate::leanh::LeanObject,
    mut v_inst_4248_: *mut crate::leanh::LeanObject,
    mut v_inst_4249_: *mut crate::leanh::LeanObject,
    mut v_it_4250_: *mut crate::leanh::LeanObject,
    mut v_f_4251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4252_ = crate::leanh::lean_ctor_get(v_inst_4247_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4252_);
    v_toBind_4253_ = crate::leanh::lean_ctor_get(v_inst_4247_, 1);
    crate::leanh::lean_inc_n(v_toBind_4253_, 2);
    crate::leanh::lean_dec_ref(v_inst_4247_);
    v_toPure_4254_ = crate::leanh::lean_ctor_get(v_toApplicative_4252_, 1);
    crate::leanh::lean_inc_n(v_toPure_4254_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4252_);
    v___f_4255_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4255_, 0, v_toBind_4253_);
    v___f_4256_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4256_, 0, v_toPure_4254_);
    v___x_4257_ = crate::leanh::lean_box(0);
    v___f_4258_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4258_, 0, v___x_4257_);
    crate::leanh::lean_closure_set(v___f_4258_, 1, v_toPure_4254_);
    v___f_4259_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4259_, 0, v_toPure_4254_);
    crate::leanh::lean_closure_set(v___f_4259_, 1, v___x_4257_);
    crate::leanh::lean_closure_set(v___f_4259_, 2, v_f_4251_);
    crate::leanh::lean_closure_set(v___f_4259_, 3, v_toBind_4253_);
    crate::leanh::lean_closure_set(v___f_4259_, 4, v___f_4258_);
    crate::leanh::lean_closure_set(v___f_4259_, 5, v___f_4256_);
    v___x_4260_ = crate::leanh::lean_apply_6(
        v_inst_4249_,
        v___f_4255_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4250_,
        v___x_4257_,
        v___f_4259_,
    );
    return v___x_4260_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f___boxed(
    mut v_00_u03b1_4261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4262_: *mut crate::leanh::LeanObject,
    mut v_m_4263_: *mut crate::leanh::LeanObject,
    mut v_inst_4264_: *mut crate::leanh::LeanObject,
    mut v_inst_4265_: *mut crate::leanh::LeanObject,
    mut v_inst_4266_: *mut crate::leanh::LeanObject,
    mut v_it_4267_: *mut crate::leanh::LeanObject,
    mut v_f_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ = l_Std_IterM_Partial_findM_x3f(
        v_00_u03b1_4261_,
        v_00_u03b2_4262_,
        v_m_4263_,
        v_inst_4264_,
        v_inst_4265_,
        v_inst_4266_,
        v_it_4267_,
        v_f_4268_,
    );
    crate::leanh::lean_dec(v_inst_4265_);
    return v_res_4269_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f___redArg(
    mut v_inst_4270_: *mut crate::leanh::LeanObject,
    mut v_inst_4271_: *mut crate::leanh::LeanObject,
    mut v_it_4272_: *mut crate::leanh::LeanObject,
    mut v_f_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4274_ = crate::leanh::lean_ctor_get(v_inst_4270_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4274_);
    v_toBind_4275_ = crate::leanh::lean_ctor_get(v_inst_4270_, 1);
    crate::leanh::lean_inc_n(v_toBind_4275_, 2);
    crate::leanh::lean_dec_ref(v_inst_4270_);
    v_toPure_4276_ = crate::leanh::lean_ctor_get(v_toApplicative_4274_, 1);
    crate::leanh::lean_inc_n(v_toPure_4276_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4274_);
    v___f_4277_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4277_, 0, v_toBind_4275_);
    v___f_4278_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4278_, 0, v_toPure_4276_);
    v___x_4279_ = crate::leanh::lean_box(0);
    v___f_4280_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4280_, 0, v___x_4279_);
    crate::leanh::lean_closure_set(v___f_4280_, 1, v_toPure_4276_);
    v___f_4281_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4281_, 0, v_toPure_4276_);
    crate::leanh::lean_closure_set(v___f_4281_, 1, v___x_4279_);
    crate::leanh::lean_closure_set(v___f_4281_, 2, v_f_4273_);
    crate::leanh::lean_closure_set(v___f_4281_, 3, v_toBind_4275_);
    crate::leanh::lean_closure_set(v___f_4281_, 4, v___f_4280_);
    crate::leanh::lean_closure_set(v___f_4281_, 5, v___f_4278_);
    v___x_4282_ = crate::leanh::lean_apply_6(
        v_inst_4271_,
        v___f_4277_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4272_,
        v___x_4279_,
        v___f_4281_,
    );
    return v___x_4282_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f(
    mut v_00_u03b1_4283_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4284_: *mut crate::leanh::LeanObject,
    mut v_m_4285_: *mut crate::leanh::LeanObject,
    mut v_inst_4286_: *mut crate::leanh::LeanObject,
    mut v_inst_4287_: *mut crate::leanh::LeanObject,
    mut v_inst_4288_: *mut crate::leanh::LeanObject,
    mut v_inst_4289_: *mut crate::leanh::LeanObject,
    mut v_it_4290_: *mut crate::leanh::LeanObject,
    mut v_f_4291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4292_ = crate::leanh::lean_ctor_get(v_inst_4286_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4292_);
    v_toBind_4293_ = crate::leanh::lean_ctor_get(v_inst_4286_, 1);
    crate::leanh::lean_inc_n(v_toBind_4293_, 2);
    crate::leanh::lean_dec_ref(v_inst_4286_);
    v_toPure_4294_ = crate::leanh::lean_ctor_get(v_toApplicative_4292_, 1);
    crate::leanh::lean_inc_n(v_toPure_4294_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4292_);
    v___f_4295_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4295_, 0, v_toBind_4293_);
    v___f_4296_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4296_, 0, v_toPure_4294_);
    v___x_4297_ = crate::leanh::lean_box(0);
    v___f_4298_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4298_, 0, v___x_4297_);
    crate::leanh::lean_closure_set(v___f_4298_, 1, v_toPure_4294_);
    v___f_4299_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4299_, 0, v_toPure_4294_);
    crate::leanh::lean_closure_set(v___f_4299_, 1, v___x_4297_);
    crate::leanh::lean_closure_set(v___f_4299_, 2, v_f_4291_);
    crate::leanh::lean_closure_set(v___f_4299_, 3, v_toBind_4293_);
    crate::leanh::lean_closure_set(v___f_4299_, 4, v___f_4298_);
    crate::leanh::lean_closure_set(v___f_4299_, 5, v___f_4296_);
    v___x_4300_ = crate::leanh::lean_apply_6(
        v_inst_4288_,
        v___f_4295_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4290_,
        v___x_4297_,
        v___f_4299_,
    );
    return v___x_4300_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f___boxed(
    mut v_00_u03b1_4301_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4302_: *mut crate::leanh::LeanObject,
    mut v_m_4303_: *mut crate::leanh::LeanObject,
    mut v_inst_4304_: *mut crate::leanh::LeanObject,
    mut v_inst_4305_: *mut crate::leanh::LeanObject,
    mut v_inst_4306_: *mut crate::leanh::LeanObject,
    mut v_inst_4307_: *mut crate::leanh::LeanObject,
    mut v_it_4308_: *mut crate::leanh::LeanObject,
    mut v_f_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4310_ = l_Std_IterM_Total_findM_x3f(
        v_00_u03b1_4301_,
        v_00_u03b2_4302_,
        v_m_4303_,
        v_inst_4304_,
        v_inst_4305_,
        v_inst_4306_,
        v_inst_4307_,
        v_it_4308_,
        v_f_4309_,
    );
    crate::leanh::lean_dec(v_inst_4305_);
    return v_res_4310_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg___lam__4(
    mut v_toPure_4311_: *mut crate::leanh::LeanObject,
    mut v___x_4312_: *mut crate::leanh::LeanObject,
    mut v_f_4313_: *mut crate::leanh::LeanObject,
    mut v_toBind_4314_: *mut crate::leanh::LeanObject,
    mut v___f_4315_: *mut crate::leanh::LeanObject,
    mut v___f_4316_: *mut crate::leanh::LeanObject,
    mut v_x1_4317_: *mut crate::leanh::LeanObject,
    mut v_x2_4318_: *mut crate::leanh::LeanObject,
    mut v_x3_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x1_4317_);
    crate::leanh::lean_inc(v_toPure_4311_);
    v___f_4320_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4320_, 0, v_toPure_4311_);
    crate::leanh::lean_closure_set(v___f_4320_, 1, v___x_4312_);
    crate::leanh::lean_closure_set(v___f_4320_, 2, v_x1_4317_);
    v___x_4321_ = crate::leanh::lean_apply_1(v_f_4313_, v_x1_4317_);
    v___x_4322_ =
        crate::leanh::lean_apply_2(v_toPure_4311_, crate::leanh::lean_box(0), v___x_4321_);
    crate::leanh::lean_inc_n(v_toBind_4314_, 2);
    v___x_4323_ = crate::leanh::lean_apply_4(
        v_toBind_4314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4322_,
        v___f_4320_,
    );
    v___x_4324_ = crate::leanh::lean_apply_4(
        v_toBind_4314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4323_,
        v___f_4315_,
    );
    v___x_4325_ = crate::leanh::lean_apply_4(
        v_toBind_4314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4324_,
        v___f_4316_,
    );
    return v___x_4325_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg___lam__4___boxed(
    mut v_toPure_4326_: *mut crate::leanh::LeanObject,
    mut v___x_4327_: *mut crate::leanh::LeanObject,
    mut v_f_4328_: *mut crate::leanh::LeanObject,
    mut v_toBind_4329_: *mut crate::leanh::LeanObject,
    mut v___f_4330_: *mut crate::leanh::LeanObject,
    mut v___f_4331_: *mut crate::leanh::LeanObject,
    mut v_x1_4332_: *mut crate::leanh::LeanObject,
    mut v_x2_4333_: *mut crate::leanh::LeanObject,
    mut v_x3_4334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l_Std_IterM_find_x3f___redArg___lam__4(
        v_toPure_4326_,
        v___x_4327_,
        v_f_4328_,
        v_toBind_4329_,
        v___f_4330_,
        v___f_4331_,
        v_x1_4332_,
        v_x2_4333_,
        v_x3_4334_,
    );
    crate::leanh::lean_dec(v_x3_4334_);
    return v_res_4335_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg(
    mut v_inst_4336_: *mut crate::leanh::LeanObject,
    mut v_inst_4337_: *mut crate::leanh::LeanObject,
    mut v_it_4338_: *mut crate::leanh::LeanObject,
    mut v_f_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4340_ = crate::leanh::lean_ctor_get(v_inst_4336_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4340_);
    v_toBind_4341_ = crate::leanh::lean_ctor_get(v_inst_4336_, 1);
    crate::leanh::lean_inc_n(v_toBind_4341_, 2);
    crate::leanh::lean_dec_ref(v_inst_4336_);
    v_toPure_4342_ = crate::leanh::lean_ctor_get(v_toApplicative_4340_, 1);
    crate::leanh::lean_inc_n(v_toPure_4342_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4340_);
    v___f_4343_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4343_, 0, v_toBind_4341_);
    v___f_4344_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4344_, 0, v_toPure_4342_);
    v___x_4345_ = crate::leanh::lean_box(0);
    v___f_4346_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4346_, 0, v___x_4345_);
    crate::leanh::lean_closure_set(v___f_4346_, 1, v_toPure_4342_);
    v___f_4347_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4347_, 0, v_toPure_4342_);
    crate::leanh::lean_closure_set(v___f_4347_, 1, v___x_4345_);
    crate::leanh::lean_closure_set(v___f_4347_, 2, v_f_4339_);
    crate::leanh::lean_closure_set(v___f_4347_, 3, v_toBind_4341_);
    crate::leanh::lean_closure_set(v___f_4347_, 4, v___f_4346_);
    crate::leanh::lean_closure_set(v___f_4347_, 5, v___f_4344_);
    v___x_4348_ = crate::leanh::lean_apply_6(
        v_inst_4337_,
        v___f_4343_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4338_,
        v___x_4345_,
        v___f_4347_,
    );
    return v___x_4348_;
}
pub unsafe fn l_Std_IterM_find_x3f(
    mut v_00_u03b1_4349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4350_: *mut crate::leanh::LeanObject,
    mut v_m_4351_: *mut crate::leanh::LeanObject,
    mut v_inst_4352_: *mut crate::leanh::LeanObject,
    mut v_inst_4353_: *mut crate::leanh::LeanObject,
    mut v_inst_4354_: *mut crate::leanh::LeanObject,
    mut v_it_4355_: *mut crate::leanh::LeanObject,
    mut v_f_4356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4357_ = crate::leanh::lean_ctor_get(v_inst_4352_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4357_);
    v_toBind_4358_ = crate::leanh::lean_ctor_get(v_inst_4352_, 1);
    crate::leanh::lean_inc_n(v_toBind_4358_, 2);
    crate::leanh::lean_dec_ref(v_inst_4352_);
    v_toPure_4359_ = crate::leanh::lean_ctor_get(v_toApplicative_4357_, 1);
    crate::leanh::lean_inc_n(v_toPure_4359_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4357_);
    v___f_4360_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4360_, 0, v_toBind_4358_);
    v___f_4361_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4361_, 0, v_toPure_4359_);
    v___x_4362_ = crate::leanh::lean_box(0);
    v___f_4363_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4363_, 0, v___x_4362_);
    crate::leanh::lean_closure_set(v___f_4363_, 1, v_toPure_4359_);
    v___f_4364_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4364_, 0, v_toPure_4359_);
    crate::leanh::lean_closure_set(v___f_4364_, 1, v___x_4362_);
    crate::leanh::lean_closure_set(v___f_4364_, 2, v_f_4356_);
    crate::leanh::lean_closure_set(v___f_4364_, 3, v_toBind_4358_);
    crate::leanh::lean_closure_set(v___f_4364_, 4, v___f_4363_);
    crate::leanh::lean_closure_set(v___f_4364_, 5, v___f_4361_);
    v___x_4365_ = crate::leanh::lean_apply_6(
        v_inst_4354_,
        v___f_4360_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4355_,
        v___x_4362_,
        v___f_4364_,
    );
    return v___x_4365_;
}
pub unsafe fn l_Std_IterM_find_x3f___boxed(
    mut v_00_u03b1_4366_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4367_: *mut crate::leanh::LeanObject,
    mut v_m_4368_: *mut crate::leanh::LeanObject,
    mut v_inst_4369_: *mut crate::leanh::LeanObject,
    mut v_inst_4370_: *mut crate::leanh::LeanObject,
    mut v_inst_4371_: *mut crate::leanh::LeanObject,
    mut v_it_4372_: *mut crate::leanh::LeanObject,
    mut v_f_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4374_ = l_Std_IterM_find_x3f(
        v_00_u03b1_4366_,
        v_00_u03b2_4367_,
        v_m_4368_,
        v_inst_4369_,
        v_inst_4370_,
        v_inst_4371_,
        v_it_4372_,
        v_f_4373_,
    );
    crate::leanh::lean_dec(v_inst_4370_);
    return v_res_4374_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f___redArg(
    mut v_inst_4375_: *mut crate::leanh::LeanObject,
    mut v_inst_4376_: *mut crate::leanh::LeanObject,
    mut v_it_4377_: *mut crate::leanh::LeanObject,
    mut v_f_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4379_ = crate::leanh::lean_ctor_get(v_inst_4375_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4379_);
    v_toBind_4380_ = crate::leanh::lean_ctor_get(v_inst_4375_, 1);
    crate::leanh::lean_inc_n(v_toBind_4380_, 2);
    crate::leanh::lean_dec_ref(v_inst_4375_);
    v_toPure_4381_ = crate::leanh::lean_ctor_get(v_toApplicative_4379_, 1);
    crate::leanh::lean_inc_n(v_toPure_4381_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4379_);
    v___f_4382_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4382_, 0, v_toBind_4380_);
    v___f_4383_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4383_, 0, v_toPure_4381_);
    v___x_4384_ = crate::leanh::lean_box(0);
    v___f_4385_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4385_, 0, v___x_4384_);
    crate::leanh::lean_closure_set(v___f_4385_, 1, v_toPure_4381_);
    v___f_4386_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4386_, 0, v_toPure_4381_);
    crate::leanh::lean_closure_set(v___f_4386_, 1, v___x_4384_);
    crate::leanh::lean_closure_set(v___f_4386_, 2, v_f_4378_);
    crate::leanh::lean_closure_set(v___f_4386_, 3, v_toBind_4380_);
    crate::leanh::lean_closure_set(v___f_4386_, 4, v___f_4385_);
    crate::leanh::lean_closure_set(v___f_4386_, 5, v___f_4383_);
    v___x_4387_ = crate::leanh::lean_apply_6(
        v_inst_4376_,
        v___f_4382_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4377_,
        v___x_4384_,
        v___f_4386_,
    );
    return v___x_4387_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f(
    mut v_00_u03b1_4388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4389_: *mut crate::leanh::LeanObject,
    mut v_m_4390_: *mut crate::leanh::LeanObject,
    mut v_inst_4391_: *mut crate::leanh::LeanObject,
    mut v_inst_4392_: *mut crate::leanh::LeanObject,
    mut v_inst_4393_: *mut crate::leanh::LeanObject,
    mut v_it_4394_: *mut crate::leanh::LeanObject,
    mut v_f_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4396_ = crate::leanh::lean_ctor_get(v_inst_4391_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4396_);
    v_toBind_4397_ = crate::leanh::lean_ctor_get(v_inst_4391_, 1);
    crate::leanh::lean_inc_n(v_toBind_4397_, 2);
    crate::leanh::lean_dec_ref(v_inst_4391_);
    v_toPure_4398_ = crate::leanh::lean_ctor_get(v_toApplicative_4396_, 1);
    crate::leanh::lean_inc_n(v_toPure_4398_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4396_);
    v___f_4399_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4399_, 0, v_toBind_4397_);
    v___f_4400_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4400_, 0, v_toPure_4398_);
    v___x_4401_ = crate::leanh::lean_box(0);
    v___f_4402_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4402_, 0, v___x_4401_);
    crate::leanh::lean_closure_set(v___f_4402_, 1, v_toPure_4398_);
    v___f_4403_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4403_, 0, v_toPure_4398_);
    crate::leanh::lean_closure_set(v___f_4403_, 1, v___x_4401_);
    crate::leanh::lean_closure_set(v___f_4403_, 2, v_f_4395_);
    crate::leanh::lean_closure_set(v___f_4403_, 3, v_toBind_4397_);
    crate::leanh::lean_closure_set(v___f_4403_, 4, v___f_4402_);
    crate::leanh::lean_closure_set(v___f_4403_, 5, v___f_4400_);
    v___x_4404_ = crate::leanh::lean_apply_6(
        v_inst_4393_,
        v___f_4399_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4394_,
        v___x_4401_,
        v___f_4403_,
    );
    return v___x_4404_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f___boxed(
    mut v_00_u03b1_4405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4406_: *mut crate::leanh::LeanObject,
    mut v_m_4407_: *mut crate::leanh::LeanObject,
    mut v_inst_4408_: *mut crate::leanh::LeanObject,
    mut v_inst_4409_: *mut crate::leanh::LeanObject,
    mut v_inst_4410_: *mut crate::leanh::LeanObject,
    mut v_it_4411_: *mut crate::leanh::LeanObject,
    mut v_f_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4413_ = l_Std_IterM_Partial_find_x3f(
        v_00_u03b1_4405_,
        v_00_u03b2_4406_,
        v_m_4407_,
        v_inst_4408_,
        v_inst_4409_,
        v_inst_4410_,
        v_it_4411_,
        v_f_4412_,
    );
    crate::leanh::lean_dec(v_inst_4409_);
    return v_res_4413_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f___redArg(
    mut v_inst_4414_: *mut crate::leanh::LeanObject,
    mut v_inst_4415_: *mut crate::leanh::LeanObject,
    mut v_it_4416_: *mut crate::leanh::LeanObject,
    mut v_f_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4418_ = crate::leanh::lean_ctor_get(v_inst_4414_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4418_);
    v_toBind_4419_ = crate::leanh::lean_ctor_get(v_inst_4414_, 1);
    crate::leanh::lean_inc_n(v_toBind_4419_, 2);
    crate::leanh::lean_dec_ref(v_inst_4414_);
    v_toPure_4420_ = crate::leanh::lean_ctor_get(v_toApplicative_4418_, 1);
    crate::leanh::lean_inc_n(v_toPure_4420_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4418_);
    v___f_4421_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4421_, 0, v_toBind_4419_);
    v___f_4422_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4422_, 0, v_toPure_4420_);
    v___x_4423_ = crate::leanh::lean_box(0);
    v___f_4424_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4424_, 0, v___x_4423_);
    crate::leanh::lean_closure_set(v___f_4424_, 1, v_toPure_4420_);
    v___f_4425_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4425_, 0, v_toPure_4420_);
    crate::leanh::lean_closure_set(v___f_4425_, 1, v___x_4423_);
    crate::leanh::lean_closure_set(v___f_4425_, 2, v_f_4417_);
    crate::leanh::lean_closure_set(v___f_4425_, 3, v_toBind_4419_);
    crate::leanh::lean_closure_set(v___f_4425_, 4, v___f_4424_);
    crate::leanh::lean_closure_set(v___f_4425_, 5, v___f_4422_);
    v___x_4426_ = crate::leanh::lean_apply_6(
        v_inst_4415_,
        v___f_4421_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4416_,
        v___x_4423_,
        v___f_4425_,
    );
    return v___x_4426_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f(
    mut v_00_u03b1_4427_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4428_: *mut crate::leanh::LeanObject,
    mut v_m_4429_: *mut crate::leanh::LeanObject,
    mut v_inst_4430_: *mut crate::leanh::LeanObject,
    mut v_inst_4431_: *mut crate::leanh::LeanObject,
    mut v_inst_4432_: *mut crate::leanh::LeanObject,
    mut v_inst_4433_: *mut crate::leanh::LeanObject,
    mut v_it_4434_: *mut crate::leanh::LeanObject,
    mut v_f_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4436_ = crate::leanh::lean_ctor_get(v_inst_4430_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4436_);
    v_toBind_4437_ = crate::leanh::lean_ctor_get(v_inst_4430_, 1);
    crate::leanh::lean_inc_n(v_toBind_4437_, 2);
    crate::leanh::lean_dec_ref(v_inst_4430_);
    v_toPure_4438_ = crate::leanh::lean_ctor_get(v_toApplicative_4436_, 1);
    crate::leanh::lean_inc_n(v_toPure_4438_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_4436_);
    v___f_4439_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4439_, 0, v_toBind_4437_);
    v___f_4440_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4440_, 0, v_toPure_4438_);
    v___x_4441_ = crate::leanh::lean_box(0);
    v___f_4442_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4442_, 0, v___x_4441_);
    crate::leanh::lean_closure_set(v___f_4442_, 1, v_toPure_4438_);
    v___f_4443_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4443_, 0, v_toPure_4438_);
    crate::leanh::lean_closure_set(v___f_4443_, 1, v___x_4441_);
    crate::leanh::lean_closure_set(v___f_4443_, 2, v_f_4435_);
    crate::leanh::lean_closure_set(v___f_4443_, 3, v_toBind_4437_);
    crate::leanh::lean_closure_set(v___f_4443_, 4, v___f_4442_);
    crate::leanh::lean_closure_set(v___f_4443_, 5, v___f_4440_);
    v___x_4444_ = crate::leanh::lean_apply_6(
        v_inst_4432_,
        v___f_4439_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4434_,
        v___x_4441_,
        v___f_4443_,
    );
    return v___x_4444_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f___boxed(
    mut v_00_u03b1_4445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4446_: *mut crate::leanh::LeanObject,
    mut v_m_4447_: *mut crate::leanh::LeanObject,
    mut v_inst_4448_: *mut crate::leanh::LeanObject,
    mut v_inst_4449_: *mut crate::leanh::LeanObject,
    mut v_inst_4450_: *mut crate::leanh::LeanObject,
    mut v_inst_4451_: *mut crate::leanh::LeanObject,
    mut v_it_4452_: *mut crate::leanh::LeanObject,
    mut v_f_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4454_ = l_Std_IterM_Total_find_x3f(
        v_00_u03b1_4445_,
        v_00_u03b2_4446_,
        v_m_4447_,
        v_inst_4448_,
        v_inst_4449_,
        v_inst_4450_,
        v_inst_4451_,
        v_it_4452_,
        v_f_4453_,
    );
    crate::leanh::lean_dec(v_inst_4449_);
    return v_res_4454_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__0(
    mut v_toBind_4455_: *mut crate::leanh::LeanObject,
    mut v_x_4456_: *mut crate::leanh::LeanObject,
    mut v_x_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = crate::leanh::lean_apply_4(
        v_toBind_4455_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___y_4459_,
        v___y_4458_,
    );
    return v___x_4460_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__1(
    mut v_toPure_4461_: *mut crate::leanh::LeanObject,
    mut v_b_4462_: *mut crate::leanh::LeanObject,
    mut v_x_4463_: *mut crate::leanh::LeanObject,
    mut v_x_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4465_, 0, v_b_4462_);
    v___x_4466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4465_);
    v___x_4467_ =
        crate::leanh::lean_apply_2(v_toPure_4461_, crate::leanh::lean_box(0), v___x_4466_);
    return v___x_4467_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__1___boxed(
    mut v_toPure_4468_: *mut crate::leanh::LeanObject,
    mut v_b_4469_: *mut crate::leanh::LeanObject,
    mut v_x_4470_: *mut crate::leanh::LeanObject,
    mut v_x_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4472_ =
        l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_4468_, v_b_4469_, v_x_4470_, v_x_4471_);
    crate::leanh::lean_dec(v_x_4471_);
    return v_res_4472_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg(
    mut v_inst_4473_: *mut crate::leanh::LeanObject,
    mut v_inst_4474_: *mut crate::leanh::LeanObject,
    mut v_it_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4476_ = crate::leanh::lean_ctor_get(v_inst_4473_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4476_);
    v_toBind_4477_ = crate::leanh::lean_ctor_get(v_inst_4473_, 1);
    crate::leanh::lean_inc(v_toBind_4477_);
    crate::leanh::lean_dec_ref(v_inst_4473_);
    v_toPure_4478_ = crate::leanh::lean_ctor_get(v_toApplicative_4476_, 1);
    crate::leanh::lean_inc(v_toPure_4478_);
    crate::leanh::lean_dec_ref(v_toApplicative_4476_);
    v___f_4479_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4479_, 0, v_toBind_4477_);
    v___f_4480_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4480_, 0, v_toPure_4478_);
    v___x_4481_ = crate::leanh::lean_box(0);
    v___x_4482_ = crate::leanh::lean_apply_6(
        v_inst_4474_,
        v___f_4479_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4475_,
        v___x_4481_,
        v___f_4480_,
    );
    return v___x_4482_;
}
pub unsafe fn l_Std_IterM_first_x3f(
    mut v_00_u03b1_4483_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4484_: *mut crate::leanh::LeanObject,
    mut v_m_4485_: *mut crate::leanh::LeanObject,
    mut v_inst_4486_: *mut crate::leanh::LeanObject,
    mut v_inst_4487_: *mut crate::leanh::LeanObject,
    mut v_inst_4488_: *mut crate::leanh::LeanObject,
    mut v_it_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4490_ = crate::leanh::lean_ctor_get(v_inst_4486_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4490_);
    v_toBind_4491_ = crate::leanh::lean_ctor_get(v_inst_4486_, 1);
    crate::leanh::lean_inc(v_toBind_4491_);
    crate::leanh::lean_dec_ref(v_inst_4486_);
    v_toPure_4492_ = crate::leanh::lean_ctor_get(v_toApplicative_4490_, 1);
    crate::leanh::lean_inc(v_toPure_4492_);
    crate::leanh::lean_dec_ref(v_toApplicative_4490_);
    v___f_4493_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4493_, 0, v_toBind_4491_);
    v___f_4494_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4494_, 0, v_toPure_4492_);
    v___x_4495_ = crate::leanh::lean_box(0);
    v___x_4496_ = crate::leanh::lean_apply_6(
        v_inst_4488_,
        v___f_4493_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4489_,
        v___x_4495_,
        v___f_4494_,
    );
    return v___x_4496_;
}
pub unsafe fn l_Std_IterM_first_x3f___boxed(
    mut v_00_u03b1_4497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4498_: *mut crate::leanh::LeanObject,
    mut v_m_4499_: *mut crate::leanh::LeanObject,
    mut v_inst_4500_: *mut crate::leanh::LeanObject,
    mut v_inst_4501_: *mut crate::leanh::LeanObject,
    mut v_inst_4502_: *mut crate::leanh::LeanObject,
    mut v_it_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4504_ = l_Std_IterM_first_x3f(
        v_00_u03b1_4497_,
        v_00_u03b2_4498_,
        v_m_4499_,
        v_inst_4500_,
        v_inst_4501_,
        v_inst_4502_,
        v_it_4503_,
    );
    crate::leanh::lean_dec(v_inst_4501_);
    return v_res_4504_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f___redArg(
    mut v_inst_4505_: *mut crate::leanh::LeanObject,
    mut v_inst_4506_: *mut crate::leanh::LeanObject,
    mut v_it_4507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4508_ = crate::leanh::lean_ctor_get(v_inst_4505_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4508_);
    v_toBind_4509_ = crate::leanh::lean_ctor_get(v_inst_4505_, 1);
    crate::leanh::lean_inc(v_toBind_4509_);
    crate::leanh::lean_dec_ref(v_inst_4505_);
    v_toPure_4510_ = crate::leanh::lean_ctor_get(v_toApplicative_4508_, 1);
    crate::leanh::lean_inc(v_toPure_4510_);
    crate::leanh::lean_dec_ref(v_toApplicative_4508_);
    v___f_4511_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4511_, 0, v_toBind_4509_);
    v___f_4512_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4512_, 0, v_toPure_4510_);
    v___x_4513_ = crate::leanh::lean_box(0);
    v___x_4514_ = crate::leanh::lean_apply_6(
        v_inst_4506_,
        v___f_4511_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4507_,
        v___x_4513_,
        v___f_4512_,
    );
    return v___x_4514_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f(
    mut v_00_u03b1_4515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4516_: *mut crate::leanh::LeanObject,
    mut v_m_4517_: *mut crate::leanh::LeanObject,
    mut v_inst_4518_: *mut crate::leanh::LeanObject,
    mut v_inst_4519_: *mut crate::leanh::LeanObject,
    mut v_inst_4520_: *mut crate::leanh::LeanObject,
    mut v_inst_4521_: *mut crate::leanh::LeanObject,
    mut v_it_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4523_ = crate::leanh::lean_ctor_get(v_inst_4518_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4523_);
    v_toBind_4524_ = crate::leanh::lean_ctor_get(v_inst_4518_, 1);
    crate::leanh::lean_inc(v_toBind_4524_);
    crate::leanh::lean_dec_ref(v_inst_4518_);
    v_toPure_4525_ = crate::leanh::lean_ctor_get(v_toApplicative_4523_, 1);
    crate::leanh::lean_inc(v_toPure_4525_);
    crate::leanh::lean_dec_ref(v_toApplicative_4523_);
    v___f_4526_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4526_, 0, v_toBind_4524_);
    v___f_4527_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4527_, 0, v_toPure_4525_);
    v___x_4528_ = crate::leanh::lean_box(0);
    v___x_4529_ = crate::leanh::lean_apply_6(
        v_inst_4520_,
        v___f_4526_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4522_,
        v___x_4528_,
        v___f_4527_,
    );
    return v___x_4529_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f___boxed(
    mut v_00_u03b1_4530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4531_: *mut crate::leanh::LeanObject,
    mut v_m_4532_: *mut crate::leanh::LeanObject,
    mut v_inst_4533_: *mut crate::leanh::LeanObject,
    mut v_inst_4534_: *mut crate::leanh::LeanObject,
    mut v_inst_4535_: *mut crate::leanh::LeanObject,
    mut v_inst_4536_: *mut crate::leanh::LeanObject,
    mut v_it_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4538_ = l_Std_IterM_Total_first_x3f(
        v_00_u03b1_4530_,
        v_00_u03b2_4531_,
        v_m_4532_,
        v_inst_4533_,
        v_inst_4534_,
        v_inst_4535_,
        v_inst_4536_,
        v_it_4537_,
    );
    crate::leanh::lean_dec(v_inst_4534_);
    return v_res_4538_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg___lam__1(
    mut v_toPure_4542_: *mut crate::leanh::LeanObject,
    mut v_x_4543_: *mut crate::leanh::LeanObject,
    mut v_x_4544_: *mut crate::leanh::LeanObject,
    mut v_x_4545_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Std_IterM_isEmpty___redArg___lam__1___closed__0;
    v___x_4547_ =
        crate::leanh::lean_apply_2(v_toPure_4542_, crate::leanh::lean_box(0), v___x_4546_);
    return v___x_4547_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg___lam__1___boxed(
    mut v_toPure_4548_: *mut crate::leanh::LeanObject,
    mut v_x_4549_: *mut crate::leanh::LeanObject,
    mut v_x_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_79__boxed_4552_: u8 = 0;
    let mut v_res_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_79__boxed_4552_ = (crate::leanh::lean_unbox(v_x_4551_) as u8);
    v_res_4553_ = l_Std_IterM_isEmpty___redArg___lam__1(
        v_toPure_4548_,
        v_x_4549_,
        v_x_4550_,
        v_x_79__boxed_4552_,
    );
    crate::leanh::lean_dec(v_x_4549_);
    return v_res_4553_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg(
    mut v_inst_4554_: *mut crate::leanh::LeanObject,
    mut v_inst_4555_: *mut crate::leanh::LeanObject,
    mut v_it_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4557_ = crate::leanh::lean_ctor_get(v_inst_4554_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4557_);
    v_toBind_4558_ = crate::leanh::lean_ctor_get(v_inst_4554_, 1);
    crate::leanh::lean_inc(v_toBind_4558_);
    crate::leanh::lean_dec_ref(v_inst_4554_);
    v_toPure_4559_ = crate::leanh::lean_ctor_get(v_toApplicative_4557_, 1);
    crate::leanh::lean_inc(v_toPure_4559_);
    crate::leanh::lean_dec_ref(v_toApplicative_4557_);
    v___f_4560_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4560_, 0, v_toBind_4558_);
    v___f_4561_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4561_, 0, v_toPure_4559_);
    v___x_4562_ = 1;
    v___x_4563_ = crate::leanh::lean_box((v___x_4562_) as usize);
    v___x_4564_ = crate::leanh::lean_apply_6(
        v_inst_4555_,
        v___f_4560_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4556_,
        v___x_4563_,
        v___f_4561_,
    );
    return v___x_4564_;
}
pub unsafe fn l_Std_IterM_isEmpty(
    mut v_00_u03b1_4565_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4566_: *mut crate::leanh::LeanObject,
    mut v_m_4567_: *mut crate::leanh::LeanObject,
    mut v_inst_4568_: *mut crate::leanh::LeanObject,
    mut v_inst_4569_: *mut crate::leanh::LeanObject,
    mut v_inst_4570_: *mut crate::leanh::LeanObject,
    mut v_it_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4572_ = crate::leanh::lean_ctor_get(v_inst_4568_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4572_);
    v_toBind_4573_ = crate::leanh::lean_ctor_get(v_inst_4568_, 1);
    crate::leanh::lean_inc(v_toBind_4573_);
    crate::leanh::lean_dec_ref(v_inst_4568_);
    v_toPure_4574_ = crate::leanh::lean_ctor_get(v_toApplicative_4572_, 1);
    crate::leanh::lean_inc(v_toPure_4574_);
    crate::leanh::lean_dec_ref(v_toApplicative_4572_);
    v___f_4575_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4575_, 0, v_toBind_4573_);
    v___f_4576_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4576_, 0, v_toPure_4574_);
    v___x_4577_ = 1;
    v___x_4578_ = crate::leanh::lean_box((v___x_4577_) as usize);
    v___x_4579_ = crate::leanh::lean_apply_6(
        v_inst_4570_,
        v___f_4575_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4571_,
        v___x_4578_,
        v___f_4576_,
    );
    return v___x_4579_;
}
pub unsafe fn l_Std_IterM_isEmpty___boxed(
    mut v_00_u03b1_4580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4581_: *mut crate::leanh::LeanObject,
    mut v_m_4582_: *mut crate::leanh::LeanObject,
    mut v_inst_4583_: *mut crate::leanh::LeanObject,
    mut v_inst_4584_: *mut crate::leanh::LeanObject,
    mut v_inst_4585_: *mut crate::leanh::LeanObject,
    mut v_it_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4587_ = l_Std_IterM_isEmpty(
        v_00_u03b1_4580_,
        v_00_u03b2_4581_,
        v_m_4582_,
        v_inst_4583_,
        v_inst_4584_,
        v_inst_4585_,
        v_it_4586_,
    );
    crate::leanh::lean_dec(v_inst_4584_);
    return v_res_4587_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty___redArg(
    mut v_inst_4588_: *mut crate::leanh::LeanObject,
    mut v_inst_4589_: *mut crate::leanh::LeanObject,
    mut v_it_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4591_ = crate::leanh::lean_ctor_get(v_inst_4588_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4591_);
    v_toBind_4592_ = crate::leanh::lean_ctor_get(v_inst_4588_, 1);
    crate::leanh::lean_inc(v_toBind_4592_);
    crate::leanh::lean_dec_ref(v_inst_4588_);
    v_toPure_4593_ = crate::leanh::lean_ctor_get(v_toApplicative_4591_, 1);
    crate::leanh::lean_inc(v_toPure_4593_);
    crate::leanh::lean_dec_ref(v_toApplicative_4591_);
    v___f_4594_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4594_, 0, v_toBind_4592_);
    v___f_4595_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4595_, 0, v_toPure_4593_);
    v___x_4596_ = 1;
    v___x_4597_ = crate::leanh::lean_box((v___x_4596_) as usize);
    v___x_4598_ = crate::leanh::lean_apply_6(
        v_inst_4589_,
        v___f_4594_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4590_,
        v___x_4597_,
        v___f_4595_,
    );
    return v___x_4598_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty(
    mut v_00_u03b1_4599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4600_: *mut crate::leanh::LeanObject,
    mut v_m_4601_: *mut crate::leanh::LeanObject,
    mut v_inst_4602_: *mut crate::leanh::LeanObject,
    mut v_inst_4603_: *mut crate::leanh::LeanObject,
    mut v_inst_4604_: *mut crate::leanh::LeanObject,
    mut v_inst_4605_: *mut crate::leanh::LeanObject,
    mut v_it_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4607_ = crate::leanh::lean_ctor_get(v_inst_4602_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4607_);
    v_toBind_4608_ = crate::leanh::lean_ctor_get(v_inst_4602_, 1);
    crate::leanh::lean_inc(v_toBind_4608_);
    crate::leanh::lean_dec_ref(v_inst_4602_);
    v_toPure_4609_ = crate::leanh::lean_ctor_get(v_toApplicative_4607_, 1);
    crate::leanh::lean_inc(v_toPure_4609_);
    crate::leanh::lean_dec_ref(v_toApplicative_4607_);
    v___f_4610_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4610_, 0, v_toBind_4608_);
    v___f_4611_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4611_, 0, v_toPure_4609_);
    v___x_4612_ = 1;
    v___x_4613_ = crate::leanh::lean_box((v___x_4612_) as usize);
    v___x_4614_ = crate::leanh::lean_apply_6(
        v_inst_4604_,
        v___f_4610_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4606_,
        v___x_4613_,
        v___f_4611_,
    );
    return v___x_4614_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty___boxed(
    mut v_00_u03b1_4615_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4616_: *mut crate::leanh::LeanObject,
    mut v_m_4617_: *mut crate::leanh::LeanObject,
    mut v_inst_4618_: *mut crate::leanh::LeanObject,
    mut v_inst_4619_: *mut crate::leanh::LeanObject,
    mut v_inst_4620_: *mut crate::leanh::LeanObject,
    mut v_inst_4621_: *mut crate::leanh::LeanObject,
    mut v_it_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ = l_Std_IterM_Total_isEmpty(
        v_00_u03b1_4615_,
        v_00_u03b2_4616_,
        v_m_4617_,
        v_inst_4618_,
        v_inst_4619_,
        v_inst_4620_,
        v_inst_4621_,
        v_it_4622_,
    );
    crate::leanh::lean_dec(v_inst_4619_);
    return v_res_4623_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__1(
    mut v_toPure_4624_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = crate::leanh::lean_apply_2(
        v_toPure_4624_,
        crate::leanh::lean_box(0),
        v_____do__lift_4625_,
    );
    return v___x_4626_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__0(
    mut v_toPure_4627_: *mut crate::leanh::LeanObject,
    mut v_toBind_4628_: *mut crate::leanh::LeanObject,
    mut v___f_4629_: *mut crate::leanh::LeanObject,
    mut v_x1_4630_: *mut crate::leanh::LeanObject,
    mut v_x2_4631_: *mut crate::leanh::LeanObject,
    mut v_x3_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4634_ = lean_nat_add(v_x3_4632_, v___x_4633_);
    v___x_4635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4635_, 0, v___x_4634_);
    v___x_4636_ =
        crate::leanh::lean_apply_2(v_toPure_4627_, crate::leanh::lean_box(0), v___x_4635_);
    v___x_4637_ = crate::leanh::lean_apply_4(
        v_toBind_4628_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4636_,
        v___f_4629_,
    );
    return v___x_4637_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__0___boxed(
    mut v_toPure_4638_: *mut crate::leanh::LeanObject,
    mut v_toBind_4639_: *mut crate::leanh::LeanObject,
    mut v___f_4640_: *mut crate::leanh::LeanObject,
    mut v_x1_4641_: *mut crate::leanh::LeanObject,
    mut v_x2_4642_: *mut crate::leanh::LeanObject,
    mut v_x3_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Std_IterM_length___redArg___lam__0(
        v_toPure_4638_,
        v_toBind_4639_,
        v___f_4640_,
        v_x1_4641_,
        v_x2_4642_,
        v_x3_4643_,
    );
    crate::leanh::lean_dec(v_x3_4643_);
    crate::leanh::lean_dec(v_x1_4641_);
    return v_res_4644_;
}
pub unsafe fn l_Std_IterM_length___redArg(
    mut v_inst_4645_: *mut crate::leanh::LeanObject,
    mut v_inst_4646_: *mut crate::leanh::LeanObject,
    mut v_it_4647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4648_ = crate::leanh::lean_ctor_get(v_inst_4646_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4648_);
    v_toBind_4649_ = crate::leanh::lean_ctor_get(v_inst_4646_, 1);
    crate::leanh::lean_inc_n(v_toBind_4649_, 2);
    crate::leanh::lean_dec_ref(v_inst_4646_);
    v_toPure_4650_ = crate::leanh::lean_ctor_get(v_toApplicative_4648_, 1);
    crate::leanh::lean_inc_n(v_toPure_4650_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4648_);
    v___x_4651_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4652_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4652_, 0, v_toBind_4649_);
    v___f_4653_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4653_, 0, v_toPure_4650_);
    v___f_4654_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4654_, 0, v_toPure_4650_);
    crate::leanh::lean_closure_set(v___f_4654_, 1, v_toBind_4649_);
    crate::leanh::lean_closure_set(v___f_4654_, 2, v___f_4653_);
    v___x_4655_ = crate::leanh::lean_apply_6(
        v_inst_4645_,
        v___f_4652_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4647_,
        v___x_4651_,
        v___f_4654_,
    );
    return v___x_4655_;
}
pub unsafe fn l_Std_IterM_length(
    mut v_00_u03b1_4656_: *mut crate::leanh::LeanObject,
    mut v_m_4657_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4658_: *mut crate::leanh::LeanObject,
    mut v_inst_4659_: *mut crate::leanh::LeanObject,
    mut v_inst_4660_: *mut crate::leanh::LeanObject,
    mut v_inst_4661_: *mut crate::leanh::LeanObject,
    mut v_it_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4663_ = crate::leanh::lean_ctor_get(v_inst_4661_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4663_);
    v_toBind_4664_ = crate::leanh::lean_ctor_get(v_inst_4661_, 1);
    crate::leanh::lean_inc_n(v_toBind_4664_, 2);
    crate::leanh::lean_dec_ref(v_inst_4661_);
    v_toPure_4665_ = crate::leanh::lean_ctor_get(v_toApplicative_4663_, 1);
    crate::leanh::lean_inc_n(v_toPure_4665_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4663_);
    v___x_4666_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4667_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4667_, 0, v_toBind_4664_);
    v___f_4668_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4668_, 0, v_toPure_4665_);
    v___f_4669_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4669_, 0, v_toPure_4665_);
    crate::leanh::lean_closure_set(v___f_4669_, 1, v_toBind_4664_);
    crate::leanh::lean_closure_set(v___f_4669_, 2, v___f_4668_);
    v___x_4670_ = crate::leanh::lean_apply_6(
        v_inst_4660_,
        v___f_4667_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4662_,
        v___x_4666_,
        v___f_4669_,
    );
    return v___x_4670_;
}
pub unsafe fn l_Std_IterM_length___boxed(
    mut v_00_u03b1_4671_: *mut crate::leanh::LeanObject,
    mut v_m_4672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4673_: *mut crate::leanh::LeanObject,
    mut v_inst_4674_: *mut crate::leanh::LeanObject,
    mut v_inst_4675_: *mut crate::leanh::LeanObject,
    mut v_inst_4676_: *mut crate::leanh::LeanObject,
    mut v_it_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4678_ = l_Std_IterM_length(
        v_00_u03b1_4671_,
        v_m_4672_,
        v_00_u03b2_4673_,
        v_inst_4674_,
        v_inst_4675_,
        v_inst_4676_,
        v_it_4677_,
    );
    crate::leanh::lean_dec(v_inst_4674_);
    return v_res_4678_;
}
pub unsafe fn l_Std_IterM_count___redArg(
    mut v_inst_4679_: *mut crate::leanh::LeanObject,
    mut v_inst_4680_: *mut crate::leanh::LeanObject,
    mut v_it_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4682_ = crate::leanh::lean_ctor_get(v_inst_4680_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4682_);
    v_toBind_4683_ = crate::leanh::lean_ctor_get(v_inst_4680_, 1);
    crate::leanh::lean_inc_n(v_toBind_4683_, 2);
    crate::leanh::lean_dec_ref(v_inst_4680_);
    v_toPure_4684_ = crate::leanh::lean_ctor_get(v_toApplicative_4682_, 1);
    crate::leanh::lean_inc_n(v_toPure_4684_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4682_);
    v___x_4685_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4686_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4686_, 0, v_toBind_4683_);
    v___f_4687_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4687_, 0, v_toPure_4684_);
    v___f_4688_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4688_, 0, v_toPure_4684_);
    crate::leanh::lean_closure_set(v___f_4688_, 1, v_toBind_4683_);
    crate::leanh::lean_closure_set(v___f_4688_, 2, v___f_4687_);
    v___x_4689_ = crate::leanh::lean_apply_6(
        v_inst_4679_,
        v___f_4686_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4681_,
        v___x_4685_,
        v___f_4688_,
    );
    return v___x_4689_;
}
pub unsafe fn l_Std_IterM_count(
    mut v_00_u03b1_4690_: *mut crate::leanh::LeanObject,
    mut v_m_4691_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4692_: *mut crate::leanh::LeanObject,
    mut v_inst_4693_: *mut crate::leanh::LeanObject,
    mut v_inst_4694_: *mut crate::leanh::LeanObject,
    mut v_inst_4695_: *mut crate::leanh::LeanObject,
    mut v_it_4696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4697_ = crate::leanh::lean_ctor_get(v_inst_4695_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4697_);
    v_toBind_4698_ = crate::leanh::lean_ctor_get(v_inst_4695_, 1);
    crate::leanh::lean_inc_n(v_toBind_4698_, 2);
    crate::leanh::lean_dec_ref(v_inst_4695_);
    v_toPure_4699_ = crate::leanh::lean_ctor_get(v_toApplicative_4697_, 1);
    crate::leanh::lean_inc_n(v_toPure_4699_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4697_);
    v___x_4700_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4701_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4701_, 0, v_toBind_4698_);
    v___f_4702_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4702_, 0, v_toPure_4699_);
    v___f_4703_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4703_, 0, v_toPure_4699_);
    crate::leanh::lean_closure_set(v___f_4703_, 1, v_toBind_4698_);
    crate::leanh::lean_closure_set(v___f_4703_, 2, v___f_4702_);
    v___x_4704_ = crate::leanh::lean_apply_6(
        v_inst_4694_,
        v___f_4701_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4696_,
        v___x_4700_,
        v___f_4703_,
    );
    return v___x_4704_;
}
pub unsafe fn l_Std_IterM_count___boxed(
    mut v_00_u03b1_4705_: *mut crate::leanh::LeanObject,
    mut v_m_4706_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4707_: *mut crate::leanh::LeanObject,
    mut v_inst_4708_: *mut crate::leanh::LeanObject,
    mut v_inst_4709_: *mut crate::leanh::LeanObject,
    mut v_inst_4710_: *mut crate::leanh::LeanObject,
    mut v_it_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4712_ = l_Std_IterM_count(
        v_00_u03b1_4705_,
        v_m_4706_,
        v_00_u03b2_4707_,
        v_inst_4708_,
        v_inst_4709_,
        v_inst_4710_,
        v_it_4711_,
    );
    crate::leanh::lean_dec(v_inst_4708_);
    return v_res_4712_;
}
pub unsafe fn l_Std_IterM_size___redArg(
    mut v_inst_4713_: *mut crate::leanh::LeanObject,
    mut v_inst_4714_: *mut crate::leanh::LeanObject,
    mut v_it_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4716_ = crate::leanh::lean_ctor_get(v_inst_4714_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4716_);
    v_toBind_4717_ = crate::leanh::lean_ctor_get(v_inst_4714_, 1);
    crate::leanh::lean_inc_n(v_toBind_4717_, 2);
    crate::leanh::lean_dec_ref(v_inst_4714_);
    v_toPure_4718_ = crate::leanh::lean_ctor_get(v_toApplicative_4716_, 1);
    crate::leanh::lean_inc_n(v_toPure_4718_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4716_);
    v___x_4719_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4720_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4720_, 0, v_toBind_4717_);
    v___f_4721_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4721_, 0, v_toPure_4718_);
    v___f_4722_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4722_, 0, v_toPure_4718_);
    crate::leanh::lean_closure_set(v___f_4722_, 1, v_toBind_4717_);
    crate::leanh::lean_closure_set(v___f_4722_, 2, v___f_4721_);
    v___x_4723_ = crate::leanh::lean_apply_6(
        v_inst_4713_,
        v___f_4720_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4715_,
        v___x_4719_,
        v___f_4722_,
    );
    return v___x_4723_;
}
pub unsafe fn l_Std_IterM_size(
    mut v_00_u03b1_4724_: *mut crate::leanh::LeanObject,
    mut v_m_4725_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4726_: *mut crate::leanh::LeanObject,
    mut v_inst_4727_: *mut crate::leanh::LeanObject,
    mut v_inst_4728_: *mut crate::leanh::LeanObject,
    mut v_inst_4729_: *mut crate::leanh::LeanObject,
    mut v_it_4730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4731_ = crate::leanh::lean_ctor_get(v_inst_4729_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4731_);
    v_toBind_4732_ = crate::leanh::lean_ctor_get(v_inst_4729_, 1);
    crate::leanh::lean_inc_n(v_toBind_4732_, 2);
    crate::leanh::lean_dec_ref(v_inst_4729_);
    v_toPure_4733_ = crate::leanh::lean_ctor_get(v_toApplicative_4731_, 1);
    crate::leanh::lean_inc_n(v_toPure_4733_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4731_);
    v___x_4734_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4735_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4735_, 0, v_toBind_4732_);
    v___f_4736_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4736_, 0, v_toPure_4733_);
    v___f_4737_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4737_, 0, v_toPure_4733_);
    crate::leanh::lean_closure_set(v___f_4737_, 1, v_toBind_4732_);
    crate::leanh::lean_closure_set(v___f_4737_, 2, v___f_4736_);
    v___x_4738_ = crate::leanh::lean_apply_6(
        v_inst_4728_,
        v___f_4735_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4730_,
        v___x_4734_,
        v___f_4737_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Std_IterM_size___boxed(
    mut v_00_u03b1_4739_: *mut crate::leanh::LeanObject,
    mut v_m_4740_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4741_: *mut crate::leanh::LeanObject,
    mut v_inst_4742_: *mut crate::leanh::LeanObject,
    mut v_inst_4743_: *mut crate::leanh::LeanObject,
    mut v_inst_4744_: *mut crate::leanh::LeanObject,
    mut v_it_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Std_IterM_size(
        v_00_u03b1_4739_,
        v_m_4740_,
        v_00_u03b2_4741_,
        v_inst_4742_,
        v_inst_4743_,
        v_inst_4744_,
        v_it_4745_,
    );
    crate::leanh::lean_dec(v_inst_4742_);
    return v_res_4746_;
}
pub unsafe fn l_Std_IterM_Partial_count___redArg(
    mut v_inst_4747_: *mut crate::leanh::LeanObject,
    mut v_inst_4748_: *mut crate::leanh::LeanObject,
    mut v_it_4749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4750_ = crate::leanh::lean_ctor_get(v_inst_4748_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4750_);
    v_toBind_4751_ = crate::leanh::lean_ctor_get(v_inst_4748_, 1);
    crate::leanh::lean_inc_n(v_toBind_4751_, 2);
    crate::leanh::lean_dec_ref(v_inst_4748_);
    v_toPure_4752_ = crate::leanh::lean_ctor_get(v_toApplicative_4750_, 1);
    crate::leanh::lean_inc_n(v_toPure_4752_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4750_);
    v___x_4753_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4754_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4754_, 0, v_toBind_4751_);
    v___f_4755_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4755_, 0, v_toPure_4752_);
    v___f_4756_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4756_, 0, v_toPure_4752_);
    crate::leanh::lean_closure_set(v___f_4756_, 1, v_toBind_4751_);
    crate::leanh::lean_closure_set(v___f_4756_, 2, v___f_4755_);
    v___x_4757_ = crate::leanh::lean_apply_6(
        v_inst_4747_,
        v___f_4754_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4749_,
        v___x_4753_,
        v___f_4756_,
    );
    return v___x_4757_;
}
pub unsafe fn l_Std_IterM_Partial_count(
    mut v_00_u03b1_4758_: *mut crate::leanh::LeanObject,
    mut v_m_4759_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4760_: *mut crate::leanh::LeanObject,
    mut v_inst_4761_: *mut crate::leanh::LeanObject,
    mut v_inst_4762_: *mut crate::leanh::LeanObject,
    mut v_inst_4763_: *mut crate::leanh::LeanObject,
    mut v_it_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4765_ = crate::leanh::lean_ctor_get(v_inst_4763_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4765_);
    v_toBind_4766_ = crate::leanh::lean_ctor_get(v_inst_4763_, 1);
    crate::leanh::lean_inc_n(v_toBind_4766_, 2);
    crate::leanh::lean_dec_ref(v_inst_4763_);
    v_toPure_4767_ = crate::leanh::lean_ctor_get(v_toApplicative_4765_, 1);
    crate::leanh::lean_inc_n(v_toPure_4767_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4765_);
    v___x_4768_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4769_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4769_, 0, v_toBind_4766_);
    v___f_4770_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4770_, 0, v_toPure_4767_);
    v___f_4771_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4771_, 0, v_toPure_4767_);
    crate::leanh::lean_closure_set(v___f_4771_, 1, v_toBind_4766_);
    crate::leanh::lean_closure_set(v___f_4771_, 2, v___f_4770_);
    v___x_4772_ = crate::leanh::lean_apply_6(
        v_inst_4762_,
        v___f_4769_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4764_,
        v___x_4768_,
        v___f_4771_,
    );
    return v___x_4772_;
}
pub unsafe fn l_Std_IterM_Partial_count___boxed(
    mut v_00_u03b1_4773_: *mut crate::leanh::LeanObject,
    mut v_m_4774_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4775_: *mut crate::leanh::LeanObject,
    mut v_inst_4776_: *mut crate::leanh::LeanObject,
    mut v_inst_4777_: *mut crate::leanh::LeanObject,
    mut v_inst_4778_: *mut crate::leanh::LeanObject,
    mut v_it_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4780_ = l_Std_IterM_Partial_count(
        v_00_u03b1_4773_,
        v_m_4774_,
        v_00_u03b2_4775_,
        v_inst_4776_,
        v_inst_4777_,
        v_inst_4778_,
        v_it_4779_,
    );
    crate::leanh::lean_dec(v_inst_4776_);
    return v_res_4780_;
}
pub unsafe fn l_Std_IterM_Partial_size___redArg(
    mut v_inst_4781_: *mut crate::leanh::LeanObject,
    mut v_inst_4782_: *mut crate::leanh::LeanObject,
    mut v_it_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4784_ = crate::leanh::lean_ctor_get(v_inst_4782_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4784_);
    v_toBind_4785_ = crate::leanh::lean_ctor_get(v_inst_4782_, 1);
    crate::leanh::lean_inc_n(v_toBind_4785_, 2);
    crate::leanh::lean_dec_ref(v_inst_4782_);
    v_toPure_4786_ = crate::leanh::lean_ctor_get(v_toApplicative_4784_, 1);
    crate::leanh::lean_inc_n(v_toPure_4786_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4784_);
    v___x_4787_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4788_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4788_, 0, v_toBind_4785_);
    v___f_4789_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4789_, 0, v_toPure_4786_);
    v___f_4790_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4790_, 0, v_toPure_4786_);
    crate::leanh::lean_closure_set(v___f_4790_, 1, v_toBind_4785_);
    crate::leanh::lean_closure_set(v___f_4790_, 2, v___f_4789_);
    v___x_4791_ = crate::leanh::lean_apply_6(
        v_inst_4781_,
        v___f_4788_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4783_,
        v___x_4787_,
        v___f_4790_,
    );
    return v___x_4791_;
}
pub unsafe fn l_Std_IterM_Partial_size(
    mut v_00_u03b1_4792_: *mut crate::leanh::LeanObject,
    mut v_m_4793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4794_: *mut crate::leanh::LeanObject,
    mut v_inst_4795_: *mut crate::leanh::LeanObject,
    mut v_inst_4796_: *mut crate::leanh::LeanObject,
    mut v_inst_4797_: *mut crate::leanh::LeanObject,
    mut v_it_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4799_ = crate::leanh::lean_ctor_get(v_inst_4797_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4799_);
    v_toBind_4800_ = crate::leanh::lean_ctor_get(v_inst_4797_, 1);
    crate::leanh::lean_inc_n(v_toBind_4800_, 2);
    crate::leanh::lean_dec_ref(v_inst_4797_);
    v_toPure_4801_ = crate::leanh::lean_ctor_get(v_toApplicative_4799_, 1);
    crate::leanh::lean_inc_n(v_toPure_4801_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4799_);
    v___x_4802_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_4803_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4803_, 0, v_toBind_4800_);
    v___f_4804_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4804_, 0, v_toPure_4801_);
    v___f_4805_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4805_, 0, v_toPure_4801_);
    crate::leanh::lean_closure_set(v___f_4805_, 1, v_toBind_4800_);
    crate::leanh::lean_closure_set(v___f_4805_, 2, v___f_4804_);
    v___x_4806_ = crate::leanh::lean_apply_6(
        v_inst_4796_,
        v___f_4803_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_it_4798_,
        v___x_4802_,
        v___f_4805_,
    );
    return v___x_4806_;
}
pub unsafe fn l_Std_IterM_Partial_size___boxed(
    mut v_00_u03b1_4807_: *mut crate::leanh::LeanObject,
    mut v_m_4808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4809_: *mut crate::leanh::LeanObject,
    mut v_inst_4810_: *mut crate::leanh::LeanObject,
    mut v_inst_4811_: *mut crate::leanh::LeanObject,
    mut v_inst_4812_: *mut crate::leanh::LeanObject,
    mut v_it_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4814_ = l_Std_IterM_Partial_size(
        v_00_u03b1_4807_,
        v_m_4808_,
        v_00_u03b2_4809_,
        v_inst_4810_,
        v_inst_4811_,
        v_inst_4812_,
        v_it_4813_,
    );
    crate::leanh::lean_dec(v_inst_4810_);
    return v_res_4814_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
}
