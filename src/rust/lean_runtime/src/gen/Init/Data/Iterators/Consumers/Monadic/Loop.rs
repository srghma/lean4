// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Loop
// Imports: Init.Data.Iterators.Consumers.Monadic.Partial Init.Data.Iterators.Internal.LawfulMonadLiftFunction Init.WFExtrinsicFix Init.Data.Iterators.Consumers.Monadic.Total Init.PropLemmas
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
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Std_IterM_foldM___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_IterM_foldM___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_IterM_foldM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IterM_foldM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_IterM_isEmpty___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_IteratorLoop_WithWF_instWellFoundedRelation(
    mut v_00_u03b1_2408_: *mut LeanObject,
    mut v_m_2409_: *mut LeanObject,
    mut v_00_u03b2_2410_: *mut LeanObject,
    mut v_inst_2411_: *mut LeanObject,
    mut v_00_u03b3_2412_: *mut LeanObject,
    mut v_PlausibleForInStep_2413_: *mut LeanObject,
    mut v_hwf_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2415_ = lean_box(0);
    return v___x_2415_;
}
pub unsafe fn l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(
    mut v_00_u03b1_2416_: *mut LeanObject,
    mut v_m_2417_: *mut LeanObject,
    mut v_00_u03b2_2418_: *mut LeanObject,
    mut v_inst_2419_: *mut LeanObject,
    mut v_00_u03b3_2420_: *mut LeanObject,
    mut v_PlausibleForInStep_2421_: *mut LeanObject,
    mut v_hwf_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2423_: *mut LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(
        v_00_u03b1_2416_,
        v_m_2417_,
        v_00_u03b2_2418_,
        v_inst_2419_,
        v_00_u03b3_2420_,
        v_PlausibleForInStep_2421_,
        v_hwf_2422_,
    );
    lean_dec(v_inst_2419_);
    return v_res_2423_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(
    mut v_toPure_2424_: *mut LeanObject,
    mut v_recur_2425_: *mut LeanObject,
    mut v_it_2426_: *mut LeanObject,
    mut v_____do__lift_2427_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2427_) == 0 {
        let mut v_a_2428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_2426_);
        lean_dec(v_recur_2425_);
        v_a_2428_ = lean_ctor_get(v_____do__lift_2427_, 0);
        lean_inc(v_a_2428_);
        lean_dec_ref_known(v_____do__lift_2427_, 1);
        v___x_2429_ = lean_apply_2(v_toPure_2424_, lean_box(0), v_a_2428_);
        return v___x_2429_;
    } else {
        let mut v_a_2430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2424_);
        v_a_2430_ = lean_ctor_get(v_____do__lift_2427_, 0);
        lean_inc(v_a_2430_);
        lean_dec_ref_known(v_____do__lift_2427_, 1);
        v___x_2431_ = lean_apply_4(
            v_recur_2425_,
            v_it_2426_,
            v_a_2430_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_2431_;
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(
    mut v_toPure_2432_: *mut LeanObject,
    mut v_recur_2433_: *mut LeanObject,
    mut v_f_2434_: *mut LeanObject,
    mut v_acc_2435_: *mut LeanObject,
    mut v_toBind_2436_: *mut LeanObject,
    mut v_s_2437_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_2437_) {
        0 => {
            let mut v_it_2438_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2440_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
            v_it_2438_ = lean_ctor_get(v_s_2437_, 0);
            lean_inc(v_it_2438_);
            v_out_2439_ = lean_ctor_get(v_s_2437_, 1);
            lean_inc(v_out_2439_);
            lean_dec_ref_known(v_s_2437_, 2);
            v___f_2440_ = lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_2440_, 0, v_toPure_2432_);
            lean_closure_set(v___f_2440_, 1, v_recur_2433_);
            lean_closure_set(v___f_2440_, 2, v_it_2438_);
            v___x_2441_ = lean_apply_3(v_f_2434_, v_out_2439_, lean_box(0), v_acc_2435_);
            v___x_2442_ = lean_apply_4(
                v_toBind_2436_,
                lean_box(0),
                lean_box(0),
                v___x_2441_,
                v___f_2440_,
            );
            return v___x_2442_;
        }
        1 => {
            let mut v_it_2443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2436_);
            lean_dec(v_f_2434_);
            lean_dec(v_toPure_2432_);
            v_it_2443_ = lean_ctor_get(v_s_2437_, 0);
            lean_inc(v_it_2443_);
            lean_dec_ref_known(v_s_2437_, 1);
            v___x_2444_ = lean_apply_4(
                v_recur_2433_,
                v_it_2443_,
                v_acc_2435_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_2444_;
        }
        _ => {
            let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2436_);
            lean_dec(v_f_2434_);
            lean_dec(v_recur_2433_);
            v___x_2445_ = lean_apply_2(v_toPure_2432_, lean_box(0), v_acc_2435_);
            return v___x_2445_;
        }
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(
    mut v_toPure_2446_: *mut LeanObject,
    mut v_f_2447_: *mut LeanObject,
    mut v_toBind_2448_: *mut LeanObject,
    mut v_inst_2449_: *mut LeanObject,
    mut v_lift_2450_: *mut LeanObject,
    mut v_it_2451_: *mut LeanObject,
    mut v_acc_2452_: *mut LeanObject,
    mut v_hP_2453_: *mut LeanObject,
    mut v_recur_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___f_2455_ = lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2455_, 0, v_toPure_2446_);
    lean_closure_set(v___f_2455_, 1, v_recur_2454_);
    lean_closure_set(v___f_2455_, 2, v_f_2447_);
    lean_closure_set(v___f_2455_, 3, v_acc_2452_);
    lean_closure_set(v___f_2455_, 4, v_toBind_2448_);
    v___x_2456_ = lean_apply_1(v_inst_2449_, v_it_2451_);
    v___x_2457_ = lean_apply_4(
        v_lift_2450_,
        lean_box(0),
        lean_box(0),
        v___f_2455_,
        v___x_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27___redArg(
    mut v_inst_2458_: *mut LeanObject,
    mut v_inst_2459_: *mut LeanObject,
    mut v_lift_2460_: *mut LeanObject,
    mut v_it_2461_: *mut LeanObject,
    mut v_init_2462_: *mut LeanObject,
    mut v_f_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2464_ = lean_ctor_get(v_inst_2459_, 0);
    lean_inc_ref(v_toApplicative_2464_);
    v_toBind_2465_ = lean_ctor_get(v_inst_2459_, 1);
    lean_inc(v_toBind_2465_);
    lean_dec_ref(v_inst_2459_);
    v_toPure_2466_ = lean_ctor_get(v_toApplicative_2464_, 1);
    lean_inc(v_toPure_2466_);
    lean_dec_ref(v_toApplicative_2464_);
    v___f_2467_ = lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_2467_, 0, v_toPure_2466_);
    lean_closure_set(v___f_2467_, 1, v_f_2463_);
    lean_closure_set(v___f_2467_, 2, v_toBind_2465_);
    lean_closure_set(v___f_2467_, 3, v_inst_2458_);
    lean_closure_set(v___f_2467_, 4, v_lift_2460_);
    v___x_2468_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2467_, v_it_2461_, v_init_2462_, lean_box(0));
    return v___x_2468_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27(
    mut v_m_2469_: *mut LeanObject,
    mut v_00_u03b1_2470_: *mut LeanObject,
    mut v_00_u03b2_2471_: *mut LeanObject,
    mut v_inst_2472_: *mut LeanObject,
    mut v_n_2473_: *mut LeanObject,
    mut v_inst_2474_: *mut LeanObject,
    mut v_lift_2475_: *mut LeanObject,
    mut v_00_u03b3_2476_: *mut LeanObject,
    mut v_PlausibleForInStep_2477_: *mut LeanObject,
    mut v_it_2478_: *mut LeanObject,
    mut v_init_2479_: *mut LeanObject,
    mut v_P_2480_: *mut LeanObject,
    mut v_hP_2481_: *mut LeanObject,
    mut v_f_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2483_ = lean_ctor_get(v_inst_2474_, 0);
    lean_inc_ref(v_toApplicative_2483_);
    v_toBind_2484_ = lean_ctor_get(v_inst_2474_, 1);
    lean_inc(v_toBind_2484_);
    lean_dec_ref(v_inst_2474_);
    v_toPure_2485_ = lean_ctor_get(v_toApplicative_2483_, 1);
    lean_inc(v_toPure_2485_);
    lean_dec_ref(v_toApplicative_2483_);
    v___f_2486_ = lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_2486_, 0, v_toPure_2485_);
    lean_closure_set(v___f_2486_, 1, v_f_2482_);
    lean_closure_set(v___f_2486_, 2, v_toBind_2484_);
    lean_closure_set(v___f_2486_, 3, v_inst_2472_);
    lean_closure_set(v___f_2486_, 4, v_lift_2475_);
    v___x_2487_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2486_, v_it_2478_, v_init_2479_, lean_box(0));
    return v___x_2487_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(
    mut v_toPure_2488_: *mut LeanObject,
    mut v_inst_2489_: *mut LeanObject,
    mut v_inst_2490_: *mut LeanObject,
    mut v_lift_2491_: *mut LeanObject,
    mut v_f_2492_: *mut LeanObject,
    mut v_init_2493_: *mut LeanObject,
    mut v_toBind_2494_: *mut LeanObject,
    mut v_s_2495_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_2495_) {
        0 => {
            let mut v_it_2496_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2497_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2498_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
            v_it_2496_ = lean_ctor_get(v_s_2495_, 0);
            lean_inc(v_it_2496_);
            v_out_2497_ = lean_ctor_get(v_s_2495_, 1);
            lean_inc(v_out_2497_);
            lean_dec_ref_known(v_s_2495_, 2);
            lean_inc(v_f_2492_);
            v___f_2498_ = lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0
                    as *mut core::ffi::c_void,
                7,
                6,
            );
            lean_closure_set(v___f_2498_, 0, v_toPure_2488_);
            lean_closure_set(v___f_2498_, 1, v_inst_2489_);
            lean_closure_set(v___f_2498_, 2, v_inst_2490_);
            lean_closure_set(v___f_2498_, 3, v_lift_2491_);
            lean_closure_set(v___f_2498_, 4, v_it_2496_);
            lean_closure_set(v___f_2498_, 5, v_f_2492_);
            v___x_2499_ = lean_apply_3(v_f_2492_, v_out_2497_, lean_box(0), v_init_2493_);
            v___x_2500_ = lean_apply_4(
                v_toBind_2494_,
                lean_box(0),
                lean_box(0),
                v___x_2499_,
                v___f_2498_,
            );
            return v___x_2500_;
        }
        1 => {
            let mut v_it_2501_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2494_);
            lean_dec(v_toPure_2488_);
            v_it_2501_ = lean_ctor_get(v_s_2495_, 0);
            lean_inc(v_it_2501_);
            lean_dec_ref_known(v_s_2495_, 1);
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
            let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2494_);
            lean_dec(v_f_2492_);
            lean_dec(v_lift_2491_);
            lean_dec_ref(v_inst_2490_);
            lean_dec(v_inst_2489_);
            v___x_2503_ = lean_apply_2(v_toPure_2488_, lean_box(0), v_init_2493_);
            return v___x_2503_;
        }
    }
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(
    mut v_inst_2504_: *mut LeanObject,
    mut v_inst_2505_: *mut LeanObject,
    mut v_lift_2506_: *mut LeanObject,
    mut v_it_2507_: *mut LeanObject,
    mut v_init_2508_: *mut LeanObject,
    mut v_f_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2510_ = lean_ctor_get(v_inst_2505_, 0);
    v_toBind_2511_ = lean_ctor_get(v_inst_2505_, 1);
    lean_inc(v_toBind_2511_);
    v_toPure_2512_ = lean_ctor_get(v_toApplicative_2510_, 1);
    lean_inc(v_toPure_2512_);
    lean_inc(v_lift_2506_);
    lean_inc(v_inst_2504_);
    v___f_2513_ = lean_alloc_closure(
        l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2513_, 0, v_toPure_2512_);
    lean_closure_set(v___f_2513_, 1, v_inst_2504_);
    lean_closure_set(v___f_2513_, 2, v_inst_2505_);
    lean_closure_set(v___f_2513_, 3, v_lift_2506_);
    lean_closure_set(v___f_2513_, 4, v_f_2509_);
    lean_closure_set(v___f_2513_, 5, v_init_2508_);
    lean_closure_set(v___f_2513_, 6, v_toBind_2511_);
    v___x_2514_ = lean_apply_1(v_inst_2504_, v_it_2507_);
    v___x_2515_ = lean_apply_4(
        v_lift_2506_,
        lean_box(0),
        lean_box(0),
        v___f_2513_,
        v___x_2514_,
    );
    return v___x_2515_;
}
pub unsafe fn l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(
    mut v_toPure_2516_: *mut LeanObject,
    mut v_inst_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_lift_2519_: *mut LeanObject,
    mut v_it_2520_: *mut LeanObject,
    mut v_f_2521_: *mut LeanObject,
    mut v_____do__lift_2522_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2522_) == 0 {
        let mut v_a_2523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_2521_);
        lean_dec(v_it_2520_);
        lean_dec(v_lift_2519_);
        lean_dec_ref(v_inst_2518_);
        lean_dec(v_inst_2517_);
        v_a_2523_ = lean_ctor_get(v_____do__lift_2522_, 0);
        lean_inc(v_a_2523_);
        lean_dec_ref_known(v_____do__lift_2522_, 1);
        v___x_2524_ = lean_apply_2(v_toPure_2516_, lean_box(0), v_a_2523_);
        return v___x_2524_;
    } else {
        let mut v_a_2525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2516_);
        v_a_2525_ = lean_ctor_get(v_____do__lift_2522_, 0);
        lean_inc(v_a_2525_);
        lean_dec_ref_known(v_____do__lift_2522_, 1);
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
    mut v_m_2527_: *mut LeanObject,
    mut v_00_u03b1_2528_: *mut LeanObject,
    mut v_00_u03b2_2529_: *mut LeanObject,
    mut v_inst_2530_: *mut LeanObject,
    mut v_n_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_lift_2533_: *mut LeanObject,
    mut v_00_u03b3_2534_: *mut LeanObject,
    mut v_PlausibleForInStep_2535_: *mut LeanObject,
    mut v_wf_2536_: *mut LeanObject,
    mut v_it_2537_: *mut LeanObject,
    mut v_init_2538_: *mut LeanObject,
    mut v_P_2539_: *mut LeanObject,
    mut v_hP_2540_: *mut LeanObject,
    mut v_f_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2543_: *mut LeanObject,
    mut v_h__1_2544_: *mut LeanObject,
    mut v_h__2_2545_: *mut LeanObject,
    mut v_h__3_2546_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2543_) {
        0 => {
            let mut v_it_2547_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2548_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2546_);
            lean_dec(v_h__2_2545_);
            v_it_2547_ = lean_ctor_get(v_x_2543_, 0);
            lean_inc(v_it_2547_);
            v_out_2548_ = lean_ctor_get(v_x_2543_, 1);
            lean_inc(v_out_2548_);
            lean_dec_ref_known(v_x_2543_, 2);
            v___x_2549_ = lean_apply_3(v_h__1_2544_, v_it_2547_, v_out_2548_, lean_box(0));
            return v___x_2549_;
        }
        1 => {
            let mut v_it_2550_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2546_);
            lean_dec(v_h__1_2544_);
            v_it_2550_ = lean_ctor_get(v_x_2543_, 0);
            lean_inc(v_it_2550_);
            lean_dec_ref_known(v_x_2543_, 1);
            v___x_2551_ = lean_apply_2(v_h__2_2545_, v_it_2550_, lean_box(0));
            return v___x_2551_;
        }
        _ => {
            let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2545_);
            lean_dec(v_h__1_2544_);
            v___x_2552_ = lean_apply_1(v_h__3_2546_, lean_box(0));
            return v___x_2552_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_2553_: *mut LeanObject,
    mut v_00_u03b1_2554_: *mut LeanObject,
    mut v_00_u03b2_2555_: *mut LeanObject,
    mut v_inst_2556_: *mut LeanObject,
    mut v_it_2557_: *mut LeanObject,
    mut v_motive_2558_: *mut LeanObject,
    mut v_x_2559_: *mut LeanObject,
    mut v_h__1_2560_: *mut LeanObject,
    mut v_h__2_2561_: *mut LeanObject,
    mut v_h__3_2562_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2559_) {
        0 => {
            let mut v_it_2563_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2562_);
            lean_dec(v_h__2_2561_);
            v_it_2563_ = lean_ctor_get(v_x_2559_, 0);
            lean_inc(v_it_2563_);
            v_out_2564_ = lean_ctor_get(v_x_2559_, 1);
            lean_inc(v_out_2564_);
            lean_dec_ref_known(v_x_2559_, 2);
            v___x_2565_ = lean_apply_3(v_h__1_2560_, v_it_2563_, v_out_2564_, lean_box(0));
            return v___x_2565_;
        }
        1 => {
            let mut v_it_2566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2562_);
            lean_dec(v_h__1_2560_);
            v_it_2566_ = lean_ctor_get(v_x_2559_, 0);
            lean_inc(v_it_2566_);
            lean_dec_ref_known(v_x_2559_, 1);
            v___x_2567_ = lean_apply_2(v_h__2_2561_, v_it_2566_, lean_box(0));
            return v___x_2567_;
        }
        _ => {
            let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2561_);
            lean_dec(v_h__1_2560_);
            v___x_2568_ = lean_apply_1(v_h__3_2562_, lean_box(0));
            return v___x_2568_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_2569_: *mut LeanObject,
    mut v_00_u03b1_2570_: *mut LeanObject,
    mut v_00_u03b2_2571_: *mut LeanObject,
    mut v_inst_2572_: *mut LeanObject,
    mut v_it_2573_: *mut LeanObject,
    mut v_motive_2574_: *mut LeanObject,
    mut v_x_2575_: *mut LeanObject,
    mut v_h__1_2576_: *mut LeanObject,
    mut v_h__2_2577_: *mut LeanObject,
    mut v_h__3_2578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2579_: *mut LeanObject = core::ptr::null_mut();
    v_res_2579_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_2569_, v_00_u03b1_2570_, v_00_u03b2_2571_, v_inst_2572_, v_it_2573_, v_motive_2574_, v_x_2575_, v_h__1_2576_, v_h__2_2577_, v_h__3_2578_);
    lean_dec(v_it_2573_);
    lean_dec(v_inst_2572_);
    return v_res_2579_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_2580_: *mut LeanObject,
    mut v_h__1_2581_: *mut LeanObject,
    mut v_h__2_2582_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2580_) == 0 {
        let mut v_a_2583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2581_);
        v_a_2583_ = lean_ctor_get(v_____do__lift_2580_, 0);
        lean_inc(v_a_2583_);
        lean_dec_ref_known(v_____do__lift_2580_, 1);
        v___x_2584_ = lean_apply_2(v_h__2_2582_, v_a_2583_, lean_box(0));
        return v___x_2584_;
    } else {
        let mut v_a_2585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2582_);
        v_a_2585_ = lean_ctor_get(v_____do__lift_2580_, 0);
        lean_inc(v_a_2585_);
        lean_dec_ref_known(v_____do__lift_2580_, 1);
        v___x_2586_ = lean_apply_2(v_h__1_2581_, v_a_2585_, lean_box(0));
        return v___x_2586_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_2587_: *mut LeanObject,
    mut v_00_u03b3_2588_: *mut LeanObject,
    mut v_PlausibleForInStep_2589_: *mut LeanObject,
    mut v_acc_2590_: *mut LeanObject,
    mut v_out_2591_: *mut LeanObject,
    mut v_motive_2592_: *mut LeanObject,
    mut v_____do__lift_2593_: *mut LeanObject,
    mut v_h__1_2594_: *mut LeanObject,
    mut v_h__2_2595_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2593_) == 0 {
        let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2594_);
        v_a_2596_ = lean_ctor_get(v_____do__lift_2593_, 0);
        lean_inc(v_a_2596_);
        lean_dec_ref_known(v_____do__lift_2593_, 1);
        v___x_2597_ = lean_apply_2(v_h__2_2595_, v_a_2596_, lean_box(0));
        return v___x_2597_;
    } else {
        let mut v_a_2598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2595_);
        v_a_2598_ = lean_ctor_get(v_____do__lift_2593_, 0);
        lean_inc(v_a_2598_);
        lean_dec_ref_known(v_____do__lift_2593_, 1);
        v___x_2599_ = lean_apply_2(v_h__1_2594_, v_a_2598_, lean_box(0));
        return v___x_2599_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_2600_: *mut LeanObject,
    mut v_00_u03b3_2601_: *mut LeanObject,
    mut v_PlausibleForInStep_2602_: *mut LeanObject,
    mut v_acc_2603_: *mut LeanObject,
    mut v_out_2604_: *mut LeanObject,
    mut v_motive_2605_: *mut LeanObject,
    mut v_____do__lift_2606_: *mut LeanObject,
    mut v_h__1_2607_: *mut LeanObject,
    mut v_h__2_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2609_: *mut LeanObject = core::ptr::null_mut();
    v_res_2609_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_2600_, v_00_u03b3_2601_, v_PlausibleForInStep_2602_, v_acc_2603_, v_out_2604_, v_motive_2605_, v_____do__lift_2606_, v_h__1_2607_, v_h__2_2608_);
    lean_dec(v_out_2604_);
    lean_dec(v_acc_2603_);
    return v_res_2609_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(
    mut v_toPure_2610_: *mut LeanObject,
    mut v_recur_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v_acc_2613_: *mut LeanObject,
    mut v_toBind_2614_: *mut LeanObject,
    mut v_s_2615_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_2615_) {
        0 => {
            let mut v_it_2616_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2618_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
            v_it_2616_ = lean_ctor_get(v_s_2615_, 0);
            lean_inc(v_it_2616_);
            v_out_2617_ = lean_ctor_get(v_s_2615_, 1);
            lean_inc(v_out_2617_);
            lean_dec_ref_known(v_s_2615_, 2);
            v___f_2618_ = lean_alloc_closure(
                l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_2618_, 0, v_toPure_2610_);
            lean_closure_set(v___f_2618_, 1, v_recur_2611_);
            lean_closure_set(v___f_2618_, 2, v_it_2616_);
            v___x_2619_ = lean_apply_3(v___y_2612_, v_out_2617_, lean_box(0), v_acc_2613_);
            v___x_2620_ = lean_apply_4(
                v_toBind_2614_,
                lean_box(0),
                lean_box(0),
                v___x_2619_,
                v___f_2618_,
            );
            return v___x_2620_;
        }
        1 => {
            let mut v_it_2621_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2614_);
            lean_dec(v___y_2612_);
            lean_dec(v_toPure_2610_);
            v_it_2621_ = lean_ctor_get(v_s_2615_, 0);
            lean_inc(v_it_2621_);
            lean_dec_ref_known(v_s_2615_, 1);
            v___x_2622_ = lean_apply_4(
                v_recur_2611_,
                v_it_2621_,
                v_acc_2613_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_2622_;
        }
        _ => {
            let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_2614_);
            lean_dec(v___y_2612_);
            lean_dec(v_recur_2611_);
            v___x_2623_ = lean_apply_2(v_toPure_2610_, lean_box(0), v_acc_2613_);
            return v___x_2623_;
        }
    }
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(
    mut v_toPure_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v_toBind_2626_: *mut LeanObject,
    mut v_inst_2627_: *mut LeanObject,
    mut v_lift_2628_: *mut LeanObject,
    mut v_it_2629_: *mut LeanObject,
    mut v_acc_2630_: *mut LeanObject,
    mut v_hP_2631_: *mut LeanObject,
    mut v_recur_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    v___f_2633_ = lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2633_, 0, v_toPure_2624_);
    lean_closure_set(v___f_2633_, 1, v_recur_2632_);
    lean_closure_set(v___f_2633_, 2, v___y_2625_);
    lean_closure_set(v___f_2633_, 3, v_acc_2630_);
    lean_closure_set(v___f_2633_, 4, v_toBind_2626_);
    v___x_2634_ = lean_apply_1(v_inst_2627_, v_it_2629_);
    v___x_2635_ = lean_apply_4(
        v_lift_2628_,
        lean_box(0),
        lean_box(0),
        v___f_2633_,
        v___x_2634_,
    );
    return v___x_2635_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(
    mut v_inst_2636_: *mut LeanObject,
    mut v_inst_2637_: *mut LeanObject,
    mut v_lift_2638_: *mut LeanObject,
    mut v_00_u03b3_2639_: *mut LeanObject,
    mut v_Pl_2640_: *mut LeanObject,
    mut v_it_2641_: *mut LeanObject,
    mut v_init_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2644_ = lean_ctor_get(v_inst_2636_, 0);
    lean_inc_ref(v_toApplicative_2644_);
    v_toBind_2645_ = lean_ctor_get(v_inst_2636_, 1);
    lean_inc(v_toBind_2645_);
    lean_dec_ref(v_inst_2636_);
    v_toPure_2646_ = lean_ctor_get(v_toApplicative_2644_, 1);
    lean_inc(v_toPure_2646_);
    lean_dec_ref(v_toApplicative_2644_);
    v___f_2647_ = lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__0 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_2647_, 0, v_toPure_2646_);
    lean_closure_set(v___f_2647_, 1, v___y_2643_);
    lean_closure_set(v___f_2647_, 2, v_toBind_2645_);
    lean_closure_set(v___f_2647_, 3, v_inst_2637_);
    lean_closure_set(v___f_2647_, 4, v_lift_2638_);
    v___x_2648_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2647_, v_it_2641_, v_init_2642_, lean_box(0));
    return v___x_2648_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation___redArg(
    mut v_inst_2649_: *mut LeanObject,
    mut v_inst_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2651_: *mut LeanObject = core::ptr::null_mut();
    v___f_2651_ = lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_2651_, 0, v_inst_2649_);
    lean_closure_set(v___f_2651_, 1, v_inst_2650_);
    return v___f_2651_;
}
pub unsafe fn l_Std_IteratorLoop_defaultImplementation(
    mut v_00_u03b2_2652_: *mut LeanObject,
    mut v_00_u03b1_2653_: *mut LeanObject,
    mut v_m_2654_: *mut LeanObject,
    mut v_n_2655_: *mut LeanObject,
    mut v_inst_2656_: *mut LeanObject,
    mut v_inst_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2658_: *mut LeanObject = core::ptr::null_mut();
    v___f_2658_ = lean_alloc_closure(
        l_Std_IteratorLoop_defaultImplementation___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_2658_, 0, v_inst_2656_);
    lean_closure_set(v___f_2658_, 1, v_inst_2657_);
    return v___f_2658_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(
    mut v_toPure_2659_: *mut LeanObject,
    mut v_____do__lift_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    v___x_2661_ = lean_apply_2(v_toPure_2659_, lean_box(0), v_____do__lift_2660_);
    return v___x_2661_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(
    mut v_f_2662_: *mut LeanObject,
    mut v_toBind_2663_: *mut LeanObject,
    mut v___f_2664_: *mut LeanObject,
    mut v_x1_2665_: *mut LeanObject,
    mut v_x2_2666_: *mut LeanObject,
    mut v_x3_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2668_ = lean_apply_3(v_f_2662_, v_x1_2665_, lean_box(0), v_x3_2667_);
    v___x_2669_ = lean_apply_4(
        v_toBind_2663_,
        lean_box(0),
        lean_box(0),
        v___x_2668_,
        v___f_2664_,
    );
    return v___x_2669_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(
    mut v_toBind_2670_: *mut LeanObject,
    mut v___f_2671_: *mut LeanObject,
    mut v_inst_2672_: *mut LeanObject,
    mut v_lift_2673_: *mut LeanObject,
    mut v_00_u03b3_2674_: *mut LeanObject,
    mut v_it_2675_: *mut LeanObject,
    mut v_init_2676_: *mut LeanObject,
    mut v_f_2677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    v___f_2678_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2678_, 0, v_f_2677_);
    lean_closure_set(v___f_2678_, 1, v_toBind_2670_);
    lean_closure_set(v___f_2678_, 2, v___f_2671_);
    v___x_2679_ = lean_apply_6(
        v_inst_2672_,
        v_lift_2673_,
        lean_box(0),
        lean_box(0),
        v_it_2675_,
        v_init_2676_,
        v___f_2678_,
    );
    return v___x_2679_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___redArg(
    mut v_inst_2680_: *mut LeanObject,
    mut v_inst_2681_: *mut LeanObject,
    mut v_lift_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2683_ = lean_ctor_get(v_inst_2681_, 0);
    lean_inc_ref(v_toApplicative_2683_);
    v_toBind_2684_ = lean_ctor_get(v_inst_2681_, 1);
    lean_inc(v_toBind_2684_);
    lean_dec_ref(v_inst_2681_);
    v_toPure_2685_ = lean_ctor_get(v_toApplicative_2683_, 1);
    lean_inc(v_toPure_2685_);
    lean_dec_ref(v_toApplicative_2683_);
    v___f_2686_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2686_, 0, v_toPure_2685_);
    v___f_2687_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2687_, 0, v_toBind_2684_);
    lean_closure_set(v___f_2687_, 1, v___f_2686_);
    lean_closure_set(v___f_2687_, 2, v_inst_2680_);
    lean_closure_set(v___f_2687_, 3, v_lift_2682_);
    return v___f_2687_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27(
    mut v_m_2688_: *mut LeanObject,
    mut v_n_2689_: *mut LeanObject,
    mut v_00_u03b1_2690_: *mut LeanObject,
    mut v_00_u03b2_2691_: *mut LeanObject,
    mut v_inst_2692_: *mut LeanObject,
    mut v_inst_2693_: *mut LeanObject,
    mut v_inst_2694_: *mut LeanObject,
    mut v_lift_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2700_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2696_ = lean_ctor_get(v_inst_2694_, 0);
    lean_inc_ref(v_toApplicative_2696_);
    v_toBind_2697_ = lean_ctor_get(v_inst_2694_, 1);
    lean_inc(v_toBind_2697_);
    lean_dec_ref(v_inst_2694_);
    v_toPure_2698_ = lean_ctor_get(v_toApplicative_2696_, 1);
    lean_inc(v_toPure_2698_);
    lean_dec_ref(v_toApplicative_2696_);
    v___f_2699_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2699_, 0, v_toPure_2698_);
    v___f_2700_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2700_, 0, v_toBind_2697_);
    lean_closure_set(v___f_2700_, 1, v___f_2699_);
    lean_closure_set(v___f_2700_, 2, v_inst_2693_);
    lean_closure_set(v___f_2700_, 3, v_lift_2695_);
    return v___f_2700_;
}
pub unsafe fn l_Std_IteratorLoop_finiteForIn_x27___boxed(
    mut v_m_2701_: *mut LeanObject,
    mut v_n_2702_: *mut LeanObject,
    mut v_00_u03b1_2703_: *mut LeanObject,
    mut v_00_u03b2_2704_: *mut LeanObject,
    mut v_inst_2705_: *mut LeanObject,
    mut v_inst_2706_: *mut LeanObject,
    mut v_inst_2707_: *mut LeanObject,
    mut v_lift_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2709_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2705_);
    return v_res_2709_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg___lam__0(
    mut v_inst_2710_: *mut LeanObject,
    mut v_toBind_2711_: *mut LeanObject,
    mut v_x_2712_: *mut LeanObject,
    mut v_x_2713_: *mut LeanObject,
    mut v_f_2714_: *mut LeanObject,
    mut v_x_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = lean_apply_2(v_inst_2710_, lean_box(0), v_x_2715_);
    v___x_2717_ = lean_apply_4(
        v_toBind_2711_,
        lean_box(0),
        lean_box(0),
        v___x_2716_,
        v_f_2714_,
    );
    return v___x_2717_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg___lam__3(
    mut v_toBind_2718_: *mut LeanObject,
    mut v___f_2719_: *mut LeanObject,
    mut v_inst_2720_: *mut LeanObject,
    mut v___f_2721_: *mut LeanObject,
    mut v_00_u03b3_2722_: *mut LeanObject,
    mut v_it_2723_: *mut LeanObject,
    mut v_init_2724_: *mut LeanObject,
    mut v_f_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    v___f_2726_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2726_, 0, v_f_2725_);
    lean_closure_set(v___f_2726_, 1, v_toBind_2718_);
    lean_closure_set(v___f_2726_, 2, v___f_2719_);
    v___x_2727_ = lean_apply_6(
        v_inst_2720_,
        v___f_2721_,
        lean_box(0),
        lean_box(0),
        v_it_2723_,
        v_init_2724_,
        v___f_2726_,
    );
    return v___x_2727_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___redArg(
    mut v_inst_2728_: *mut LeanObject,
    mut v_inst_2729_: *mut LeanObject,
    mut v_inst_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2736_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2731_ = lean_ctor_get(v_inst_2729_, 0);
    lean_inc_ref(v_toApplicative_2731_);
    v_toBind_2732_ = lean_ctor_get(v_inst_2729_, 1);
    lean_inc_n(v_toBind_2732_, 2);
    lean_dec_ref(v_inst_2729_);
    v_toPure_2733_ = lean_ctor_get(v_toApplicative_2731_, 1);
    lean_inc(v_toPure_2733_);
    lean_dec_ref(v_toApplicative_2731_);
    v___f_2734_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2734_, 0, v_inst_2730_);
    lean_closure_set(v___f_2734_, 1, v_toBind_2732_);
    v___f_2735_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2735_, 0, v_toPure_2733_);
    v___f_2736_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2736_, 0, v_toBind_2732_);
    lean_closure_set(v___f_2736_, 1, v___f_2735_);
    lean_closure_set(v___f_2736_, 2, v_inst_2728_);
    lean_closure_set(v___f_2736_, 3, v___f_2734_);
    return v___f_2736_;
}
pub unsafe fn l_Std_IterM_instForIn_x27(
    mut v_m_2737_: *mut LeanObject,
    mut v_n_2738_: *mut LeanObject,
    mut v_00_u03b1_2739_: *mut LeanObject,
    mut v_00_u03b2_2740_: *mut LeanObject,
    mut v_inst_2741_: *mut LeanObject,
    mut v_inst_2742_: *mut LeanObject,
    mut v_inst_2743_: *mut LeanObject,
    mut v_inst_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2745_ = lean_ctor_get(v_inst_2743_, 0);
    lean_inc_ref(v_toApplicative_2745_);
    v_toBind_2746_ = lean_ctor_get(v_inst_2743_, 1);
    lean_inc_n(v_toBind_2746_, 2);
    lean_dec_ref(v_inst_2743_);
    v_toPure_2747_ = lean_ctor_get(v_toApplicative_2745_, 1);
    lean_inc(v_toPure_2747_);
    lean_dec_ref(v_toApplicative_2745_);
    v___f_2748_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2748_, 0, v_inst_2744_);
    lean_closure_set(v___f_2748_, 1, v_toBind_2746_);
    v___f_2749_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2749_, 0, v_toPure_2747_);
    v___f_2750_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2750_, 0, v_toBind_2746_);
    lean_closure_set(v___f_2750_, 1, v___f_2749_);
    lean_closure_set(v___f_2750_, 2, v_inst_2742_);
    lean_closure_set(v___f_2750_, 3, v___f_2748_);
    return v___f_2750_;
}
pub unsafe fn l_Std_IterM_instForIn_x27___boxed(
    mut v_m_2751_: *mut LeanObject,
    mut v_n_2752_: *mut LeanObject,
    mut v_00_u03b1_2753_: *mut LeanObject,
    mut v_00_u03b2_2754_: *mut LeanObject,
    mut v_inst_2755_: *mut LeanObject,
    mut v_inst_2756_: *mut LeanObject,
    mut v_inst_2757_: *mut LeanObject,
    mut v_inst_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2755_);
    return v_res_2759_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop___redArg(
    mut v_inst_2760_: *mut LeanObject,
    mut v_inst_2761_: *mut LeanObject,
    mut v_inst_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2763_ = lean_ctor_get(v_inst_2762_, 0);
    lean_inc_ref(v_toApplicative_2763_);
    v_toBind_2764_ = lean_ctor_get(v_inst_2762_, 1);
    lean_inc_n(v_toBind_2764_, 2);
    lean_dec_ref(v_inst_2762_);
    v_toPure_2765_ = lean_ctor_get(v_toApplicative_2763_, 1);
    lean_inc(v_toPure_2765_);
    lean_dec_ref(v_toApplicative_2763_);
    v___f_2766_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2766_, 0, v_inst_2761_);
    lean_closure_set(v___f_2766_, 1, v_toBind_2764_);
    v___f_2767_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2767_, 0, v_toPure_2765_);
    v___f_2768_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2768_, 0, v_toBind_2764_);
    lean_closure_set(v___f_2768_, 1, v___f_2767_);
    lean_closure_set(v___f_2768_, 2, v_inst_2760_);
    lean_closure_set(v___f_2768_, 3, v___f_2766_);
    v___f_2769_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2769_, 0, v___f_2768_);
    return v___f_2769_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop(
    mut v_m_2770_: *mut LeanObject,
    mut v_n_2771_: *mut LeanObject,
    mut v_00_u03b1_2772_: *mut LeanObject,
    mut v_00_u03b2_2773_: *mut LeanObject,
    mut v_inst_2774_: *mut LeanObject,
    mut v_inst_2775_: *mut LeanObject,
    mut v_inst_2776_: *mut LeanObject,
    mut v_inst_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ =
        l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_2775_, v_inst_2776_, v_inst_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_IterM_instForInOfIteratorLoop___boxed(
    mut v_m_2779_: *mut LeanObject,
    mut v_n_2780_: *mut LeanObject,
    mut v_00_u03b1_2781_: *mut LeanObject,
    mut v_00_u03b2_2782_: *mut LeanObject,
    mut v_inst_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
    mut v_inst_2785_: *mut LeanObject,
    mut v_inst_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2787_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2783_);
    return v_res_2787_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(
    mut v_toBind_2788_: *mut LeanObject,
    mut v___f_2789_: *mut LeanObject,
    mut v_inst_2790_: *mut LeanObject,
    mut v___f_2791_: *mut LeanObject,
    mut v_00_u03b2_2792_: *mut LeanObject,
    mut v_it_2793_: *mut LeanObject,
    mut v_init_2794_: *mut LeanObject,
    mut v_f_2795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    v___f_2796_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2796_, 0, v_f_2795_);
    lean_closure_set(v___f_2796_, 1, v_toBind_2788_);
    lean_closure_set(v___f_2796_, 2, v___f_2789_);
    v___x_2797_ = lean_apply_6(
        v_inst_2790_,
        v___f_2791_,
        lean_box(0),
        lean_box(0),
        v_it_2793_,
        v_init_2794_,
        v___f_2796_,
    );
    return v___x_2797_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___redArg(
    mut v_inst_2798_: *mut LeanObject,
    mut v_inst_2799_: *mut LeanObject,
    mut v_inst_2800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2806_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2801_ = lean_ctor_get(v_inst_2800_, 0);
    lean_inc_ref(v_toApplicative_2801_);
    v_toBind_2802_ = lean_ctor_get(v_inst_2800_, 1);
    lean_inc_n(v_toBind_2802_, 2);
    lean_dec_ref(v_inst_2800_);
    v_toPure_2803_ = lean_ctor_get(v_toApplicative_2801_, 1);
    lean_inc(v_toPure_2803_);
    lean_dec_ref(v_toApplicative_2801_);
    v___f_2804_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2804_, 0, v_inst_2799_);
    lean_closure_set(v___f_2804_, 1, v_toBind_2802_);
    v___f_2805_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2805_, 0, v_toPure_2803_);
    v___f_2806_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2806_, 0, v_toBind_2802_);
    lean_closure_set(v___f_2806_, 1, v___f_2805_);
    lean_closure_set(v___f_2806_, 2, v_inst_2798_);
    lean_closure_set(v___f_2806_, 3, v___f_2804_);
    return v___f_2806_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27(
    mut v_m_2807_: *mut LeanObject,
    mut v_n_2808_: *mut LeanObject,
    mut v_00_u03b1_2809_: *mut LeanObject,
    mut v_00_u03b2_2810_: *mut LeanObject,
    mut v_inst_2811_: *mut LeanObject,
    mut v_inst_2812_: *mut LeanObject,
    mut v_inst_2813_: *mut LeanObject,
    mut v_inst_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2820_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2815_ = lean_ctor_get(v_inst_2814_, 0);
    lean_inc_ref(v_toApplicative_2815_);
    v_toBind_2816_ = lean_ctor_get(v_inst_2814_, 1);
    lean_inc_n(v_toBind_2816_, 2);
    lean_dec_ref(v_inst_2814_);
    v_toPure_2817_ = lean_ctor_get(v_toApplicative_2815_, 1);
    lean_inc(v_toPure_2817_);
    lean_dec_ref(v_toApplicative_2815_);
    v___f_2818_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2818_, 0, v_inst_2813_);
    lean_closure_set(v___f_2818_, 1, v_toBind_2816_);
    v___f_2819_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2819_, 0, v_toPure_2817_);
    v___f_2820_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2820_, 0, v_toBind_2816_);
    lean_closure_set(v___f_2820_, 1, v___f_2819_);
    lean_closure_set(v___f_2820_, 2, v_inst_2812_);
    lean_closure_set(v___f_2820_, 3, v___f_2818_);
    return v___f_2820_;
}
pub unsafe fn l_Std_IterM_Partial_instForIn_x27___boxed(
    mut v_m_2821_: *mut LeanObject,
    mut v_n_2822_: *mut LeanObject,
    mut v_00_u03b1_2823_: *mut LeanObject,
    mut v_00_u03b2_2824_: *mut LeanObject,
    mut v_inst_2825_: *mut LeanObject,
    mut v_inst_2826_: *mut LeanObject,
    mut v_inst_2827_: *mut LeanObject,
    mut v_inst_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2829_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2825_);
    return v_res_2829_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27___redArg(
    mut v_inst_2830_: *mut LeanObject,
    mut v_inst_2831_: *mut LeanObject,
    mut v_inst_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2838_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2833_ = lean_ctor_get(v_inst_2832_, 0);
    lean_inc_ref(v_toApplicative_2833_);
    v_toBind_2834_ = lean_ctor_get(v_inst_2832_, 1);
    lean_inc_n(v_toBind_2834_, 2);
    lean_dec_ref(v_inst_2832_);
    v_toPure_2835_ = lean_ctor_get(v_toApplicative_2833_, 1);
    lean_inc(v_toPure_2835_);
    lean_dec_ref(v_toApplicative_2833_);
    v___f_2836_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2836_, 0, v_inst_2831_);
    lean_closure_set(v___f_2836_, 1, v_toBind_2834_);
    v___f_2837_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2837_, 0, v_toPure_2835_);
    v___f_2838_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2838_, 0, v_toBind_2834_);
    lean_closure_set(v___f_2838_, 1, v___f_2837_);
    lean_closure_set(v___f_2838_, 2, v_inst_2830_);
    lean_closure_set(v___f_2838_, 3, v___f_2836_);
    return v___f_2838_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27(
    mut v_m_2839_: *mut LeanObject,
    mut v_n_2840_: *mut LeanObject,
    mut v_00_u03b1_2841_: *mut LeanObject,
    mut v_00_u03b2_2842_: *mut LeanObject,
    mut v_inst_2843_: *mut LeanObject,
    mut v_inst_2844_: *mut LeanObject,
    mut v_inst_2845_: *mut LeanObject,
    mut v_inst_2846_: *mut LeanObject,
    mut v_inst_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2853_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2848_ = lean_ctor_get(v_inst_2846_, 0);
    lean_inc_ref(v_toApplicative_2848_);
    v_toBind_2849_ = lean_ctor_get(v_inst_2846_, 1);
    lean_inc_n(v_toBind_2849_, 2);
    lean_dec_ref(v_inst_2846_);
    v_toPure_2850_ = lean_ctor_get(v_toApplicative_2848_, 1);
    lean_inc(v_toPure_2850_);
    lean_dec_ref(v_toApplicative_2848_);
    v___f_2851_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2851_, 0, v_inst_2845_);
    lean_closure_set(v___f_2851_, 1, v_toBind_2849_);
    v___f_2852_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2852_, 0, v_toPure_2850_);
    v___f_2853_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2853_, 0, v_toBind_2849_);
    lean_closure_set(v___f_2853_, 1, v___f_2852_);
    lean_closure_set(v___f_2853_, 2, v_inst_2844_);
    lean_closure_set(v___f_2853_, 3, v___f_2851_);
    return v___f_2853_;
}
pub unsafe fn l_Std_IterM_Total_instForIn_x27___boxed(
    mut v_m_2854_: *mut LeanObject,
    mut v_n_2855_: *mut LeanObject,
    mut v_00_u03b1_2856_: *mut LeanObject,
    mut v_00_u03b2_2857_: *mut LeanObject,
    mut v_inst_2858_: *mut LeanObject,
    mut v_inst_2859_: *mut LeanObject,
    mut v_inst_2860_: *mut LeanObject,
    mut v_inst_2861_: *mut LeanObject,
    mut v_inst_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2863_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2858_);
    return v_res_2863_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(
    mut v_inst_2864_: *mut LeanObject,
    mut v_inst_2865_: *mut LeanObject,
    mut v_inst_2866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2867_ = lean_ctor_get(v_inst_2866_, 0);
    lean_inc_ref(v_toApplicative_2867_);
    v_toBind_2868_ = lean_ctor_get(v_inst_2866_, 1);
    lean_inc_n(v_toBind_2868_, 2);
    lean_dec_ref(v_inst_2866_);
    v_toPure_2869_ = lean_ctor_get(v_toApplicative_2867_, 1);
    lean_inc(v_toPure_2869_);
    lean_dec_ref(v_toApplicative_2867_);
    v___f_2870_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2870_, 0, v_inst_2865_);
    lean_closure_set(v___f_2870_, 1, v_toBind_2868_);
    v___f_2871_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2871_, 0, v_toPure_2869_);
    v___f_2872_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2872_, 0, v_toBind_2868_);
    lean_closure_set(v___f_2872_, 1, v___f_2871_);
    lean_closure_set(v___f_2872_, 2, v_inst_2864_);
    lean_closure_set(v___f_2872_, 3, v___f_2870_);
    v___f_2873_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2873_, 0, v___f_2872_);
    return v___f_2873_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop(
    mut v_m_2874_: *mut LeanObject,
    mut v_n_2875_: *mut LeanObject,
    mut v_00_u03b1_2876_: *mut LeanObject,
    mut v_00_u03b2_2877_: *mut LeanObject,
    mut v_inst_2878_: *mut LeanObject,
    mut v_inst_2879_: *mut LeanObject,
    mut v_inst_2880_: *mut LeanObject,
    mut v_inst_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v___x_2882_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(
        v_inst_2879_,
        v_inst_2880_,
        v_inst_2881_,
    );
    return v___x_2882_;
}
pub unsafe fn l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(
    mut v_m_2883_: *mut LeanObject,
    mut v_n_2884_: *mut LeanObject,
    mut v_00_u03b1_2885_: *mut LeanObject,
    mut v_00_u03b2_2886_: *mut LeanObject,
    mut v_inst_2887_: *mut LeanObject,
    mut v_inst_2888_: *mut LeanObject,
    mut v_inst_2889_: *mut LeanObject,
    mut v_inst_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2887_);
    return v_res_2891_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(
    mut v_inst_2892_: *mut LeanObject,
    mut v_inst_2893_: *mut LeanObject,
    mut v_inst_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2895_ = lean_ctor_get(v_inst_2894_, 0);
    lean_inc_ref(v_toApplicative_2895_);
    v_toBind_2896_ = lean_ctor_get(v_inst_2894_, 1);
    lean_inc_n(v_toBind_2896_, 2);
    lean_dec_ref(v_inst_2894_);
    v_toPure_2897_ = lean_ctor_get(v_toApplicative_2895_, 1);
    lean_inc(v_toPure_2897_);
    lean_dec_ref(v_toApplicative_2895_);
    v___f_2898_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2898_, 0, v_inst_2893_);
    lean_closure_set(v___f_2898_, 1, v_toBind_2896_);
    v___f_2899_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2899_, 0, v_toPure_2897_);
    v___f_2900_ = lean_alloc_closure(
        l_Std_IterM_Partial_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2900_, 0, v_toBind_2896_);
    lean_closure_set(v___f_2900_, 1, v___f_2899_);
    lean_closure_set(v___f_2900_, 2, v_inst_2892_);
    lean_closure_set(v___f_2900_, 3, v___f_2898_);
    v___f_2901_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2901_, 0, v___f_2900_);
    return v___f_2901_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(
    mut v_m_2902_: *mut LeanObject,
    mut v_n_2903_: *mut LeanObject,
    mut v_00_u03b1_2904_: *mut LeanObject,
    mut v_00_u03b2_2905_: *mut LeanObject,
    mut v_inst_2906_: *mut LeanObject,
    mut v_inst_2907_: *mut LeanObject,
    mut v_inst_2908_: *mut LeanObject,
    mut v_inst_2909_: *mut LeanObject,
    mut v_inst_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    v___x_2911_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(
        v_inst_2907_,
        v_inst_2908_,
        v_inst_2909_,
    );
    return v___x_2911_;
}
pub unsafe fn l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(
    mut v_m_2912_: *mut LeanObject,
    mut v_n_2913_: *mut LeanObject,
    mut v_00_u03b1_2914_: *mut LeanObject,
    mut v_00_u03b2_2915_: *mut LeanObject,
    mut v_inst_2916_: *mut LeanObject,
    mut v_inst_2917_: *mut LeanObject,
    mut v_inst_2918_: *mut LeanObject,
    mut v_inst_2919_: *mut LeanObject,
    mut v_inst_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2916_);
    return v_res_2921_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(
    mut v_toPure_2922_: *mut LeanObject,
    mut v_____do__lift_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = lean_apply_2(v_toPure_2922_, lean_box(0), v_____do__lift_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(
    mut v___x_2925_: *mut LeanObject,
    mut v_toPure_2926_: *mut LeanObject,
    mut v_____r_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    v___x_2928_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2928_, 0, v___x_2925_);
    v___x_2929_ = lean_apply_2(v_toPure_2926_, lean_box(0), v___x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(
    mut v_f_2930_: *mut LeanObject,
    mut v_toBind_2931_: *mut LeanObject,
    mut v___f_2932_: *mut LeanObject,
    mut v___f_2933_: *mut LeanObject,
    mut v_x1_2934_: *mut LeanObject,
    mut v_x2_2935_: *mut LeanObject,
    mut v_x3_2936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    v___x_2937_ = lean_apply_1(v_f_2930_, v_x1_2934_);
    lean_inc(v_toBind_2931_);
    v___x_2938_ = lean_apply_4(
        v_toBind_2931_,
        lean_box(0),
        lean_box(0),
        v___x_2937_,
        v___f_2932_,
    );
    v___x_2939_ = lean_apply_4(
        v_toBind_2931_,
        lean_box(0),
        lean_box(0),
        v___x_2938_,
        v___f_2933_,
    );
    return v___x_2939_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(
    mut v_toPure_2940_: *mut LeanObject,
    mut v_toBind_2941_: *mut LeanObject,
    mut v___f_2942_: *mut LeanObject,
    mut v_inst_2943_: *mut LeanObject,
    mut v___f_2944_: *mut LeanObject,
    mut v_it_2945_: *mut LeanObject,
    mut v_f_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    v___x_2947_ = lean_box(0);
    v___f_2948_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2948_, 0, v___x_2947_);
    lean_closure_set(v___f_2948_, 1, v_toPure_2940_);
    v___f_2949_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2949_, 0, v_f_2946_);
    lean_closure_set(v___f_2949_, 1, v_toBind_2941_);
    lean_closure_set(v___f_2949_, 2, v___f_2948_);
    lean_closure_set(v___f_2949_, 3, v___f_2942_);
    v___x_2950_ = lean_apply_6(
        v_inst_2943_,
        v___f_2944_,
        lean_box(0),
        lean_box(0),
        v_it_2945_,
        v___x_2947_,
        v___f_2949_,
    );
    return v___x_2950_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___redArg(
    mut v_inst_2951_: *mut LeanObject,
    mut v_inst_2952_: *mut LeanObject,
    mut v_inst_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2959_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2954_ = lean_ctor_get(v_inst_2952_, 0);
    lean_inc_ref(v_toApplicative_2954_);
    v_toBind_2955_ = lean_ctor_get(v_inst_2952_, 1);
    lean_inc_n(v_toBind_2955_, 2);
    lean_dec_ref(v_inst_2952_);
    v_toPure_2956_ = lean_ctor_get(v_toApplicative_2954_, 1);
    lean_inc_n(v_toPure_2956_, 2);
    lean_dec_ref(v_toApplicative_2954_);
    v___f_2957_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2957_, 0, v_inst_2953_);
    lean_closure_set(v___f_2957_, 1, v_toBind_2955_);
    v___f_2958_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2958_, 0, v_toPure_2956_);
    v___f_2959_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2959_, 0, v_toPure_2956_);
    lean_closure_set(v___f_2959_, 1, v_toBind_2955_);
    lean_closure_set(v___f_2959_, 2, v___f_2958_);
    lean_closure_set(v___f_2959_, 3, v_inst_2951_);
    lean_closure_set(v___f_2959_, 4, v___f_2957_);
    return v___f_2959_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop(
    mut v_m_2960_: *mut LeanObject,
    mut v_n_2961_: *mut LeanObject,
    mut v_00_u03b1_2962_: *mut LeanObject,
    mut v_00_u03b2_2963_: *mut LeanObject,
    mut v_inst_2964_: *mut LeanObject,
    mut v_inst_2965_: *mut LeanObject,
    mut v_inst_2966_: *mut LeanObject,
    mut v_inst_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ =
        l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_2965_, v_inst_2966_, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Std_IterM_instForMOfIteratorLoop___boxed(
    mut v_m_2969_: *mut LeanObject,
    mut v_n_2970_: *mut LeanObject,
    mut v_00_u03b1_2971_: *mut LeanObject,
    mut v_00_u03b2_2972_: *mut LeanObject,
    mut v_inst_2973_: *mut LeanObject,
    mut v_inst_2974_: *mut LeanObject,
    mut v_inst_2975_: *mut LeanObject,
    mut v_inst_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2977_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2973_);
    return v_res_2977_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(
    mut v_inst_2978_: *mut LeanObject,
    mut v_inst_2979_: *mut LeanObject,
    mut v_inst_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2986_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2981_ = lean_ctor_get(v_inst_2978_, 0);
    lean_inc_ref(v_toApplicative_2981_);
    v_toBind_2982_ = lean_ctor_get(v_inst_2978_, 1);
    lean_inc_n(v_toBind_2982_, 2);
    lean_dec_ref(v_inst_2978_);
    v_toPure_2983_ = lean_ctor_get(v_toApplicative_2981_, 1);
    lean_inc_n(v_toPure_2983_, 2);
    lean_dec_ref(v_toApplicative_2981_);
    v___f_2984_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_2984_, 0, v_inst_2980_);
    lean_closure_set(v___f_2984_, 1, v_toBind_2982_);
    v___f_2985_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2985_, 0, v_toPure_2983_);
    v___f_2986_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2986_, 0, v_toPure_2983_);
    lean_closure_set(v___f_2986_, 1, v_toBind_2982_);
    lean_closure_set(v___f_2986_, 2, v___f_2985_);
    lean_closure_set(v___f_2986_, 3, v_inst_2979_);
    lean_closure_set(v___f_2986_, 4, v___f_2984_);
    return v___f_2986_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop(
    mut v_m_2987_: *mut LeanObject,
    mut v_n_2988_: *mut LeanObject,
    mut v_00_u03b1_2989_: *mut LeanObject,
    mut v_00_u03b2_2990_: *mut LeanObject,
    mut v_inst_2991_: *mut LeanObject,
    mut v_inst_2992_: *mut LeanObject,
    mut v_inst_2993_: *mut LeanObject,
    mut v_inst_2994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    v___x_2995_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(
        v_inst_2991_,
        v_inst_2993_,
        v_inst_2994_,
    );
    return v___x_2995_;
}
pub unsafe fn l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(
    mut v_m_2996_: *mut LeanObject,
    mut v_n_2997_: *mut LeanObject,
    mut v_00_u03b1_2998_: *mut LeanObject,
    mut v_00_u03b2_2999_: *mut LeanObject,
    mut v_inst_3000_: *mut LeanObject,
    mut v_inst_3001_: *mut LeanObject,
    mut v_inst_3002_: *mut LeanObject,
    mut v_inst_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3004_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3001_);
    return v_res_3004_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(
    mut v_inst_3005_: *mut LeanObject,
    mut v_inst_3006_: *mut LeanObject,
    mut v_inst_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3013_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3008_ = lean_ctor_get(v_inst_3006_, 0);
    lean_inc_ref(v_toApplicative_3008_);
    v_toBind_3009_ = lean_ctor_get(v_inst_3006_, 1);
    lean_inc_n(v_toBind_3009_, 2);
    lean_dec_ref(v_inst_3006_);
    v_toPure_3010_ = lean_ctor_get(v_toApplicative_3008_, 1);
    lean_inc_n(v_toPure_3010_, 2);
    lean_dec_ref(v_toApplicative_3008_);
    v___f_3011_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3011_, 0, v_inst_3007_);
    lean_closure_set(v___f_3011_, 1, v_toBind_3009_);
    v___f_3012_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3012_, 0, v_toPure_3010_);
    v___f_3013_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_3013_, 0, v_toPure_3010_);
    lean_closure_set(v___f_3013_, 1, v_toBind_3009_);
    lean_closure_set(v___f_3013_, 2, v___f_3012_);
    lean_closure_set(v___f_3013_, 3, v_inst_3005_);
    lean_closure_set(v___f_3013_, 4, v___f_3011_);
    return v___f_3013_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(
    mut v_m_3014_: *mut LeanObject,
    mut v_n_3015_: *mut LeanObject,
    mut v_00_u03b1_3016_: *mut LeanObject,
    mut v_00_u03b2_3017_: *mut LeanObject,
    mut v_inst_3018_: *mut LeanObject,
    mut v_inst_3019_: *mut LeanObject,
    mut v_inst_3020_: *mut LeanObject,
    mut v_inst_3021_: *mut LeanObject,
    mut v_inst_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    v___x_3023_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(
        v_inst_3019_,
        v_inst_3020_,
        v_inst_3021_,
    );
    return v___x_3023_;
}
pub unsafe fn l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(
    mut v_m_3024_: *mut LeanObject,
    mut v_n_3025_: *mut LeanObject,
    mut v_00_u03b1_3026_: *mut LeanObject,
    mut v_00_u03b2_3027_: *mut LeanObject,
    mut v_inst_3028_: *mut LeanObject,
    mut v_inst_3029_: *mut LeanObject,
    mut v_inst_3030_: *mut LeanObject,
    mut v_inst_3031_: *mut LeanObject,
    mut v_inst_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3033_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3028_);
    return v_res_3033_;
}
pub unsafe fn l_Std_IterM_foldM___redArg___lam__0(
    mut v_a_3034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    v___x_3035_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3035_, 0, v_a_3034_);
    return v___x_3035_;
}
pub unsafe fn l_Std_IterM_foldM___redArg___lam__3(
    mut v_toFunctor_3036_: *mut LeanObject,
    mut v_f_3037_: *mut LeanObject,
    mut v___f_3038_: *mut LeanObject,
    mut v_toBind_3039_: *mut LeanObject,
    mut v___f_3040_: *mut LeanObject,
    mut v_x1_3041_: *mut LeanObject,
    mut v_x2_3042_: *mut LeanObject,
    mut v_x3_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    v_map_3044_ = lean_ctor_get(v_toFunctor_3036_, 0);
    lean_inc(v_map_3044_);
    lean_dec_ref(v_toFunctor_3036_);
    v___x_3045_ = lean_apply_2(v_f_3037_, v_x3_3043_, v_x1_3041_);
    v___x_3046_ = lean_apply_4(
        v_map_3044_,
        lean_box(0),
        lean_box(0),
        v___f_3038_,
        v___x_3045_,
    );
    v___x_3047_ = lean_apply_4(
        v_toBind_3039_,
        lean_box(0),
        lean_box(0),
        v___x_3046_,
        v___f_3040_,
    );
    return v___x_3047_;
}
pub unsafe fn l_Std_IterM_foldM___redArg(
    mut v_inst_3049_: *mut LeanObject,
    mut v_inst_3050_: *mut LeanObject,
    mut v_inst_3051_: *mut LeanObject,
    mut v_f_3052_: *mut LeanObject,
    mut v_init_3053_: *mut LeanObject,
    mut v_it_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3055_ = lean_ctor_get(v_inst_3049_, 0);
    lean_inc_ref(v_toApplicative_3055_);
    v_toBind_3056_ = lean_ctor_get(v_inst_3049_, 1);
    lean_inc_n(v_toBind_3056_, 2);
    lean_dec_ref(v_inst_3049_);
    v_toFunctor_3057_ = lean_ctor_get(v_toApplicative_3055_, 0);
    lean_inc_ref(v_toFunctor_3057_);
    v_toPure_3058_ = lean_ctor_get(v_toApplicative_3055_, 1);
    lean_inc(v_toPure_3058_);
    lean_dec_ref(v_toApplicative_3055_);
    v___f_3059_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3060_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3060_, 0, v_inst_3051_);
    lean_closure_set(v___f_3060_, 1, v_toBind_3056_);
    v___f_3061_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3061_, 0, v_toPure_3058_);
    v___f_3062_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3062_, 0, v_toFunctor_3057_);
    lean_closure_set(v___f_3062_, 1, v_f_3052_);
    lean_closure_set(v___f_3062_, 2, v___f_3059_);
    lean_closure_set(v___f_3062_, 3, v_toBind_3056_);
    lean_closure_set(v___f_3062_, 4, v___f_3061_);
    v___x_3063_ = lean_apply_6(
        v_inst_3050_,
        v___f_3060_,
        lean_box(0),
        lean_box(0),
        v_it_3054_,
        v_init_3053_,
        v___f_3062_,
    );
    return v___x_3063_;
}
pub unsafe fn l_Std_IterM_foldM(
    mut v_m_3064_: *mut LeanObject,
    mut v_n_3065_: *mut LeanObject,
    mut v_inst_3066_: *mut LeanObject,
    mut v_00_u03b1_3067_: *mut LeanObject,
    mut v_00_u03b2_3068_: *mut LeanObject,
    mut v_00_u03b3_3069_: *mut LeanObject,
    mut v_inst_3070_: *mut LeanObject,
    mut v_inst_3071_: *mut LeanObject,
    mut v_inst_3072_: *mut LeanObject,
    mut v_f_3073_: *mut LeanObject,
    mut v_init_3074_: *mut LeanObject,
    mut v_it_3075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3076_ = lean_ctor_get(v_inst_3066_, 0);
    lean_inc_ref(v_toApplicative_3076_);
    v_toBind_3077_ = lean_ctor_get(v_inst_3066_, 1);
    lean_inc_n(v_toBind_3077_, 2);
    lean_dec_ref(v_inst_3066_);
    v_toFunctor_3078_ = lean_ctor_get(v_toApplicative_3076_, 0);
    lean_inc_ref(v_toFunctor_3078_);
    v_toPure_3079_ = lean_ctor_get(v_toApplicative_3076_, 1);
    lean_inc(v_toPure_3079_);
    lean_dec_ref(v_toApplicative_3076_);
    v___f_3080_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3081_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3081_, 0, v_inst_3072_);
    lean_closure_set(v___f_3081_, 1, v_toBind_3077_);
    v___f_3082_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3082_, 0, v_toPure_3079_);
    v___f_3083_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3083_, 0, v_toFunctor_3078_);
    lean_closure_set(v___f_3083_, 1, v_f_3073_);
    lean_closure_set(v___f_3083_, 2, v___f_3080_);
    lean_closure_set(v___f_3083_, 3, v_toBind_3077_);
    lean_closure_set(v___f_3083_, 4, v___f_3082_);
    v___x_3084_ = lean_apply_6(
        v_inst_3071_,
        v___f_3081_,
        lean_box(0),
        lean_box(0),
        v_it_3075_,
        v_init_3074_,
        v___f_3083_,
    );
    return v___x_3084_;
}
pub unsafe fn l_Std_IterM_foldM___boxed(
    mut v_m_3085_: *mut LeanObject,
    mut v_n_3086_: *mut LeanObject,
    mut v_inst_3087_: *mut LeanObject,
    mut v_00_u03b1_3088_: *mut LeanObject,
    mut v_00_u03b2_3089_: *mut LeanObject,
    mut v_00_u03b3_3090_: *mut LeanObject,
    mut v_inst_3091_: *mut LeanObject,
    mut v_inst_3092_: *mut LeanObject,
    mut v_inst_3093_: *mut LeanObject,
    mut v_f_3094_: *mut LeanObject,
    mut v_init_3095_: *mut LeanObject,
    mut v_it_3096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3097_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3091_);
    return v_res_3097_;
}
pub unsafe fn l_Std_IterM_Partial_foldM___redArg(
    mut v_inst_3098_: *mut LeanObject,
    mut v_inst_3099_: *mut LeanObject,
    mut v_inst_3100_: *mut LeanObject,
    mut v_f_3101_: *mut LeanObject,
    mut v_init_3102_: *mut LeanObject,
    mut v_it_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3104_ = lean_ctor_get(v_inst_3098_, 0);
    lean_inc_ref(v_toApplicative_3104_);
    v_toBind_3105_ = lean_ctor_get(v_inst_3098_, 1);
    lean_inc_n(v_toBind_3105_, 2);
    lean_dec_ref(v_inst_3098_);
    v_toFunctor_3106_ = lean_ctor_get(v_toApplicative_3104_, 0);
    lean_inc_ref(v_toFunctor_3106_);
    v_toPure_3107_ = lean_ctor_get(v_toApplicative_3104_, 1);
    lean_inc(v_toPure_3107_);
    lean_dec_ref(v_toApplicative_3104_);
    v___f_3108_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3109_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3109_, 0, v_inst_3100_);
    lean_closure_set(v___f_3109_, 1, v_toBind_3105_);
    v___f_3110_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3110_, 0, v_toPure_3107_);
    v___f_3111_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3111_, 0, v_toFunctor_3106_);
    lean_closure_set(v___f_3111_, 1, v_f_3101_);
    lean_closure_set(v___f_3111_, 2, v___f_3108_);
    lean_closure_set(v___f_3111_, 3, v_toBind_3105_);
    lean_closure_set(v___f_3111_, 4, v___f_3110_);
    v___x_3112_ = lean_apply_6(
        v_inst_3099_,
        v___f_3109_,
        lean_box(0),
        lean_box(0),
        v_it_3103_,
        v_init_3102_,
        v___f_3111_,
    );
    return v___x_3112_;
}
pub unsafe fn l_Std_IterM_Partial_foldM(
    mut v_m_3113_: *mut LeanObject,
    mut v_n_3114_: *mut LeanObject,
    mut v_inst_3115_: *mut LeanObject,
    mut v_00_u03b1_3116_: *mut LeanObject,
    mut v_00_u03b2_3117_: *mut LeanObject,
    mut v_00_u03b3_3118_: *mut LeanObject,
    mut v_inst_3119_: *mut LeanObject,
    mut v_inst_3120_: *mut LeanObject,
    mut v_inst_3121_: *mut LeanObject,
    mut v_f_3122_: *mut LeanObject,
    mut v_init_3123_: *mut LeanObject,
    mut v_it_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3125_ = lean_ctor_get(v_inst_3115_, 0);
    lean_inc_ref(v_toApplicative_3125_);
    v_toBind_3126_ = lean_ctor_get(v_inst_3115_, 1);
    lean_inc_n(v_toBind_3126_, 2);
    lean_dec_ref(v_inst_3115_);
    v_toFunctor_3127_ = lean_ctor_get(v_toApplicative_3125_, 0);
    lean_inc_ref(v_toFunctor_3127_);
    v_toPure_3128_ = lean_ctor_get(v_toApplicative_3125_, 1);
    lean_inc(v_toPure_3128_);
    lean_dec_ref(v_toApplicative_3125_);
    v___f_3129_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3130_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3130_, 0, v_inst_3121_);
    lean_closure_set(v___f_3130_, 1, v_toBind_3126_);
    v___f_3131_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3131_, 0, v_toPure_3128_);
    v___f_3132_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3132_, 0, v_toFunctor_3127_);
    lean_closure_set(v___f_3132_, 1, v_f_3122_);
    lean_closure_set(v___f_3132_, 2, v___f_3129_);
    lean_closure_set(v___f_3132_, 3, v_toBind_3126_);
    lean_closure_set(v___f_3132_, 4, v___f_3131_);
    v___x_3133_ = lean_apply_6(
        v_inst_3120_,
        v___f_3130_,
        lean_box(0),
        lean_box(0),
        v_it_3124_,
        v_init_3123_,
        v___f_3132_,
    );
    return v___x_3133_;
}
pub unsafe fn l_Std_IterM_Partial_foldM___boxed(
    mut v_m_3134_: *mut LeanObject,
    mut v_n_3135_: *mut LeanObject,
    mut v_inst_3136_: *mut LeanObject,
    mut v_00_u03b1_3137_: *mut LeanObject,
    mut v_00_u03b2_3138_: *mut LeanObject,
    mut v_00_u03b3_3139_: *mut LeanObject,
    mut v_inst_3140_: *mut LeanObject,
    mut v_inst_3141_: *mut LeanObject,
    mut v_inst_3142_: *mut LeanObject,
    mut v_f_3143_: *mut LeanObject,
    mut v_init_3144_: *mut LeanObject,
    mut v_it_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3146_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3140_);
    return v_res_3146_;
}
pub unsafe fn l_Std_IterM_Total_foldM___redArg(
    mut v_inst_3147_: *mut LeanObject,
    mut v_inst_3148_: *mut LeanObject,
    mut v_inst_3149_: *mut LeanObject,
    mut v_f_3150_: *mut LeanObject,
    mut v_init_3151_: *mut LeanObject,
    mut v_it_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3153_ = lean_ctor_get(v_inst_3147_, 0);
    lean_inc_ref(v_toApplicative_3153_);
    v_toBind_3154_ = lean_ctor_get(v_inst_3147_, 1);
    lean_inc_n(v_toBind_3154_, 2);
    lean_dec_ref(v_inst_3147_);
    v_toFunctor_3155_ = lean_ctor_get(v_toApplicative_3153_, 0);
    lean_inc_ref(v_toFunctor_3155_);
    v_toPure_3156_ = lean_ctor_get(v_toApplicative_3153_, 1);
    lean_inc(v_toPure_3156_);
    lean_dec_ref(v_toApplicative_3153_);
    v___f_3157_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3158_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3158_, 0, v_inst_3149_);
    lean_closure_set(v___f_3158_, 1, v_toBind_3154_);
    v___f_3159_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3159_, 0, v_toPure_3156_);
    v___f_3160_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3160_, 0, v_toFunctor_3155_);
    lean_closure_set(v___f_3160_, 1, v_f_3150_);
    lean_closure_set(v___f_3160_, 2, v___f_3157_);
    lean_closure_set(v___f_3160_, 3, v_toBind_3154_);
    lean_closure_set(v___f_3160_, 4, v___f_3159_);
    v___x_3161_ = lean_apply_6(
        v_inst_3148_,
        v___f_3158_,
        lean_box(0),
        lean_box(0),
        v_it_3152_,
        v_init_3151_,
        v___f_3160_,
    );
    return v___x_3161_;
}
pub unsafe fn l_Std_IterM_Total_foldM(
    mut v_m_3162_: *mut LeanObject,
    mut v_n_3163_: *mut LeanObject,
    mut v_inst_3164_: *mut LeanObject,
    mut v_00_u03b1_3165_: *mut LeanObject,
    mut v_00_u03b2_3166_: *mut LeanObject,
    mut v_00_u03b3_3167_: *mut LeanObject,
    mut v_inst_3168_: *mut LeanObject,
    mut v_inst_3169_: *mut LeanObject,
    mut v_inst_3170_: *mut LeanObject,
    mut v_inst_3171_: *mut LeanObject,
    mut v_f_3172_: *mut LeanObject,
    mut v_init_3173_: *mut LeanObject,
    mut v_it_3174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3175_ = lean_ctor_get(v_inst_3164_, 0);
    lean_inc_ref(v_toApplicative_3175_);
    v_toBind_3176_ = lean_ctor_get(v_inst_3164_, 1);
    lean_inc_n(v_toBind_3176_, 2);
    lean_dec_ref(v_inst_3164_);
    v_toFunctor_3177_ = lean_ctor_get(v_toApplicative_3175_, 0);
    lean_inc_ref(v_toFunctor_3177_);
    v_toPure_3178_ = lean_ctor_get(v_toApplicative_3175_, 1);
    lean_inc(v_toPure_3178_);
    lean_dec_ref(v_toApplicative_3175_);
    v___f_3179_ = l_Std_IterM_foldM___redArg___closed__0;
    v___f_3180_ = lean_alloc_closure(
        l_Std_IterM_instForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_3180_, 0, v_inst_3170_);
    lean_closure_set(v___f_3180_, 1, v_toBind_3176_);
    v___f_3181_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3181_, 0, v_toPure_3178_);
    v___f_3182_ = lean_alloc_closure(
        l_Std_IterM_foldM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_3182_, 0, v_toFunctor_3177_);
    lean_closure_set(v___f_3182_, 1, v_f_3172_);
    lean_closure_set(v___f_3182_, 2, v___f_3179_);
    lean_closure_set(v___f_3182_, 3, v_toBind_3176_);
    lean_closure_set(v___f_3182_, 4, v___f_3181_);
    v___x_3183_ = lean_apply_6(
        v_inst_3169_,
        v___f_3180_,
        lean_box(0),
        lean_box(0),
        v_it_3174_,
        v_init_3173_,
        v___f_3182_,
    );
    return v___x_3183_;
}
pub unsafe fn l_Std_IterM_Total_foldM___boxed(
    mut v_m_3184_: *mut LeanObject,
    mut v_n_3185_: *mut LeanObject,
    mut v_inst_3186_: *mut LeanObject,
    mut v_00_u03b1_3187_: *mut LeanObject,
    mut v_00_u03b2_3188_: *mut LeanObject,
    mut v_00_u03b3_3189_: *mut LeanObject,
    mut v_inst_3190_: *mut LeanObject,
    mut v_inst_3191_: *mut LeanObject,
    mut v_inst_3192_: *mut LeanObject,
    mut v_inst_3193_: *mut LeanObject,
    mut v_f_3194_: *mut LeanObject,
    mut v_init_3195_: *mut LeanObject,
    mut v_it_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3197_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3190_);
    return v_res_3197_;
}
pub unsafe fn l_Std_IterM_fold___redArg___lam__0(
    mut v_toBind_3198_: *mut LeanObject,
    mut v_x_3199_: *mut LeanObject,
    mut v_x_3200_: *mut LeanObject,
    mut v_f_3201_: *mut LeanObject,
    mut v_x_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    v___x_3203_ = lean_apply_4(
        v_toBind_3198_,
        lean_box(0),
        lean_box(0),
        v_x_3202_,
        v_f_3201_,
    );
    return v___x_3203_;
}
pub unsafe fn l_Std_IterM_fold___redArg___lam__2(
    mut v_f_3204_: *mut LeanObject,
    mut v_toPure_3205_: *mut LeanObject,
    mut v_toBind_3206_: *mut LeanObject,
    mut v___f_3207_: *mut LeanObject,
    mut v_x1_3208_: *mut LeanObject,
    mut v_x2_3209_: *mut LeanObject,
    mut v_x3_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    v___x_3211_ = lean_apply_2(v_f_3204_, v_x3_3210_, v_x1_3208_);
    v___x_3212_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3212_, 0, v___x_3211_);
    v___x_3213_ = lean_apply_2(v_toPure_3205_, lean_box(0), v___x_3212_);
    v___x_3214_ = lean_apply_4(
        v_toBind_3206_,
        lean_box(0),
        lean_box(0),
        v___x_3213_,
        v___f_3207_,
    );
    return v___x_3214_;
}
pub unsafe fn l_Std_IterM_fold___redArg(
    mut v_inst_3215_: *mut LeanObject,
    mut v_inst_3216_: *mut LeanObject,
    mut v_f_3217_: *mut LeanObject,
    mut v_init_3218_: *mut LeanObject,
    mut v_it_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3220_ = lean_ctor_get(v_inst_3215_, 0);
    lean_inc_ref(v_toApplicative_3220_);
    v_toBind_3221_ = lean_ctor_get(v_inst_3215_, 1);
    lean_inc_n(v_toBind_3221_, 2);
    lean_dec_ref(v_inst_3215_);
    v_toPure_3222_ = lean_ctor_get(v_toApplicative_3220_, 1);
    lean_inc_n(v_toPure_3222_, 2);
    lean_dec_ref(v_toApplicative_3220_);
    v___f_3223_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3223_, 0, v_toBind_3221_);
    v___f_3224_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3224_, 0, v_toPure_3222_);
    v___f_3225_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3225_, 0, v_f_3217_);
    lean_closure_set(v___f_3225_, 1, v_toPure_3222_);
    lean_closure_set(v___f_3225_, 2, v_toBind_3221_);
    lean_closure_set(v___f_3225_, 3, v___f_3224_);
    v___x_3226_ = lean_apply_6(
        v_inst_3216_,
        v___f_3223_,
        lean_box(0),
        lean_box(0),
        v_it_3219_,
        v_init_3218_,
        v___f_3225_,
    );
    return v___x_3226_;
}
pub unsafe fn l_Std_IterM_fold(
    mut v_m_3227_: *mut LeanObject,
    mut v_00_u03b1_3228_: *mut LeanObject,
    mut v_00_u03b2_3229_: *mut LeanObject,
    mut v_00_u03b3_3230_: *mut LeanObject,
    mut v_inst_3231_: *mut LeanObject,
    mut v_inst_3232_: *mut LeanObject,
    mut v_inst_3233_: *mut LeanObject,
    mut v_f_3234_: *mut LeanObject,
    mut v_init_3235_: *mut LeanObject,
    mut v_it_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3237_ = lean_ctor_get(v_inst_3231_, 0);
    lean_inc_ref(v_toApplicative_3237_);
    v_toBind_3238_ = lean_ctor_get(v_inst_3231_, 1);
    lean_inc_n(v_toBind_3238_, 2);
    lean_dec_ref(v_inst_3231_);
    v_toPure_3239_ = lean_ctor_get(v_toApplicative_3237_, 1);
    lean_inc_n(v_toPure_3239_, 2);
    lean_dec_ref(v_toApplicative_3237_);
    v___f_3240_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3240_, 0, v_toBind_3238_);
    v___f_3241_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3241_, 0, v_toPure_3239_);
    v___f_3242_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3242_, 0, v_f_3234_);
    lean_closure_set(v___f_3242_, 1, v_toPure_3239_);
    lean_closure_set(v___f_3242_, 2, v_toBind_3238_);
    lean_closure_set(v___f_3242_, 3, v___f_3241_);
    v___x_3243_ = lean_apply_6(
        v_inst_3233_,
        v___f_3240_,
        lean_box(0),
        lean_box(0),
        v_it_3236_,
        v_init_3235_,
        v___f_3242_,
    );
    return v___x_3243_;
}
pub unsafe fn l_Std_IterM_fold___boxed(
    mut v_m_3244_: *mut LeanObject,
    mut v_00_u03b1_3245_: *mut LeanObject,
    mut v_00_u03b2_3246_: *mut LeanObject,
    mut v_00_u03b3_3247_: *mut LeanObject,
    mut v_inst_3248_: *mut LeanObject,
    mut v_inst_3249_: *mut LeanObject,
    mut v_inst_3250_: *mut LeanObject,
    mut v_f_3251_: *mut LeanObject,
    mut v_init_3252_: *mut LeanObject,
    mut v_it_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3254_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3249_);
    return v_res_3254_;
}
pub unsafe fn l_Std_IterM_Partial_fold___redArg(
    mut v_inst_3255_: *mut LeanObject,
    mut v_inst_3256_: *mut LeanObject,
    mut v_f_3257_: *mut LeanObject,
    mut v_init_3258_: *mut LeanObject,
    mut v_it_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3260_ = lean_ctor_get(v_inst_3255_, 0);
    lean_inc_ref(v_toApplicative_3260_);
    v_toBind_3261_ = lean_ctor_get(v_inst_3255_, 1);
    lean_inc_n(v_toBind_3261_, 2);
    lean_dec_ref(v_inst_3255_);
    v_toPure_3262_ = lean_ctor_get(v_toApplicative_3260_, 1);
    lean_inc_n(v_toPure_3262_, 2);
    lean_dec_ref(v_toApplicative_3260_);
    v___f_3263_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3263_, 0, v_toBind_3261_);
    v___f_3264_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3264_, 0, v_toPure_3262_);
    v___f_3265_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3265_, 0, v_f_3257_);
    lean_closure_set(v___f_3265_, 1, v_toPure_3262_);
    lean_closure_set(v___f_3265_, 2, v_toBind_3261_);
    lean_closure_set(v___f_3265_, 3, v___f_3264_);
    v___x_3266_ = lean_apply_6(
        v_inst_3256_,
        v___f_3263_,
        lean_box(0),
        lean_box(0),
        v_it_3259_,
        v_init_3258_,
        v___f_3265_,
    );
    return v___x_3266_;
}
pub unsafe fn l_Std_IterM_Partial_fold(
    mut v_m_3267_: *mut LeanObject,
    mut v_00_u03b1_3268_: *mut LeanObject,
    mut v_00_u03b2_3269_: *mut LeanObject,
    mut v_00_u03b3_3270_: *mut LeanObject,
    mut v_inst_3271_: *mut LeanObject,
    mut v_inst_3272_: *mut LeanObject,
    mut v_inst_3273_: *mut LeanObject,
    mut v_f_3274_: *mut LeanObject,
    mut v_init_3275_: *mut LeanObject,
    mut v_it_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3277_ = lean_ctor_get(v_inst_3271_, 0);
    lean_inc_ref(v_toApplicative_3277_);
    v_toBind_3278_ = lean_ctor_get(v_inst_3271_, 1);
    lean_inc_n(v_toBind_3278_, 2);
    lean_dec_ref(v_inst_3271_);
    v_toPure_3279_ = lean_ctor_get(v_toApplicative_3277_, 1);
    lean_inc_n(v_toPure_3279_, 2);
    lean_dec_ref(v_toApplicative_3277_);
    v___f_3280_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3280_, 0, v_toBind_3278_);
    v___f_3281_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3281_, 0, v_toPure_3279_);
    v___f_3282_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3282_, 0, v_f_3274_);
    lean_closure_set(v___f_3282_, 1, v_toPure_3279_);
    lean_closure_set(v___f_3282_, 2, v_toBind_3278_);
    lean_closure_set(v___f_3282_, 3, v___f_3281_);
    v___x_3283_ = lean_apply_6(
        v_inst_3273_,
        v___f_3280_,
        lean_box(0),
        lean_box(0),
        v_it_3276_,
        v_init_3275_,
        v___f_3282_,
    );
    return v___x_3283_;
}
pub unsafe fn l_Std_IterM_Partial_fold___boxed(
    mut v_m_3284_: *mut LeanObject,
    mut v_00_u03b1_3285_: *mut LeanObject,
    mut v_00_u03b2_3286_: *mut LeanObject,
    mut v_00_u03b3_3287_: *mut LeanObject,
    mut v_inst_3288_: *mut LeanObject,
    mut v_inst_3289_: *mut LeanObject,
    mut v_inst_3290_: *mut LeanObject,
    mut v_f_3291_: *mut LeanObject,
    mut v_init_3292_: *mut LeanObject,
    mut v_it_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3294_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3289_);
    return v_res_3294_;
}
pub unsafe fn l_Std_IterM_Total_fold___redArg(
    mut v_inst_3295_: *mut LeanObject,
    mut v_inst_3296_: *mut LeanObject,
    mut v_f_3297_: *mut LeanObject,
    mut v_init_3298_: *mut LeanObject,
    mut v_it_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3300_ = lean_ctor_get(v_inst_3295_, 0);
    lean_inc_ref(v_toApplicative_3300_);
    v_toBind_3301_ = lean_ctor_get(v_inst_3295_, 1);
    lean_inc_n(v_toBind_3301_, 2);
    lean_dec_ref(v_inst_3295_);
    v_toPure_3302_ = lean_ctor_get(v_toApplicative_3300_, 1);
    lean_inc_n(v_toPure_3302_, 2);
    lean_dec_ref(v_toApplicative_3300_);
    v___f_3303_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3303_, 0, v_toBind_3301_);
    v___f_3304_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3304_, 0, v_toPure_3302_);
    v___f_3305_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3305_, 0, v_f_3297_);
    lean_closure_set(v___f_3305_, 1, v_toPure_3302_);
    lean_closure_set(v___f_3305_, 2, v_toBind_3301_);
    lean_closure_set(v___f_3305_, 3, v___f_3304_);
    v___x_3306_ = lean_apply_6(
        v_inst_3296_,
        v___f_3303_,
        lean_box(0),
        lean_box(0),
        v_it_3299_,
        v_init_3298_,
        v___f_3305_,
    );
    return v___x_3306_;
}
pub unsafe fn l_Std_IterM_Total_fold(
    mut v_m_3307_: *mut LeanObject,
    mut v_00_u03b1_3308_: *mut LeanObject,
    mut v_00_u03b2_3309_: *mut LeanObject,
    mut v_00_u03b3_3310_: *mut LeanObject,
    mut v_inst_3311_: *mut LeanObject,
    mut v_inst_3312_: *mut LeanObject,
    mut v_inst_3313_: *mut LeanObject,
    mut v_inst_3314_: *mut LeanObject,
    mut v_f_3315_: *mut LeanObject,
    mut v_init_3316_: *mut LeanObject,
    mut v_it_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3318_ = lean_ctor_get(v_inst_3311_, 0);
    lean_inc_ref(v_toApplicative_3318_);
    v_toBind_3319_ = lean_ctor_get(v_inst_3311_, 1);
    lean_inc_n(v_toBind_3319_, 2);
    lean_dec_ref(v_inst_3311_);
    v_toPure_3320_ = lean_ctor_get(v_toApplicative_3318_, 1);
    lean_inc_n(v_toPure_3320_, 2);
    lean_dec_ref(v_toApplicative_3318_);
    v___f_3321_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3321_, 0, v_toBind_3319_);
    v___f_3322_ = lean_alloc_closure(
        l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3322_, 0, v_toPure_3320_);
    v___f_3323_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3323_, 0, v_f_3315_);
    lean_closure_set(v___f_3323_, 1, v_toPure_3320_);
    lean_closure_set(v___f_3323_, 2, v_toBind_3319_);
    lean_closure_set(v___f_3323_, 3, v___f_3322_);
    v___x_3324_ = lean_apply_6(
        v_inst_3313_,
        v___f_3321_,
        lean_box(0),
        lean_box(0),
        v_it_3317_,
        v_init_3316_,
        v___f_3323_,
    );
    return v___x_3324_;
}
pub unsafe fn l_Std_IterM_Total_fold___boxed(
    mut v_m_3325_: *mut LeanObject,
    mut v_00_u03b1_3326_: *mut LeanObject,
    mut v_00_u03b2_3327_: *mut LeanObject,
    mut v_00_u03b3_3328_: *mut LeanObject,
    mut v_inst_3329_: *mut LeanObject,
    mut v_inst_3330_: *mut LeanObject,
    mut v_inst_3331_: *mut LeanObject,
    mut v_inst_3332_: *mut LeanObject,
    mut v_f_3333_: *mut LeanObject,
    mut v_init_3334_: *mut LeanObject,
    mut v_it_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3330_);
    return v_res_3336_;
}
pub unsafe fn l_Std_IterM_drain___redArg___lam__2(
    mut v___x_3337_: *mut LeanObject,
    mut v_toPure_3338_: *mut LeanObject,
    mut v_toBind_3339_: *mut LeanObject,
    mut v___f_3340_: *mut LeanObject,
    mut v_x1_3341_: *mut LeanObject,
    mut v_x2_3342_: *mut LeanObject,
    mut v_x3_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3344_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3344_, 0, v___x_3337_);
    v___x_3345_ = lean_apply_2(v_toPure_3338_, lean_box(0), v___x_3344_);
    v___x_3346_ = lean_apply_4(
        v_toBind_3339_,
        lean_box(0),
        lean_box(0),
        v___x_3345_,
        v___f_3340_,
    );
    return v___x_3346_;
}
pub unsafe fn l_Std_IterM_drain___redArg___lam__2___boxed(
    mut v___x_3347_: *mut LeanObject,
    mut v_toPure_3348_: *mut LeanObject,
    mut v_toBind_3349_: *mut LeanObject,
    mut v___f_3350_: *mut LeanObject,
    mut v_x1_3351_: *mut LeanObject,
    mut v_x2_3352_: *mut LeanObject,
    mut v_x3_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3354_: *mut LeanObject = core::ptr::null_mut();
    v_res_3354_ = l_Std_IterM_drain___redArg___lam__2(
        v___x_3347_,
        v_toPure_3348_,
        v_toBind_3349_,
        v___f_3350_,
        v_x1_3351_,
        v_x2_3352_,
        v_x3_3353_,
    );
    lean_dec(v_x1_3351_);
    return v_res_3354_;
}
pub unsafe fn l_Std_IterM_drain___redArg(
    mut v_inst_3355_: *mut LeanObject,
    mut v_it_3356_: *mut LeanObject,
    mut v_inst_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3358_ = lean_ctor_get(v_inst_3355_, 0);
    lean_inc_ref(v_toApplicative_3358_);
    v_toBind_3359_ = lean_ctor_get(v_inst_3355_, 1);
    lean_inc_n(v_toBind_3359_, 2);
    lean_dec_ref(v_inst_3355_);
    v_toPure_3360_ = lean_ctor_get(v_toApplicative_3358_, 1);
    lean_inc_n(v_toPure_3360_, 2);
    lean_dec_ref(v_toApplicative_3358_);
    v___x_3361_ = lean_box(0);
    v___f_3362_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3362_, 0, v_toBind_3359_);
    v___f_3363_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3363_, 0, v_toPure_3360_);
    v___f_3364_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3364_, 0, v___x_3361_);
    lean_closure_set(v___f_3364_, 1, v_toPure_3360_);
    lean_closure_set(v___f_3364_, 2, v_toBind_3359_);
    lean_closure_set(v___f_3364_, 3, v___f_3363_);
    v___x_3365_ = lean_apply_6(
        v_inst_3357_,
        v___f_3362_,
        lean_box(0),
        lean_box(0),
        v_it_3356_,
        v___x_3361_,
        v___f_3364_,
    );
    return v___x_3365_;
}
pub unsafe fn l_Std_IterM_drain(
    mut v_00_u03b1_3366_: *mut LeanObject,
    mut v_m_3367_: *mut LeanObject,
    mut v_inst_3368_: *mut LeanObject,
    mut v_00_u03b2_3369_: *mut LeanObject,
    mut v_inst_3370_: *mut LeanObject,
    mut v_it_3371_: *mut LeanObject,
    mut v_inst_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3373_ = lean_ctor_get(v_inst_3368_, 0);
    lean_inc_ref(v_toApplicative_3373_);
    v_toBind_3374_ = lean_ctor_get(v_inst_3368_, 1);
    lean_inc_n(v_toBind_3374_, 2);
    lean_dec_ref(v_inst_3368_);
    v_toPure_3375_ = lean_ctor_get(v_toApplicative_3373_, 1);
    lean_inc_n(v_toPure_3375_, 2);
    lean_dec_ref(v_toApplicative_3373_);
    v___x_3376_ = lean_box(0);
    v___f_3377_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3377_, 0, v_toBind_3374_);
    v___f_3378_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3378_, 0, v_toPure_3375_);
    v___f_3379_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3379_, 0, v___x_3376_);
    lean_closure_set(v___f_3379_, 1, v_toPure_3375_);
    lean_closure_set(v___f_3379_, 2, v_toBind_3374_);
    lean_closure_set(v___f_3379_, 3, v___f_3378_);
    v___x_3380_ = lean_apply_6(
        v_inst_3372_,
        v___f_3377_,
        lean_box(0),
        lean_box(0),
        v_it_3371_,
        v___x_3376_,
        v___f_3379_,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_IterM_drain___boxed(
    mut v_00_u03b1_3381_: *mut LeanObject,
    mut v_m_3382_: *mut LeanObject,
    mut v_inst_3383_: *mut LeanObject,
    mut v_00_u03b2_3384_: *mut LeanObject,
    mut v_inst_3385_: *mut LeanObject,
    mut v_it_3386_: *mut LeanObject,
    mut v_inst_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Std_IterM_drain(
        v_00_u03b1_3381_,
        v_m_3382_,
        v_inst_3383_,
        v_00_u03b2_3384_,
        v_inst_3385_,
        v_it_3386_,
        v_inst_3387_,
    );
    lean_dec(v_inst_3385_);
    return v_res_3388_;
}
pub unsafe fn l_Std_IterM_Partial_drain___redArg(
    mut v_inst_3389_: *mut LeanObject,
    mut v_it_3390_: *mut LeanObject,
    mut v_inst_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3392_ = lean_ctor_get(v_inst_3389_, 0);
    lean_inc_ref(v_toApplicative_3392_);
    v_toBind_3393_ = lean_ctor_get(v_inst_3389_, 1);
    lean_inc_n(v_toBind_3393_, 2);
    lean_dec_ref(v_inst_3389_);
    v_toPure_3394_ = lean_ctor_get(v_toApplicative_3392_, 1);
    lean_inc_n(v_toPure_3394_, 2);
    lean_dec_ref(v_toApplicative_3392_);
    v___x_3395_ = lean_box(0);
    v___f_3396_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3396_, 0, v_toBind_3393_);
    v___f_3397_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3397_, 0, v_toPure_3394_);
    v___f_3398_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3398_, 0, v___x_3395_);
    lean_closure_set(v___f_3398_, 1, v_toPure_3394_);
    lean_closure_set(v___f_3398_, 2, v_toBind_3393_);
    lean_closure_set(v___f_3398_, 3, v___f_3397_);
    v___x_3399_ = lean_apply_6(
        v_inst_3391_,
        v___f_3396_,
        lean_box(0),
        lean_box(0),
        v_it_3390_,
        v___x_3395_,
        v___f_3398_,
    );
    return v___x_3399_;
}
pub unsafe fn l_Std_IterM_Partial_drain(
    mut v_00_u03b1_3400_: *mut LeanObject,
    mut v_m_3401_: *mut LeanObject,
    mut v_inst_3402_: *mut LeanObject,
    mut v_00_u03b2_3403_: *mut LeanObject,
    mut v_inst_3404_: *mut LeanObject,
    mut v_it_3405_: *mut LeanObject,
    mut v_inst_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3407_ = lean_ctor_get(v_inst_3402_, 0);
    lean_inc_ref(v_toApplicative_3407_);
    v_toBind_3408_ = lean_ctor_get(v_inst_3402_, 1);
    lean_inc_n(v_toBind_3408_, 2);
    lean_dec_ref(v_inst_3402_);
    v_toPure_3409_ = lean_ctor_get(v_toApplicative_3407_, 1);
    lean_inc_n(v_toPure_3409_, 2);
    lean_dec_ref(v_toApplicative_3407_);
    v___x_3410_ = lean_box(0);
    v___f_3411_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3411_, 0, v_toBind_3408_);
    v___f_3412_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3412_, 0, v_toPure_3409_);
    v___f_3413_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3413_, 0, v___x_3410_);
    lean_closure_set(v___f_3413_, 1, v_toPure_3409_);
    lean_closure_set(v___f_3413_, 2, v_toBind_3408_);
    lean_closure_set(v___f_3413_, 3, v___f_3412_);
    v___x_3414_ = lean_apply_6(
        v_inst_3406_,
        v___f_3411_,
        lean_box(0),
        lean_box(0),
        v_it_3405_,
        v___x_3410_,
        v___f_3413_,
    );
    return v___x_3414_;
}
pub unsafe fn l_Std_IterM_Partial_drain___boxed(
    mut v_00_u03b1_3415_: *mut LeanObject,
    mut v_m_3416_: *mut LeanObject,
    mut v_inst_3417_: *mut LeanObject,
    mut v_00_u03b2_3418_: *mut LeanObject,
    mut v_inst_3419_: *mut LeanObject,
    mut v_it_3420_: *mut LeanObject,
    mut v_inst_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Std_IterM_Partial_drain(
        v_00_u03b1_3415_,
        v_m_3416_,
        v_inst_3417_,
        v_00_u03b2_3418_,
        v_inst_3419_,
        v_it_3420_,
        v_inst_3421_,
    );
    lean_dec(v_inst_3419_);
    return v_res_3422_;
}
pub unsafe fn l_Std_IterM_Total_drain___redArg(
    mut v_inst_3423_: *mut LeanObject,
    mut v_it_3424_: *mut LeanObject,
    mut v_inst_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3426_ = lean_ctor_get(v_inst_3423_, 0);
    lean_inc_ref(v_toApplicative_3426_);
    v_toBind_3427_ = lean_ctor_get(v_inst_3423_, 1);
    lean_inc_n(v_toBind_3427_, 2);
    lean_dec_ref(v_inst_3423_);
    v_toPure_3428_ = lean_ctor_get(v_toApplicative_3426_, 1);
    lean_inc_n(v_toPure_3428_, 2);
    lean_dec_ref(v_toApplicative_3426_);
    v___x_3429_ = lean_box(0);
    v___f_3430_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3430_, 0, v_toBind_3427_);
    v___f_3431_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3431_, 0, v_toPure_3428_);
    v___f_3432_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3432_, 0, v___x_3429_);
    lean_closure_set(v___f_3432_, 1, v_toPure_3428_);
    lean_closure_set(v___f_3432_, 2, v_toBind_3427_);
    lean_closure_set(v___f_3432_, 3, v___f_3431_);
    v___x_3433_ = lean_apply_6(
        v_inst_3425_,
        v___f_3430_,
        lean_box(0),
        lean_box(0),
        v_it_3424_,
        v___x_3429_,
        v___f_3432_,
    );
    return v___x_3433_;
}
pub unsafe fn l_Std_IterM_Total_drain(
    mut v_00_u03b1_3434_: *mut LeanObject,
    mut v_m_3435_: *mut LeanObject,
    mut v_inst_3436_: *mut LeanObject,
    mut v_00_u03b2_3437_: *mut LeanObject,
    mut v_inst_3438_: *mut LeanObject,
    mut v_inst_3439_: *mut LeanObject,
    mut v_it_3440_: *mut LeanObject,
    mut v_inst_3441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3442_ = lean_ctor_get(v_inst_3436_, 0);
    lean_inc_ref(v_toApplicative_3442_);
    v_toBind_3443_ = lean_ctor_get(v_inst_3436_, 1);
    lean_inc_n(v_toBind_3443_, 2);
    lean_dec_ref(v_inst_3436_);
    v_toPure_3444_ = lean_ctor_get(v_toApplicative_3442_, 1);
    lean_inc_n(v_toPure_3444_, 2);
    lean_dec_ref(v_toApplicative_3442_);
    v___x_3445_ = lean_box(0);
    v___f_3446_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3446_, 0, v_toBind_3443_);
    v___f_3447_ = lean_alloc_closure(
        l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3447_, 0, v_toPure_3444_);
    v___f_3448_ = lean_alloc_closure(
        l_Std_IterM_drain___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3448_, 0, v___x_3445_);
    lean_closure_set(v___f_3448_, 1, v_toPure_3444_);
    lean_closure_set(v___f_3448_, 2, v_toBind_3443_);
    lean_closure_set(v___f_3448_, 3, v___f_3447_);
    v___x_3449_ = lean_apply_6(
        v_inst_3441_,
        v___f_3446_,
        lean_box(0),
        lean_box(0),
        v_it_3440_,
        v___x_3445_,
        v___f_3448_,
    );
    return v___x_3449_;
}
pub unsafe fn l_Std_IterM_Total_drain___boxed(
    mut v_00_u03b1_3450_: *mut LeanObject,
    mut v_m_3451_: *mut LeanObject,
    mut v_inst_3452_: *mut LeanObject,
    mut v_00_u03b2_3453_: *mut LeanObject,
    mut v_inst_3454_: *mut LeanObject,
    mut v_inst_3455_: *mut LeanObject,
    mut v_it_3456_: *mut LeanObject,
    mut v_inst_3457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3458_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3454_);
    return v_res_3458_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__1(
    mut v_toPure_3459_: *mut LeanObject,
    mut v_____do__lift_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    v___x_3461_ = lean_apply_2(v_toPure_3459_, lean_box(0), v_____do__lift_3460_);
    return v___x_3461_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__0(
    mut v___x_3462_: u8,
    mut v_toPure_3463_: *mut LeanObject,
    mut v_____do__lift_3464_: u8,
) -> *mut LeanObject {
    if v_____do__lift_3464_ == 0 {
        let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
        v___x_3465_ = lean_box((v___x_3462_) as usize);
        v___x_3466_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3466_, 0, v___x_3465_);
        v___x_3467_ = lean_apply_2(v_toPure_3463_, lean_box(0), v___x_3466_);
        return v___x_3467_;
    } else {
        let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
        v___x_3468_ = lean_box((v_____do__lift_3464_) as usize);
        v___x_3469_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3469_, 0, v___x_3468_);
        v___x_3470_ = lean_apply_2(v_toPure_3463_, lean_box(0), v___x_3469_);
        return v___x_3470_;
    }
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__0___boxed(
    mut v___x_3471_: *mut LeanObject,
    mut v_toPure_3472_: *mut LeanObject,
    mut v_____do__lift_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_203__boxed_3474_: u8 = 0;
    let mut v_____do__lift_204__boxed_3475_: u8 = 0;
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v___x_203__boxed_3474_ = (lean_unbox(v___x_3471_) as u8);
    v_____do__lift_204__boxed_3475_ = (lean_unbox(v_____do__lift_3473_) as u8);
    v_res_3476_ = l_Std_IterM_anyM___redArg___lam__0(
        v___x_203__boxed_3474_,
        v_toPure_3472_,
        v_____do__lift_204__boxed_3475_,
    );
    return v_res_3476_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__2(
    mut v_p_3477_: *mut LeanObject,
    mut v_toBind_3478_: *mut LeanObject,
    mut v___f_3479_: *mut LeanObject,
    mut v___f_3480_: *mut LeanObject,
    mut v_x1_3481_: *mut LeanObject,
    mut v_x2_3482_: *mut LeanObject,
    mut v_x3_3483_: u8,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = lean_apply_1(v_p_3477_, v_x1_3481_);
    lean_inc(v_toBind_3478_);
    v___x_3485_ = lean_apply_4(
        v_toBind_3478_,
        lean_box(0),
        lean_box(0),
        v___x_3484_,
        v___f_3479_,
    );
    v___x_3486_ = lean_apply_4(
        v_toBind_3478_,
        lean_box(0),
        lean_box(0),
        v___x_3485_,
        v___f_3480_,
    );
    return v___x_3486_;
}
pub unsafe fn l_Std_IterM_anyM___redArg___lam__2___boxed(
    mut v_p_3487_: *mut LeanObject,
    mut v_toBind_3488_: *mut LeanObject,
    mut v___f_3489_: *mut LeanObject,
    mut v___f_3490_: *mut LeanObject,
    mut v_x1_3491_: *mut LeanObject,
    mut v_x2_3492_: *mut LeanObject,
    mut v_x3_3493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x3_225__boxed_3494_: u8 = 0;
    let mut v_res_3495_: *mut LeanObject = core::ptr::null_mut();
    v_x3_225__boxed_3494_ = (lean_unbox(v_x3_3493_) as u8);
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
    mut v_inst_3496_: *mut LeanObject,
    mut v_inst_3497_: *mut LeanObject,
    mut v_p_3498_: *mut LeanObject,
    mut v_it_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3500_ = lean_ctor_get(v_inst_3496_, 0);
    lean_inc_ref(v_toApplicative_3500_);
    v_toBind_3501_ = lean_ctor_get(v_inst_3496_, 1);
    lean_inc_n(v_toBind_3501_, 2);
    lean_dec_ref(v_inst_3496_);
    v_toPure_3502_ = lean_ctor_get(v_toApplicative_3500_, 1);
    lean_inc_n(v_toPure_3502_, 2);
    lean_dec_ref(v_toApplicative_3500_);
    v___f_3503_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3503_, 0, v_toBind_3501_);
    v___f_3504_ = lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3504_, 0, v_toPure_3502_);
    v___x_3505_ = 0;
    v___x_3506_ = lean_box((v___x_3505_) as usize);
    v___f_3507_ = lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3507_, 0, v___x_3506_);
    lean_closure_set(v___f_3507_, 1, v_toPure_3502_);
    v___f_3508_ = lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3508_, 0, v_p_3498_);
    lean_closure_set(v___f_3508_, 1, v_toBind_3501_);
    lean_closure_set(v___f_3508_, 2, v___f_3507_);
    lean_closure_set(v___f_3508_, 3, v___f_3504_);
    v___x_3509_ = lean_box((v___x_3505_) as usize);
    v___x_3510_ = lean_apply_6(
        v_inst_3497_,
        v___f_3503_,
        lean_box(0),
        lean_box(0),
        v_it_3499_,
        v___x_3509_,
        v___f_3508_,
    );
    return v___x_3510_;
}
pub unsafe fn l_Std_IterM_anyM(
    mut v_00_u03b1_3511_: *mut LeanObject,
    mut v_00_u03b2_3512_: *mut LeanObject,
    mut v_m_3513_: *mut LeanObject,
    mut v_inst_3514_: *mut LeanObject,
    mut v_inst_3515_: *mut LeanObject,
    mut v_inst_3516_: *mut LeanObject,
    mut v_p_3517_: *mut LeanObject,
    mut v_it_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Std_IterM_anyM___redArg(v_inst_3514_, v_inst_3516_, v_p_3517_, v_it_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Std_IterM_anyM___boxed(
    mut v_00_u03b1_3520_: *mut LeanObject,
    mut v_00_u03b2_3521_: *mut LeanObject,
    mut v_m_3522_: *mut LeanObject,
    mut v_inst_3523_: *mut LeanObject,
    mut v_inst_3524_: *mut LeanObject,
    mut v_inst_3525_: *mut LeanObject,
    mut v_p_3526_: *mut LeanObject,
    mut v_it_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3528_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3524_);
    return v_res_3528_;
}
pub unsafe fn l_Std_IterM_Partial_anyM___redArg(
    mut v_inst_3529_: *mut LeanObject,
    mut v_inst_3530_: *mut LeanObject,
    mut v_p_3531_: *mut LeanObject,
    mut v_it_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v___x_3533_ = l_Std_IterM_anyM___redArg(v_inst_3529_, v_inst_3530_, v_p_3531_, v_it_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Std_IterM_Partial_anyM(
    mut v_00_u03b1_3534_: *mut LeanObject,
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_m_3536_: *mut LeanObject,
    mut v_inst_3537_: *mut LeanObject,
    mut v_inst_3538_: *mut LeanObject,
    mut v_inst_3539_: *mut LeanObject,
    mut v_p_3540_: *mut LeanObject,
    mut v_it_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = l_Std_IterM_anyM___redArg(v_inst_3537_, v_inst_3539_, v_p_3540_, v_it_3541_);
    return v___x_3542_;
}
pub unsafe fn l_Std_IterM_Partial_anyM___boxed(
    mut v_00_u03b1_3543_: *mut LeanObject,
    mut v_00_u03b2_3544_: *mut LeanObject,
    mut v_m_3545_: *mut LeanObject,
    mut v_inst_3546_: *mut LeanObject,
    mut v_inst_3547_: *mut LeanObject,
    mut v_inst_3548_: *mut LeanObject,
    mut v_p_3549_: *mut LeanObject,
    mut v_it_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3551_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3547_);
    return v_res_3551_;
}
pub unsafe fn l_Std_IterM_Total_anyM___redArg(
    mut v_inst_3552_: *mut LeanObject,
    mut v_inst_3553_: *mut LeanObject,
    mut v_p_3554_: *mut LeanObject,
    mut v_it_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v___x_3556_ = l_Std_IterM_anyM___redArg(v_inst_3552_, v_inst_3553_, v_p_3554_, v_it_3555_);
    return v___x_3556_;
}
pub unsafe fn l_Std_IterM_Total_anyM(
    mut v_00_u03b1_3557_: *mut LeanObject,
    mut v_00_u03b2_3558_: *mut LeanObject,
    mut v_m_3559_: *mut LeanObject,
    mut v_inst_3560_: *mut LeanObject,
    mut v_inst_3561_: *mut LeanObject,
    mut v_inst_3562_: *mut LeanObject,
    mut v_inst_3563_: *mut LeanObject,
    mut v_p_3564_: *mut LeanObject,
    mut v_it_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    v___x_3566_ = l_Std_IterM_anyM___redArg(v_inst_3560_, v_inst_3562_, v_p_3564_, v_it_3565_);
    return v___x_3566_;
}
pub unsafe fn l_Std_IterM_Total_anyM___boxed(
    mut v_00_u03b1_3567_: *mut LeanObject,
    mut v_00_u03b2_3568_: *mut LeanObject,
    mut v_m_3569_: *mut LeanObject,
    mut v_inst_3570_: *mut LeanObject,
    mut v_inst_3571_: *mut LeanObject,
    mut v_inst_3572_: *mut LeanObject,
    mut v_inst_3573_: *mut LeanObject,
    mut v_p_3574_: *mut LeanObject,
    mut v_it_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3576_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3571_);
    return v_res_3576_;
}
pub unsafe fn l_Std_IterM_any___redArg___lam__0(
    mut v_p_3577_: *mut LeanObject,
    mut v_toPure_3578_: *mut LeanObject,
    mut v_x_3579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = lean_apply_1(v_p_3577_, v_x_3579_);
    v___x_3581_ = lean_apply_2(v_toPure_3578_, lean_box(0), v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn l_Std_IterM_any___redArg(
    mut v_inst_3582_: *mut LeanObject,
    mut v_inst_3583_: *mut LeanObject,
    mut v_p_3584_: *mut LeanObject,
    mut v_it_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3586_ = lean_ctor_get(v_inst_3582_, 0);
    v_toPure_3587_ = lean_ctor_get(v_toApplicative_3586_, 1);
    lean_inc(v_toPure_3587_);
    v___f_3588_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3588_, 0, v_p_3584_);
    lean_closure_set(v___f_3588_, 1, v_toPure_3587_);
    v___x_3589_ = l_Std_IterM_anyM___redArg(v_inst_3582_, v_inst_3583_, v___f_3588_, v_it_3585_);
    return v___x_3589_;
}
pub unsafe fn l_Std_IterM_any(
    mut v_00_u03b1_3590_: *mut LeanObject,
    mut v_00_u03b2_3591_: *mut LeanObject,
    mut v_m_3592_: *mut LeanObject,
    mut v_inst_3593_: *mut LeanObject,
    mut v_inst_3594_: *mut LeanObject,
    mut v_inst_3595_: *mut LeanObject,
    mut v_p_3596_: *mut LeanObject,
    mut v_it_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3598_ = lean_ctor_get(v_inst_3593_, 0);
    v_toPure_3599_ = lean_ctor_get(v_toApplicative_3598_, 1);
    lean_inc(v_toPure_3599_);
    v___f_3600_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3600_, 0, v_p_3596_);
    lean_closure_set(v___f_3600_, 1, v_toPure_3599_);
    v___x_3601_ = l_Std_IterM_anyM___redArg(v_inst_3593_, v_inst_3595_, v___f_3600_, v_it_3597_);
    return v___x_3601_;
}
pub unsafe fn l_Std_IterM_any___boxed(
    mut v_00_u03b1_3602_: *mut LeanObject,
    mut v_00_u03b2_3603_: *mut LeanObject,
    mut v_m_3604_: *mut LeanObject,
    mut v_inst_3605_: *mut LeanObject,
    mut v_inst_3606_: *mut LeanObject,
    mut v_inst_3607_: *mut LeanObject,
    mut v_p_3608_: *mut LeanObject,
    mut v_it_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3610_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3606_);
    return v_res_3610_;
}
pub unsafe fn l_Std_IterM_Partial_any___redArg(
    mut v_inst_3611_: *mut LeanObject,
    mut v_inst_3612_: *mut LeanObject,
    mut v_p_3613_: *mut LeanObject,
    mut v_it_3614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3615_ = lean_ctor_get(v_inst_3611_, 0);
    v_toPure_3616_ = lean_ctor_get(v_toApplicative_3615_, 1);
    lean_inc(v_toPure_3616_);
    v___f_3617_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3617_, 0, v_p_3613_);
    lean_closure_set(v___f_3617_, 1, v_toPure_3616_);
    v___x_3618_ = l_Std_IterM_anyM___redArg(v_inst_3611_, v_inst_3612_, v___f_3617_, v_it_3614_);
    return v___x_3618_;
}
pub unsafe fn l_Std_IterM_Partial_any(
    mut v_00_u03b1_3619_: *mut LeanObject,
    mut v_00_u03b2_3620_: *mut LeanObject,
    mut v_m_3621_: *mut LeanObject,
    mut v_inst_3622_: *mut LeanObject,
    mut v_inst_3623_: *mut LeanObject,
    mut v_inst_3624_: *mut LeanObject,
    mut v_p_3625_: *mut LeanObject,
    mut v_it_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3627_ = lean_ctor_get(v_inst_3622_, 0);
    v_toPure_3628_ = lean_ctor_get(v_toApplicative_3627_, 1);
    lean_inc(v_toPure_3628_);
    v___f_3629_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3629_, 0, v_p_3625_);
    lean_closure_set(v___f_3629_, 1, v_toPure_3628_);
    v___x_3630_ = l_Std_IterM_anyM___redArg(v_inst_3622_, v_inst_3624_, v___f_3629_, v_it_3626_);
    return v___x_3630_;
}
pub unsafe fn l_Std_IterM_Partial_any___boxed(
    mut v_00_u03b1_3631_: *mut LeanObject,
    mut v_00_u03b2_3632_: *mut LeanObject,
    mut v_m_3633_: *mut LeanObject,
    mut v_inst_3634_: *mut LeanObject,
    mut v_inst_3635_: *mut LeanObject,
    mut v_inst_3636_: *mut LeanObject,
    mut v_p_3637_: *mut LeanObject,
    mut v_it_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3639_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3635_);
    return v_res_3639_;
}
pub unsafe fn l_Std_IterM_Total_any___redArg(
    mut v_inst_3640_: *mut LeanObject,
    mut v_inst_3641_: *mut LeanObject,
    mut v_p_3642_: *mut LeanObject,
    mut v_it_3643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3644_ = lean_ctor_get(v_inst_3640_, 0);
    v_toPure_3645_ = lean_ctor_get(v_toApplicative_3644_, 1);
    lean_inc(v_toPure_3645_);
    v___f_3646_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3646_, 0, v_p_3642_);
    lean_closure_set(v___f_3646_, 1, v_toPure_3645_);
    v___x_3647_ = l_Std_IterM_anyM___redArg(v_inst_3640_, v_inst_3641_, v___f_3646_, v_it_3643_);
    return v___x_3647_;
}
pub unsafe fn l_Std_IterM_Total_any(
    mut v_00_u03b1_3648_: *mut LeanObject,
    mut v_00_u03b2_3649_: *mut LeanObject,
    mut v_m_3650_: *mut LeanObject,
    mut v_inst_3651_: *mut LeanObject,
    mut v_inst_3652_: *mut LeanObject,
    mut v_inst_3653_: *mut LeanObject,
    mut v_inst_3654_: *mut LeanObject,
    mut v_p_3655_: *mut LeanObject,
    mut v_it_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3657_ = lean_ctor_get(v_inst_3651_, 0);
    v_toPure_3658_ = lean_ctor_get(v_toApplicative_3657_, 1);
    lean_inc(v_toPure_3658_);
    v___f_3659_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3659_, 0, v_p_3655_);
    lean_closure_set(v___f_3659_, 1, v_toPure_3658_);
    v___x_3660_ = l_Std_IterM_anyM___redArg(v_inst_3651_, v_inst_3653_, v___f_3659_, v_it_3656_);
    return v___x_3660_;
}
pub unsafe fn l_Std_IterM_Total_any___boxed(
    mut v_00_u03b1_3661_: *mut LeanObject,
    mut v_00_u03b2_3662_: *mut LeanObject,
    mut v_m_3663_: *mut LeanObject,
    mut v_inst_3664_: *mut LeanObject,
    mut v_inst_3665_: *mut LeanObject,
    mut v_inst_3666_: *mut LeanObject,
    mut v_inst_3667_: *mut LeanObject,
    mut v_p_3668_: *mut LeanObject,
    mut v_it_3669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3670_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3665_);
    return v_res_3670_;
}
pub unsafe fn l_Std_IterM_allM___redArg___lam__2(
    mut v_toPure_3671_: *mut LeanObject,
    mut v___x_3672_: u8,
    mut v_____do__lift_3673_: u8,
) -> *mut LeanObject {
    if v_____do__lift_3673_ == 0 {
        let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
        v___x_3674_ = lean_box((v_____do__lift_3673_) as usize);
        v___x_3675_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3675_, 0, v___x_3674_);
        v___x_3676_ = lean_apply_2(v_toPure_3671_, lean_box(0), v___x_3675_);
        return v___x_3676_;
    } else {
        let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
        v___x_3677_ = lean_box((v___x_3672_) as usize);
        v___x_3678_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3678_, 0, v___x_3677_);
        v___x_3679_ = lean_apply_2(v_toPure_3671_, lean_box(0), v___x_3678_);
        return v___x_3679_;
    }
}
pub unsafe fn l_Std_IterM_allM___redArg___lam__2___boxed(
    mut v_toPure_3680_: *mut LeanObject,
    mut v___x_3681_: *mut LeanObject,
    mut v_____do__lift_3682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_201__boxed_3683_: u8 = 0;
    let mut v_____do__lift_202__boxed_3684_: u8 = 0;
    let mut v_res_3685_: *mut LeanObject = core::ptr::null_mut();
    v___x_201__boxed_3683_ = (lean_unbox(v___x_3681_) as u8);
    v_____do__lift_202__boxed_3684_ = (lean_unbox(v_____do__lift_3682_) as u8);
    v_res_3685_ = l_Std_IterM_allM___redArg___lam__2(
        v_toPure_3680_,
        v___x_201__boxed_3683_,
        v_____do__lift_202__boxed_3684_,
    );
    return v_res_3685_;
}
pub unsafe fn l_Std_IterM_allM___redArg(
    mut v_inst_3686_: *mut LeanObject,
    mut v_inst_3687_: *mut LeanObject,
    mut v_p_3688_: *mut LeanObject,
    mut v_it_3689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3690_ = lean_ctor_get(v_inst_3686_, 0);
    lean_inc_ref(v_toApplicative_3690_);
    v_toBind_3691_ = lean_ctor_get(v_inst_3686_, 1);
    lean_inc_n(v_toBind_3691_, 2);
    lean_dec_ref(v_inst_3686_);
    v_toPure_3692_ = lean_ctor_get(v_toApplicative_3690_, 1);
    lean_inc_n(v_toPure_3692_, 2);
    lean_dec_ref(v_toApplicative_3690_);
    v___f_3693_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3693_, 0, v_toBind_3691_);
    v___f_3694_ = lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3694_, 0, v_toPure_3692_);
    v___x_3695_ = 1;
    v___x_3696_ = lean_box((v___x_3695_) as usize);
    v___f_3697_ = lean_alloc_closure(
        l_Std_IterM_allM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3697_, 0, v_toPure_3692_);
    lean_closure_set(v___f_3697_, 1, v___x_3696_);
    v___f_3698_ = lean_alloc_closure(
        l_Std_IterM_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3698_, 0, v_p_3688_);
    lean_closure_set(v___f_3698_, 1, v_toBind_3691_);
    lean_closure_set(v___f_3698_, 2, v___f_3697_);
    lean_closure_set(v___f_3698_, 3, v___f_3694_);
    v___x_3699_ = lean_box((v___x_3695_) as usize);
    v___x_3700_ = lean_apply_6(
        v_inst_3687_,
        v___f_3693_,
        lean_box(0),
        lean_box(0),
        v_it_3689_,
        v___x_3699_,
        v___f_3698_,
    );
    return v___x_3700_;
}
pub unsafe fn l_Std_IterM_allM(
    mut v_00_u03b1_3701_: *mut LeanObject,
    mut v_00_u03b2_3702_: *mut LeanObject,
    mut v_m_3703_: *mut LeanObject,
    mut v_inst_3704_: *mut LeanObject,
    mut v_inst_3705_: *mut LeanObject,
    mut v_inst_3706_: *mut LeanObject,
    mut v_p_3707_: *mut LeanObject,
    mut v_it_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    v___x_3709_ = l_Std_IterM_allM___redArg(v_inst_3704_, v_inst_3706_, v_p_3707_, v_it_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Std_IterM_allM___boxed(
    mut v_00_u03b1_3710_: *mut LeanObject,
    mut v_00_u03b2_3711_: *mut LeanObject,
    mut v_m_3712_: *mut LeanObject,
    mut v_inst_3713_: *mut LeanObject,
    mut v_inst_3714_: *mut LeanObject,
    mut v_inst_3715_: *mut LeanObject,
    mut v_p_3716_: *mut LeanObject,
    mut v_it_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3718_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3714_);
    return v_res_3718_;
}
pub unsafe fn l_Std_IterM_Partial_allM___redArg(
    mut v_inst_3719_: *mut LeanObject,
    mut v_inst_3720_: *mut LeanObject,
    mut v_p_3721_: *mut LeanObject,
    mut v_it_3722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_Std_IterM_allM___redArg(v_inst_3719_, v_inst_3720_, v_p_3721_, v_it_3722_);
    return v___x_3723_;
}
pub unsafe fn l_Std_IterM_Partial_allM(
    mut v_00_u03b1_3724_: *mut LeanObject,
    mut v_00_u03b2_3725_: *mut LeanObject,
    mut v_m_3726_: *mut LeanObject,
    mut v_inst_3727_: *mut LeanObject,
    mut v_inst_3728_: *mut LeanObject,
    mut v_inst_3729_: *mut LeanObject,
    mut v_p_3730_: *mut LeanObject,
    mut v_it_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    v___x_3732_ = l_Std_IterM_allM___redArg(v_inst_3727_, v_inst_3729_, v_p_3730_, v_it_3731_);
    return v___x_3732_;
}
pub unsafe fn l_Std_IterM_Partial_allM___boxed(
    mut v_00_u03b1_3733_: *mut LeanObject,
    mut v_00_u03b2_3734_: *mut LeanObject,
    mut v_m_3735_: *mut LeanObject,
    mut v_inst_3736_: *mut LeanObject,
    mut v_inst_3737_: *mut LeanObject,
    mut v_inst_3738_: *mut LeanObject,
    mut v_p_3739_: *mut LeanObject,
    mut v_it_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3737_);
    return v_res_3741_;
}
pub unsafe fn l_Std_IterM_Total_allM___redArg(
    mut v_inst_3742_: *mut LeanObject,
    mut v_inst_3743_: *mut LeanObject,
    mut v_p_3744_: *mut LeanObject,
    mut v_it_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Std_IterM_allM___redArg(v_inst_3742_, v_inst_3743_, v_p_3744_, v_it_3745_);
    return v___x_3746_;
}
pub unsafe fn l_Std_IterM_Total_allM(
    mut v_00_u03b1_3747_: *mut LeanObject,
    mut v_00_u03b2_3748_: *mut LeanObject,
    mut v_m_3749_: *mut LeanObject,
    mut v_inst_3750_: *mut LeanObject,
    mut v_inst_3751_: *mut LeanObject,
    mut v_inst_3752_: *mut LeanObject,
    mut v_inst_3753_: *mut LeanObject,
    mut v_p_3754_: *mut LeanObject,
    mut v_it_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    v___x_3756_ = l_Std_IterM_allM___redArg(v_inst_3750_, v_inst_3752_, v_p_3754_, v_it_3755_);
    return v___x_3756_;
}
pub unsafe fn l_Std_IterM_Total_allM___boxed(
    mut v_00_u03b1_3757_: *mut LeanObject,
    mut v_00_u03b2_3758_: *mut LeanObject,
    mut v_m_3759_: *mut LeanObject,
    mut v_inst_3760_: *mut LeanObject,
    mut v_inst_3761_: *mut LeanObject,
    mut v_inst_3762_: *mut LeanObject,
    mut v_inst_3763_: *mut LeanObject,
    mut v_p_3764_: *mut LeanObject,
    mut v_it_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3761_);
    return v_res_3766_;
}
pub unsafe fn l_Std_IterM_all___redArg(
    mut v_inst_3767_: *mut LeanObject,
    mut v_inst_3768_: *mut LeanObject,
    mut v_p_3769_: *mut LeanObject,
    mut v_it_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3771_ = lean_ctor_get(v_inst_3767_, 0);
    v_toPure_3772_ = lean_ctor_get(v_toApplicative_3771_, 1);
    lean_inc(v_toPure_3772_);
    v___f_3773_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3773_, 0, v_p_3769_);
    lean_closure_set(v___f_3773_, 1, v_toPure_3772_);
    v___x_3774_ = l_Std_IterM_allM___redArg(v_inst_3767_, v_inst_3768_, v___f_3773_, v_it_3770_);
    return v___x_3774_;
}
pub unsafe fn l_Std_IterM_all(
    mut v_00_u03b1_3775_: *mut LeanObject,
    mut v_00_u03b2_3776_: *mut LeanObject,
    mut v_m_3777_: *mut LeanObject,
    mut v_inst_3778_: *mut LeanObject,
    mut v_inst_3779_: *mut LeanObject,
    mut v_inst_3780_: *mut LeanObject,
    mut v_p_3781_: *mut LeanObject,
    mut v_it_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3783_ = lean_ctor_get(v_inst_3778_, 0);
    v_toPure_3784_ = lean_ctor_get(v_toApplicative_3783_, 1);
    lean_inc(v_toPure_3784_);
    v___f_3785_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3785_, 0, v_p_3781_);
    lean_closure_set(v___f_3785_, 1, v_toPure_3784_);
    v___x_3786_ = l_Std_IterM_allM___redArg(v_inst_3778_, v_inst_3780_, v___f_3785_, v_it_3782_);
    return v___x_3786_;
}
pub unsafe fn l_Std_IterM_all___boxed(
    mut v_00_u03b1_3787_: *mut LeanObject,
    mut v_00_u03b2_3788_: *mut LeanObject,
    mut v_m_3789_: *mut LeanObject,
    mut v_inst_3790_: *mut LeanObject,
    mut v_inst_3791_: *mut LeanObject,
    mut v_inst_3792_: *mut LeanObject,
    mut v_p_3793_: *mut LeanObject,
    mut v_it_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3791_);
    return v_res_3795_;
}
pub unsafe fn l_Std_IterM_Partial_all___redArg(
    mut v_inst_3796_: *mut LeanObject,
    mut v_inst_3797_: *mut LeanObject,
    mut v_p_3798_: *mut LeanObject,
    mut v_it_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3800_ = lean_ctor_get(v_inst_3796_, 0);
    v_toPure_3801_ = lean_ctor_get(v_toApplicative_3800_, 1);
    lean_inc(v_toPure_3801_);
    v___f_3802_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3802_, 0, v_p_3798_);
    lean_closure_set(v___f_3802_, 1, v_toPure_3801_);
    v___x_3803_ = l_Std_IterM_allM___redArg(v_inst_3796_, v_inst_3797_, v___f_3802_, v_it_3799_);
    return v___x_3803_;
}
pub unsafe fn l_Std_IterM_Partial_all(
    mut v_00_u03b1_3804_: *mut LeanObject,
    mut v_00_u03b2_3805_: *mut LeanObject,
    mut v_m_3806_: *mut LeanObject,
    mut v_inst_3807_: *mut LeanObject,
    mut v_inst_3808_: *mut LeanObject,
    mut v_inst_3809_: *mut LeanObject,
    mut v_p_3810_: *mut LeanObject,
    mut v_it_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3812_ = lean_ctor_get(v_inst_3807_, 0);
    v_toPure_3813_ = lean_ctor_get(v_toApplicative_3812_, 1);
    lean_inc(v_toPure_3813_);
    v___f_3814_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3814_, 0, v_p_3810_);
    lean_closure_set(v___f_3814_, 1, v_toPure_3813_);
    v___x_3815_ = l_Std_IterM_allM___redArg(v_inst_3807_, v_inst_3809_, v___f_3814_, v_it_3811_);
    return v___x_3815_;
}
pub unsafe fn l_Std_IterM_Partial_all___boxed(
    mut v_00_u03b1_3816_: *mut LeanObject,
    mut v_00_u03b2_3817_: *mut LeanObject,
    mut v_m_3818_: *mut LeanObject,
    mut v_inst_3819_: *mut LeanObject,
    mut v_inst_3820_: *mut LeanObject,
    mut v_inst_3821_: *mut LeanObject,
    mut v_p_3822_: *mut LeanObject,
    mut v_it_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3824_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3820_);
    return v_res_3824_;
}
pub unsafe fn l_Std_IterM_Total_all___redArg(
    mut v_inst_3825_: *mut LeanObject,
    mut v_inst_3826_: *mut LeanObject,
    mut v_p_3827_: *mut LeanObject,
    mut v_it_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3829_ = lean_ctor_get(v_inst_3825_, 0);
    v_toPure_3830_ = lean_ctor_get(v_toApplicative_3829_, 1);
    lean_inc(v_toPure_3830_);
    v___f_3831_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3831_, 0, v_p_3827_);
    lean_closure_set(v___f_3831_, 1, v_toPure_3830_);
    v___x_3832_ = l_Std_IterM_allM___redArg(v_inst_3825_, v_inst_3826_, v___f_3831_, v_it_3828_);
    return v___x_3832_;
}
pub unsafe fn l_Std_IterM_Total_all(
    mut v_00_u03b1_3833_: *mut LeanObject,
    mut v_00_u03b2_3834_: *mut LeanObject,
    mut v_m_3835_: *mut LeanObject,
    mut v_inst_3836_: *mut LeanObject,
    mut v_inst_3837_: *mut LeanObject,
    mut v_inst_3838_: *mut LeanObject,
    mut v_inst_3839_: *mut LeanObject,
    mut v_p_3840_: *mut LeanObject,
    mut v_it_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3842_ = lean_ctor_get(v_inst_3836_, 0);
    v_toPure_3843_ = lean_ctor_get(v_toApplicative_3842_, 1);
    lean_inc(v_toPure_3843_);
    v___f_3844_ = lean_alloc_closure(
        l_Std_IterM_any___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3844_, 0, v_p_3840_);
    lean_closure_set(v___f_3844_, 1, v_toPure_3843_);
    v___x_3845_ = l_Std_IterM_allM___redArg(v_inst_3836_, v_inst_3838_, v___f_3844_, v_it_3841_);
    return v___x_3845_;
}
pub unsafe fn l_Std_IterM_Total_all___boxed(
    mut v_00_u03b1_3846_: *mut LeanObject,
    mut v_00_u03b2_3847_: *mut LeanObject,
    mut v_m_3848_: *mut LeanObject,
    mut v_inst_3849_: *mut LeanObject,
    mut v_inst_3850_: *mut LeanObject,
    mut v_inst_3851_: *mut LeanObject,
    mut v_inst_3852_: *mut LeanObject,
    mut v_p_3853_: *mut LeanObject,
    mut v_it_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3855_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3850_);
    return v_res_3855_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__1(
    mut v_toPure_3856_: *mut LeanObject,
    mut v_____do__lift_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = lean_apply_2(v_toPure_3856_, lean_box(0), v_____do__lift_3857_);
    return v___x_3858_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__0(
    mut v___x_3859_: *mut LeanObject,
    mut v_toPure_3860_: *mut LeanObject,
    mut v_____do__lift_3861_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_3861_) == 0 {
        let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
        v___x_3862_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3862_, 0, v___x_3859_);
        v___x_3863_ = lean_apply_2(v_toPure_3860_, lean_box(0), v___x_3862_);
        return v___x_3863_;
    } else {
        let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3859_);
        v___x_3864_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3864_, 0, v_____do__lift_3861_);
        v___x_3865_ = lean_apply_2(v_toPure_3860_, lean_box(0), v___x_3864_);
        return v___x_3865_;
    }
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__2(
    mut v_f_3866_: *mut LeanObject,
    mut v_toBind_3867_: *mut LeanObject,
    mut v___f_3868_: *mut LeanObject,
    mut v___f_3869_: *mut LeanObject,
    mut v_x1_3870_: *mut LeanObject,
    mut v_x2_3871_: *mut LeanObject,
    mut v_x3_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    v___x_3873_ = lean_apply_1(v_f_3866_, v_x1_3870_);
    lean_inc(v_toBind_3867_);
    v___x_3874_ = lean_apply_4(
        v_toBind_3867_,
        lean_box(0),
        lean_box(0),
        v___x_3873_,
        v___f_3868_,
    );
    v___x_3875_ = lean_apply_4(
        v_toBind_3867_,
        lean_box(0),
        lean_box(0),
        v___x_3874_,
        v___f_3869_,
    );
    return v___x_3875_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(
    mut v_f_3876_: *mut LeanObject,
    mut v_toBind_3877_: *mut LeanObject,
    mut v___f_3878_: *mut LeanObject,
    mut v___f_3879_: *mut LeanObject,
    mut v_x1_3880_: *mut LeanObject,
    mut v_x2_3881_: *mut LeanObject,
    mut v_x3_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3883_: *mut LeanObject = core::ptr::null_mut();
    v_res_3883_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(
        v_f_3876_,
        v_toBind_3877_,
        v___f_3878_,
        v___f_3879_,
        v_x1_3880_,
        v_x2_3881_,
        v_x3_3882_,
    );
    lean_dec(v_x3_3882_);
    return v_res_3883_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___redArg(
    mut v_inst_3884_: *mut LeanObject,
    mut v_inst_3885_: *mut LeanObject,
    mut v_it_3886_: *mut LeanObject,
    mut v_f_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3888_ = lean_ctor_get(v_inst_3884_, 0);
    lean_inc_ref(v_toApplicative_3888_);
    v_toBind_3889_ = lean_ctor_get(v_inst_3884_, 1);
    lean_inc_n(v_toBind_3889_, 2);
    lean_dec_ref(v_inst_3884_);
    v_toPure_3890_ = lean_ctor_get(v_toApplicative_3888_, 1);
    lean_inc_n(v_toPure_3890_, 2);
    lean_dec_ref(v_toApplicative_3888_);
    v___f_3891_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3891_, 0, v_toBind_3889_);
    v___f_3892_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3892_, 0, v_toPure_3890_);
    v___x_3893_ = lean_box(0);
    v___f_3894_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3894_, 0, v___x_3893_);
    lean_closure_set(v___f_3894_, 1, v_toPure_3890_);
    v___f_3895_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3895_, 0, v_f_3887_);
    lean_closure_set(v___f_3895_, 1, v_toBind_3889_);
    lean_closure_set(v___f_3895_, 2, v___f_3894_);
    lean_closure_set(v___f_3895_, 3, v___f_3892_);
    v___x_3896_ = lean_apply_6(
        v_inst_3885_,
        v___f_3891_,
        lean_box(0),
        lean_box(0),
        v_it_3886_,
        v___x_3893_,
        v___f_3895_,
    );
    return v___x_3896_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f(
    mut v_00_u03b1_3897_: *mut LeanObject,
    mut v_00_u03b2_3898_: *mut LeanObject,
    mut v_00_u03b3_3899_: *mut LeanObject,
    mut v_m_3900_: *mut LeanObject,
    mut v_inst_3901_: *mut LeanObject,
    mut v_inst_3902_: *mut LeanObject,
    mut v_inst_3903_: *mut LeanObject,
    mut v_it_3904_: *mut LeanObject,
    mut v_f_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3906_ = lean_ctor_get(v_inst_3901_, 0);
    lean_inc_ref(v_toApplicative_3906_);
    v_toBind_3907_ = lean_ctor_get(v_inst_3901_, 1);
    lean_inc_n(v_toBind_3907_, 2);
    lean_dec_ref(v_inst_3901_);
    v_toPure_3908_ = lean_ctor_get(v_toApplicative_3906_, 1);
    lean_inc_n(v_toPure_3908_, 2);
    lean_dec_ref(v_toApplicative_3906_);
    v___f_3909_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3909_, 0, v_toBind_3907_);
    v___f_3910_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3910_, 0, v_toPure_3908_);
    v___x_3911_ = lean_box(0);
    v___f_3912_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3912_, 0, v___x_3911_);
    lean_closure_set(v___f_3912_, 1, v_toPure_3908_);
    v___f_3913_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3913_, 0, v_f_3905_);
    lean_closure_set(v___f_3913_, 1, v_toBind_3907_);
    lean_closure_set(v___f_3913_, 2, v___f_3912_);
    lean_closure_set(v___f_3913_, 3, v___f_3910_);
    v___x_3914_ = lean_apply_6(
        v_inst_3903_,
        v___f_3909_,
        lean_box(0),
        lean_box(0),
        v_it_3904_,
        v___x_3911_,
        v___f_3913_,
    );
    return v___x_3914_;
}
pub unsafe fn l_Std_IterM_findSomeM_x3f___boxed(
    mut v_00_u03b1_3915_: *mut LeanObject,
    mut v_00_u03b2_3916_: *mut LeanObject,
    mut v_00_u03b3_3917_: *mut LeanObject,
    mut v_m_3918_: *mut LeanObject,
    mut v_inst_3919_: *mut LeanObject,
    mut v_inst_3920_: *mut LeanObject,
    mut v_inst_3921_: *mut LeanObject,
    mut v_it_3922_: *mut LeanObject,
    mut v_f_3923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3924_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3920_);
    return v_res_3924_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f___redArg(
    mut v_inst_3925_: *mut LeanObject,
    mut v_inst_3926_: *mut LeanObject,
    mut v_it_3927_: *mut LeanObject,
    mut v_f_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3929_ = lean_ctor_get(v_inst_3925_, 0);
    lean_inc_ref(v_toApplicative_3929_);
    v_toBind_3930_ = lean_ctor_get(v_inst_3925_, 1);
    lean_inc_n(v_toBind_3930_, 2);
    lean_dec_ref(v_inst_3925_);
    v_toPure_3931_ = lean_ctor_get(v_toApplicative_3929_, 1);
    lean_inc_n(v_toPure_3931_, 2);
    lean_dec_ref(v_toApplicative_3929_);
    v___f_3932_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3932_, 0, v_toBind_3930_);
    v___f_3933_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3933_, 0, v_toPure_3931_);
    v___x_3934_ = lean_box(0);
    v___f_3935_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3935_, 0, v___x_3934_);
    lean_closure_set(v___f_3935_, 1, v_toPure_3931_);
    v___f_3936_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3936_, 0, v_f_3928_);
    lean_closure_set(v___f_3936_, 1, v_toBind_3930_);
    lean_closure_set(v___f_3936_, 2, v___f_3935_);
    lean_closure_set(v___f_3936_, 3, v___f_3933_);
    v___x_3937_ = lean_apply_6(
        v_inst_3926_,
        v___f_3932_,
        lean_box(0),
        lean_box(0),
        v_it_3927_,
        v___x_3934_,
        v___f_3936_,
    );
    return v___x_3937_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f(
    mut v_00_u03b1_3938_: *mut LeanObject,
    mut v_00_u03b2_3939_: *mut LeanObject,
    mut v_00_u03b3_3940_: *mut LeanObject,
    mut v_m_3941_: *mut LeanObject,
    mut v_inst_3942_: *mut LeanObject,
    mut v_inst_3943_: *mut LeanObject,
    mut v_inst_3944_: *mut LeanObject,
    mut v_it_3945_: *mut LeanObject,
    mut v_f_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3947_ = lean_ctor_get(v_inst_3942_, 0);
    lean_inc_ref(v_toApplicative_3947_);
    v_toBind_3948_ = lean_ctor_get(v_inst_3942_, 1);
    lean_inc_n(v_toBind_3948_, 2);
    lean_dec_ref(v_inst_3942_);
    v_toPure_3949_ = lean_ctor_get(v_toApplicative_3947_, 1);
    lean_inc_n(v_toPure_3949_, 2);
    lean_dec_ref(v_toApplicative_3947_);
    v___f_3950_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3950_, 0, v_toBind_3948_);
    v___f_3951_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3951_, 0, v_toPure_3949_);
    v___x_3952_ = lean_box(0);
    v___f_3953_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3953_, 0, v___x_3952_);
    lean_closure_set(v___f_3953_, 1, v_toPure_3949_);
    v___f_3954_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3954_, 0, v_f_3946_);
    lean_closure_set(v___f_3954_, 1, v_toBind_3948_);
    lean_closure_set(v___f_3954_, 2, v___f_3953_);
    lean_closure_set(v___f_3954_, 3, v___f_3951_);
    v___x_3955_ = lean_apply_6(
        v_inst_3944_,
        v___f_3950_,
        lean_box(0),
        lean_box(0),
        v_it_3945_,
        v___x_3952_,
        v___f_3954_,
    );
    return v___x_3955_;
}
pub unsafe fn l_Std_IterM_Partial_findSomeM_x3f___boxed(
    mut v_00_u03b1_3956_: *mut LeanObject,
    mut v_00_u03b2_3957_: *mut LeanObject,
    mut v_00_u03b3_3958_: *mut LeanObject,
    mut v_m_3959_: *mut LeanObject,
    mut v_inst_3960_: *mut LeanObject,
    mut v_inst_3961_: *mut LeanObject,
    mut v_inst_3962_: *mut LeanObject,
    mut v_it_3963_: *mut LeanObject,
    mut v_f_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3965_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3961_);
    return v_res_3965_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f___redArg(
    mut v_inst_3966_: *mut LeanObject,
    mut v_inst_3967_: *mut LeanObject,
    mut v_it_3968_: *mut LeanObject,
    mut v_f_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3970_ = lean_ctor_get(v_inst_3966_, 0);
    lean_inc_ref(v_toApplicative_3970_);
    v_toBind_3971_ = lean_ctor_get(v_inst_3966_, 1);
    lean_inc_n(v_toBind_3971_, 2);
    lean_dec_ref(v_inst_3966_);
    v_toPure_3972_ = lean_ctor_get(v_toApplicative_3970_, 1);
    lean_inc_n(v_toPure_3972_, 2);
    lean_dec_ref(v_toApplicative_3970_);
    v___f_3973_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3973_, 0, v_toBind_3971_);
    v___f_3974_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3974_, 0, v_toPure_3972_);
    v___x_3975_ = lean_box(0);
    v___f_3976_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3976_, 0, v___x_3975_);
    lean_closure_set(v___f_3976_, 1, v_toPure_3972_);
    v___f_3977_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3977_, 0, v_f_3969_);
    lean_closure_set(v___f_3977_, 1, v_toBind_3971_);
    lean_closure_set(v___f_3977_, 2, v___f_3976_);
    lean_closure_set(v___f_3977_, 3, v___f_3974_);
    v___x_3978_ = lean_apply_6(
        v_inst_3967_,
        v___f_3973_,
        lean_box(0),
        lean_box(0),
        v_it_3968_,
        v___x_3975_,
        v___f_3977_,
    );
    return v___x_3978_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f(
    mut v_00_u03b1_3979_: *mut LeanObject,
    mut v_00_u03b2_3980_: *mut LeanObject,
    mut v_00_u03b3_3981_: *mut LeanObject,
    mut v_m_3982_: *mut LeanObject,
    mut v_inst_3983_: *mut LeanObject,
    mut v_inst_3984_: *mut LeanObject,
    mut v_inst_3985_: *mut LeanObject,
    mut v_inst_3986_: *mut LeanObject,
    mut v_it_3987_: *mut LeanObject,
    mut v_f_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3989_ = lean_ctor_get(v_inst_3983_, 0);
    lean_inc_ref(v_toApplicative_3989_);
    v_toBind_3990_ = lean_ctor_get(v_inst_3983_, 1);
    lean_inc_n(v_toBind_3990_, 2);
    lean_dec_ref(v_inst_3983_);
    v_toPure_3991_ = lean_ctor_get(v_toApplicative_3989_, 1);
    lean_inc_n(v_toPure_3991_, 2);
    lean_dec_ref(v_toApplicative_3989_);
    v___f_3992_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3992_, 0, v_toBind_3990_);
    v___f_3993_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3993_, 0, v_toPure_3991_);
    v___x_3994_ = lean_box(0);
    v___f_3995_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3995_, 0, v___x_3994_);
    lean_closure_set(v___f_3995_, 1, v_toPure_3991_);
    v___f_3996_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_3996_, 0, v_f_3988_);
    lean_closure_set(v___f_3996_, 1, v_toBind_3990_);
    lean_closure_set(v___f_3996_, 2, v___f_3995_);
    lean_closure_set(v___f_3996_, 3, v___f_3993_);
    v___x_3997_ = lean_apply_6(
        v_inst_3985_,
        v___f_3992_,
        lean_box(0),
        lean_box(0),
        v_it_3987_,
        v___x_3994_,
        v___f_3996_,
    );
    return v___x_3997_;
}
pub unsafe fn l_Std_IterM_Total_findSomeM_x3f___boxed(
    mut v_00_u03b1_3998_: *mut LeanObject,
    mut v_00_u03b2_3999_: *mut LeanObject,
    mut v_00_u03b3_4000_: *mut LeanObject,
    mut v_m_4001_: *mut LeanObject,
    mut v_inst_4002_: *mut LeanObject,
    mut v_inst_4003_: *mut LeanObject,
    mut v_inst_4004_: *mut LeanObject,
    mut v_inst_4005_: *mut LeanObject,
    mut v_it_4006_: *mut LeanObject,
    mut v_f_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4008_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4003_);
    return v_res_4008_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg___lam__3(
    mut v_f_4009_: *mut LeanObject,
    mut v_toPure_4010_: *mut LeanObject,
    mut v_toBind_4011_: *mut LeanObject,
    mut v___f_4012_: *mut LeanObject,
    mut v___f_4013_: *mut LeanObject,
    mut v_x1_4014_: *mut LeanObject,
    mut v_x2_4015_: *mut LeanObject,
    mut v_x3_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = lean_apply_1(v_f_4009_, v_x1_4014_);
    v___x_4018_ = lean_apply_2(v_toPure_4010_, lean_box(0), v___x_4017_);
    lean_inc(v_toBind_4011_);
    v___x_4019_ = lean_apply_4(
        v_toBind_4011_,
        lean_box(0),
        lean_box(0),
        v___x_4018_,
        v___f_4012_,
    );
    v___x_4020_ = lean_apply_4(
        v_toBind_4011_,
        lean_box(0),
        lean_box(0),
        v___x_4019_,
        v___f_4013_,
    );
    return v___x_4020_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(
    mut v_f_4021_: *mut LeanObject,
    mut v_toPure_4022_: *mut LeanObject,
    mut v_toBind_4023_: *mut LeanObject,
    mut v___f_4024_: *mut LeanObject,
    mut v___f_4025_: *mut LeanObject,
    mut v_x1_4026_: *mut LeanObject,
    mut v_x2_4027_: *mut LeanObject,
    mut v_x3_4028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4029_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x3_4028_);
    return v_res_4029_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___redArg(
    mut v_inst_4030_: *mut LeanObject,
    mut v_inst_4031_: *mut LeanObject,
    mut v_it_4032_: *mut LeanObject,
    mut v_f_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4034_ = lean_ctor_get(v_inst_4030_, 0);
    lean_inc_ref(v_toApplicative_4034_);
    v_toBind_4035_ = lean_ctor_get(v_inst_4030_, 1);
    lean_inc_n(v_toBind_4035_, 2);
    lean_dec_ref(v_inst_4030_);
    v_toPure_4036_ = lean_ctor_get(v_toApplicative_4034_, 1);
    lean_inc_n(v_toPure_4036_, 3);
    lean_dec_ref(v_toApplicative_4034_);
    v___f_4037_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4037_, 0, v_toBind_4035_);
    v___f_4038_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4038_, 0, v_toPure_4036_);
    v___x_4039_ = lean_box(0);
    v___f_4040_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4040_, 0, v___x_4039_);
    lean_closure_set(v___f_4040_, 1, v_toPure_4036_);
    v___f_4041_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4041_, 0, v_f_4033_);
    lean_closure_set(v___f_4041_, 1, v_toPure_4036_);
    lean_closure_set(v___f_4041_, 2, v_toBind_4035_);
    lean_closure_set(v___f_4041_, 3, v___f_4040_);
    lean_closure_set(v___f_4041_, 4, v___f_4038_);
    v___x_4042_ = lean_apply_6(
        v_inst_4031_,
        v___f_4037_,
        lean_box(0),
        lean_box(0),
        v_it_4032_,
        v___x_4039_,
        v___f_4041_,
    );
    return v___x_4042_;
}
pub unsafe fn l_Std_IterM_findSome_x3f(
    mut v_00_u03b1_4043_: *mut LeanObject,
    mut v_00_u03b2_4044_: *mut LeanObject,
    mut v_00_u03b3_4045_: *mut LeanObject,
    mut v_m_4046_: *mut LeanObject,
    mut v_inst_4047_: *mut LeanObject,
    mut v_inst_4048_: *mut LeanObject,
    mut v_inst_4049_: *mut LeanObject,
    mut v_it_4050_: *mut LeanObject,
    mut v_f_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4052_ = lean_ctor_get(v_inst_4047_, 0);
    lean_inc_ref(v_toApplicative_4052_);
    v_toBind_4053_ = lean_ctor_get(v_inst_4047_, 1);
    lean_inc_n(v_toBind_4053_, 2);
    lean_dec_ref(v_inst_4047_);
    v_toPure_4054_ = lean_ctor_get(v_toApplicative_4052_, 1);
    lean_inc_n(v_toPure_4054_, 3);
    lean_dec_ref(v_toApplicative_4052_);
    v___f_4055_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4055_, 0, v_toBind_4053_);
    v___f_4056_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4056_, 0, v_toPure_4054_);
    v___x_4057_ = lean_box(0);
    v___f_4058_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4058_, 0, v___x_4057_);
    lean_closure_set(v___f_4058_, 1, v_toPure_4054_);
    v___f_4059_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4059_, 0, v_f_4051_);
    lean_closure_set(v___f_4059_, 1, v_toPure_4054_);
    lean_closure_set(v___f_4059_, 2, v_toBind_4053_);
    lean_closure_set(v___f_4059_, 3, v___f_4058_);
    lean_closure_set(v___f_4059_, 4, v___f_4056_);
    v___x_4060_ = lean_apply_6(
        v_inst_4049_,
        v___f_4055_,
        lean_box(0),
        lean_box(0),
        v_it_4050_,
        v___x_4057_,
        v___f_4059_,
    );
    return v___x_4060_;
}
pub unsafe fn l_Std_IterM_findSome_x3f___boxed(
    mut v_00_u03b1_4061_: *mut LeanObject,
    mut v_00_u03b2_4062_: *mut LeanObject,
    mut v_00_u03b3_4063_: *mut LeanObject,
    mut v_m_4064_: *mut LeanObject,
    mut v_inst_4065_: *mut LeanObject,
    mut v_inst_4066_: *mut LeanObject,
    mut v_inst_4067_: *mut LeanObject,
    mut v_it_4068_: *mut LeanObject,
    mut v_f_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4070_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4066_);
    return v_res_4070_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f___redArg(
    mut v_inst_4071_: *mut LeanObject,
    mut v_inst_4072_: *mut LeanObject,
    mut v_it_4073_: *mut LeanObject,
    mut v_f_4074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4075_ = lean_ctor_get(v_inst_4071_, 0);
    lean_inc_ref(v_toApplicative_4075_);
    v_toBind_4076_ = lean_ctor_get(v_inst_4071_, 1);
    lean_inc_n(v_toBind_4076_, 2);
    lean_dec_ref(v_inst_4071_);
    v_toPure_4077_ = lean_ctor_get(v_toApplicative_4075_, 1);
    lean_inc_n(v_toPure_4077_, 3);
    lean_dec_ref(v_toApplicative_4075_);
    v___f_4078_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4078_, 0, v_toBind_4076_);
    v___f_4079_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4079_, 0, v_toPure_4077_);
    v___x_4080_ = lean_box(0);
    v___f_4081_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4081_, 0, v___x_4080_);
    lean_closure_set(v___f_4081_, 1, v_toPure_4077_);
    v___f_4082_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4082_, 0, v_f_4074_);
    lean_closure_set(v___f_4082_, 1, v_toPure_4077_);
    lean_closure_set(v___f_4082_, 2, v_toBind_4076_);
    lean_closure_set(v___f_4082_, 3, v___f_4081_);
    lean_closure_set(v___f_4082_, 4, v___f_4079_);
    v___x_4083_ = lean_apply_6(
        v_inst_4072_,
        v___f_4078_,
        lean_box(0),
        lean_box(0),
        v_it_4073_,
        v___x_4080_,
        v___f_4082_,
    );
    return v___x_4083_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f(
    mut v_00_u03b1_4084_: *mut LeanObject,
    mut v_00_u03b2_4085_: *mut LeanObject,
    mut v_00_u03b3_4086_: *mut LeanObject,
    mut v_m_4087_: *mut LeanObject,
    mut v_inst_4088_: *mut LeanObject,
    mut v_inst_4089_: *mut LeanObject,
    mut v_inst_4090_: *mut LeanObject,
    mut v_it_4091_: *mut LeanObject,
    mut v_f_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4093_ = lean_ctor_get(v_inst_4088_, 0);
    lean_inc_ref(v_toApplicative_4093_);
    v_toBind_4094_ = lean_ctor_get(v_inst_4088_, 1);
    lean_inc_n(v_toBind_4094_, 2);
    lean_dec_ref(v_inst_4088_);
    v_toPure_4095_ = lean_ctor_get(v_toApplicative_4093_, 1);
    lean_inc_n(v_toPure_4095_, 3);
    lean_dec_ref(v_toApplicative_4093_);
    v___f_4096_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4096_, 0, v_toBind_4094_);
    v___f_4097_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4097_, 0, v_toPure_4095_);
    v___x_4098_ = lean_box(0);
    v___f_4099_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4099_, 0, v___x_4098_);
    lean_closure_set(v___f_4099_, 1, v_toPure_4095_);
    v___f_4100_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4100_, 0, v_f_4092_);
    lean_closure_set(v___f_4100_, 1, v_toPure_4095_);
    lean_closure_set(v___f_4100_, 2, v_toBind_4094_);
    lean_closure_set(v___f_4100_, 3, v___f_4099_);
    lean_closure_set(v___f_4100_, 4, v___f_4097_);
    v___x_4101_ = lean_apply_6(
        v_inst_4090_,
        v___f_4096_,
        lean_box(0),
        lean_box(0),
        v_it_4091_,
        v___x_4098_,
        v___f_4100_,
    );
    return v___x_4101_;
}
pub unsafe fn l_Std_IterM_Partial_findSome_x3f___boxed(
    mut v_00_u03b1_4102_: *mut LeanObject,
    mut v_00_u03b2_4103_: *mut LeanObject,
    mut v_00_u03b3_4104_: *mut LeanObject,
    mut v_m_4105_: *mut LeanObject,
    mut v_inst_4106_: *mut LeanObject,
    mut v_inst_4107_: *mut LeanObject,
    mut v_inst_4108_: *mut LeanObject,
    mut v_it_4109_: *mut LeanObject,
    mut v_f_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4111_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4107_);
    return v_res_4111_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f___redArg(
    mut v_inst_4112_: *mut LeanObject,
    mut v_inst_4113_: *mut LeanObject,
    mut v_it_4114_: *mut LeanObject,
    mut v_f_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4116_ = lean_ctor_get(v_inst_4112_, 0);
    lean_inc_ref(v_toApplicative_4116_);
    v_toBind_4117_ = lean_ctor_get(v_inst_4112_, 1);
    lean_inc_n(v_toBind_4117_, 2);
    lean_dec_ref(v_inst_4112_);
    v_toPure_4118_ = lean_ctor_get(v_toApplicative_4116_, 1);
    lean_inc_n(v_toPure_4118_, 3);
    lean_dec_ref(v_toApplicative_4116_);
    v___f_4119_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4119_, 0, v_toBind_4117_);
    v___f_4120_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4120_, 0, v_toPure_4118_);
    v___x_4121_ = lean_box(0);
    v___f_4122_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4122_, 0, v___x_4121_);
    lean_closure_set(v___f_4122_, 1, v_toPure_4118_);
    v___f_4123_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4123_, 0, v_f_4115_);
    lean_closure_set(v___f_4123_, 1, v_toPure_4118_);
    lean_closure_set(v___f_4123_, 2, v_toBind_4117_);
    lean_closure_set(v___f_4123_, 3, v___f_4122_);
    lean_closure_set(v___f_4123_, 4, v___f_4120_);
    v___x_4124_ = lean_apply_6(
        v_inst_4113_,
        v___f_4119_,
        lean_box(0),
        lean_box(0),
        v_it_4114_,
        v___x_4121_,
        v___f_4123_,
    );
    return v___x_4124_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f(
    mut v_00_u03b1_4125_: *mut LeanObject,
    mut v_00_u03b2_4126_: *mut LeanObject,
    mut v_00_u03b3_4127_: *mut LeanObject,
    mut v_m_4128_: *mut LeanObject,
    mut v_inst_4129_: *mut LeanObject,
    mut v_inst_4130_: *mut LeanObject,
    mut v_inst_4131_: *mut LeanObject,
    mut v_inst_4132_: *mut LeanObject,
    mut v_it_4133_: *mut LeanObject,
    mut v_f_4134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4135_ = lean_ctor_get(v_inst_4129_, 0);
    lean_inc_ref(v_toApplicative_4135_);
    v_toBind_4136_ = lean_ctor_get(v_inst_4129_, 1);
    lean_inc_n(v_toBind_4136_, 2);
    lean_dec_ref(v_inst_4129_);
    v_toPure_4137_ = lean_ctor_get(v_toApplicative_4135_, 1);
    lean_inc_n(v_toPure_4137_, 3);
    lean_dec_ref(v_toApplicative_4135_);
    v___f_4138_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4138_, 0, v_toBind_4136_);
    v___f_4139_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4139_, 0, v_toPure_4137_);
    v___x_4140_ = lean_box(0);
    v___f_4141_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4141_, 0, v___x_4140_);
    lean_closure_set(v___f_4141_, 1, v_toPure_4137_);
    v___f_4142_ = lean_alloc_closure(
        l_Std_IterM_findSome_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_4142_, 0, v_f_4134_);
    lean_closure_set(v___f_4142_, 1, v_toPure_4137_);
    lean_closure_set(v___f_4142_, 2, v_toBind_4136_);
    lean_closure_set(v___f_4142_, 3, v___f_4141_);
    lean_closure_set(v___f_4142_, 4, v___f_4139_);
    v___x_4143_ = lean_apply_6(
        v_inst_4131_,
        v___f_4138_,
        lean_box(0),
        lean_box(0),
        v_it_4133_,
        v___x_4140_,
        v___f_4142_,
    );
    return v___x_4143_;
}
pub unsafe fn l_Std_IterM_Total_findSome_x3f___boxed(
    mut v_00_u03b1_4144_: *mut LeanObject,
    mut v_00_u03b2_4145_: *mut LeanObject,
    mut v_00_u03b3_4146_: *mut LeanObject,
    mut v_m_4147_: *mut LeanObject,
    mut v_inst_4148_: *mut LeanObject,
    mut v_inst_4149_: *mut LeanObject,
    mut v_inst_4150_: *mut LeanObject,
    mut v_inst_4151_: *mut LeanObject,
    mut v_it_4152_: *mut LeanObject,
    mut v_f_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4154_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4149_);
    return v_res_4154_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__3(
    mut v_toPure_4155_: *mut LeanObject,
    mut v___x_4156_: *mut LeanObject,
    mut v_x1_4157_: *mut LeanObject,
    mut v_____do__lift_4158_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4158_ == 0 {
        let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x1_4157_);
        v___x_4159_ = lean_apply_2(v_toPure_4155_, lean_box(0), v___x_4156_);
        return v___x_4159_;
    } else {
        let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_4156_);
        v___x_4160_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4160_, 0, v_x1_4157_);
        v___x_4161_ = lean_apply_2(v_toPure_4155_, lean_box(0), v___x_4160_);
        return v___x_4161_;
    }
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__3___boxed(
    mut v_toPure_4162_: *mut LeanObject,
    mut v___x_4163_: *mut LeanObject,
    mut v_x1_4164_: *mut LeanObject,
    mut v_____do__lift_4165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_191__boxed_4166_: u8 = 0;
    let mut v_res_4167_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_4166_ = (lean_unbox(v_____do__lift_4165_) as u8);
    v_res_4167_ = l_Std_IterM_findM_x3f___redArg___lam__3(
        v_toPure_4162_,
        v___x_4163_,
        v_x1_4164_,
        v_____do__lift_191__boxed_4166_,
    );
    return v_res_4167_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__0(
    mut v_toPure_4168_: *mut LeanObject,
    mut v___x_4169_: *mut LeanObject,
    mut v_f_4170_: *mut LeanObject,
    mut v_toBind_4171_: *mut LeanObject,
    mut v___f_4172_: *mut LeanObject,
    mut v___f_4173_: *mut LeanObject,
    mut v_x1_4174_: *mut LeanObject,
    mut v_x2_4175_: *mut LeanObject,
    mut v_x3_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_x1_4174_);
    v___f_4177_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4177_, 0, v_toPure_4168_);
    lean_closure_set(v___f_4177_, 1, v___x_4169_);
    lean_closure_set(v___f_4177_, 2, v_x1_4174_);
    v___x_4178_ = lean_apply_1(v_f_4170_, v_x1_4174_);
    lean_inc_n(v_toBind_4171_, 2);
    v___x_4179_ = lean_apply_4(
        v_toBind_4171_,
        lean_box(0),
        lean_box(0),
        v___x_4178_,
        v___f_4177_,
    );
    v___x_4180_ = lean_apply_4(
        v_toBind_4171_,
        lean_box(0),
        lean_box(0),
        v___x_4179_,
        v___f_4172_,
    );
    v___x_4181_ = lean_apply_4(
        v_toBind_4171_,
        lean_box(0),
        lean_box(0),
        v___x_4180_,
        v___f_4173_,
    );
    return v___x_4181_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg___lam__0___boxed(
    mut v_toPure_4182_: *mut LeanObject,
    mut v___x_4183_: *mut LeanObject,
    mut v_f_4184_: *mut LeanObject,
    mut v_toBind_4185_: *mut LeanObject,
    mut v___f_4186_: *mut LeanObject,
    mut v___f_4187_: *mut LeanObject,
    mut v_x1_4188_: *mut LeanObject,
    mut v_x2_4189_: *mut LeanObject,
    mut v_x3_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4191_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x3_4190_);
    return v_res_4191_;
}
pub unsafe fn l_Std_IterM_findM_x3f___redArg(
    mut v_inst_4192_: *mut LeanObject,
    mut v_inst_4193_: *mut LeanObject,
    mut v_it_4194_: *mut LeanObject,
    mut v_f_4195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4196_ = lean_ctor_get(v_inst_4192_, 0);
    lean_inc_ref(v_toApplicative_4196_);
    v_toBind_4197_ = lean_ctor_get(v_inst_4192_, 1);
    lean_inc_n(v_toBind_4197_, 2);
    lean_dec_ref(v_inst_4192_);
    v_toPure_4198_ = lean_ctor_get(v_toApplicative_4196_, 1);
    lean_inc_n(v_toPure_4198_, 3);
    lean_dec_ref(v_toApplicative_4196_);
    v___f_4199_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4199_, 0, v_toBind_4197_);
    v___f_4200_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4200_, 0, v_toPure_4198_);
    v___x_4201_ = lean_box(0);
    v___f_4202_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4202_, 0, v___x_4201_);
    lean_closure_set(v___f_4202_, 1, v_toPure_4198_);
    v___f_4203_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4203_, 0, v_toPure_4198_);
    lean_closure_set(v___f_4203_, 1, v___x_4201_);
    lean_closure_set(v___f_4203_, 2, v_f_4195_);
    lean_closure_set(v___f_4203_, 3, v_toBind_4197_);
    lean_closure_set(v___f_4203_, 4, v___f_4202_);
    lean_closure_set(v___f_4203_, 5, v___f_4200_);
    v___x_4204_ = lean_apply_6(
        v_inst_4193_,
        v___f_4199_,
        lean_box(0),
        lean_box(0),
        v_it_4194_,
        v___x_4201_,
        v___f_4203_,
    );
    return v___x_4204_;
}
pub unsafe fn l_Std_IterM_findM_x3f(
    mut v_00_u03b1_4205_: *mut LeanObject,
    mut v_00_u03b2_4206_: *mut LeanObject,
    mut v_m_4207_: *mut LeanObject,
    mut v_inst_4208_: *mut LeanObject,
    mut v_inst_4209_: *mut LeanObject,
    mut v_inst_4210_: *mut LeanObject,
    mut v_it_4211_: *mut LeanObject,
    mut v_f_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4213_ = lean_ctor_get(v_inst_4208_, 0);
    lean_inc_ref(v_toApplicative_4213_);
    v_toBind_4214_ = lean_ctor_get(v_inst_4208_, 1);
    lean_inc_n(v_toBind_4214_, 2);
    lean_dec_ref(v_inst_4208_);
    v_toPure_4215_ = lean_ctor_get(v_toApplicative_4213_, 1);
    lean_inc_n(v_toPure_4215_, 3);
    lean_dec_ref(v_toApplicative_4213_);
    v___f_4216_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4216_, 0, v_toBind_4214_);
    v___f_4217_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4217_, 0, v_toPure_4215_);
    v___x_4218_ = lean_box(0);
    v___f_4219_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4219_, 0, v___x_4218_);
    lean_closure_set(v___f_4219_, 1, v_toPure_4215_);
    v___f_4220_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4220_, 0, v_toPure_4215_);
    lean_closure_set(v___f_4220_, 1, v___x_4218_);
    lean_closure_set(v___f_4220_, 2, v_f_4212_);
    lean_closure_set(v___f_4220_, 3, v_toBind_4214_);
    lean_closure_set(v___f_4220_, 4, v___f_4219_);
    lean_closure_set(v___f_4220_, 5, v___f_4217_);
    v___x_4221_ = lean_apply_6(
        v_inst_4210_,
        v___f_4216_,
        lean_box(0),
        lean_box(0),
        v_it_4211_,
        v___x_4218_,
        v___f_4220_,
    );
    return v___x_4221_;
}
pub unsafe fn l_Std_IterM_findM_x3f___boxed(
    mut v_00_u03b1_4222_: *mut LeanObject,
    mut v_00_u03b2_4223_: *mut LeanObject,
    mut v_m_4224_: *mut LeanObject,
    mut v_inst_4225_: *mut LeanObject,
    mut v_inst_4226_: *mut LeanObject,
    mut v_inst_4227_: *mut LeanObject,
    mut v_it_4228_: *mut LeanObject,
    mut v_f_4229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4230_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4226_);
    return v_res_4230_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f___redArg(
    mut v_inst_4231_: *mut LeanObject,
    mut v_inst_4232_: *mut LeanObject,
    mut v_it_4233_: *mut LeanObject,
    mut v_f_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4235_ = lean_ctor_get(v_inst_4231_, 0);
    lean_inc_ref(v_toApplicative_4235_);
    v_toBind_4236_ = lean_ctor_get(v_inst_4231_, 1);
    lean_inc_n(v_toBind_4236_, 2);
    lean_dec_ref(v_inst_4231_);
    v_toPure_4237_ = lean_ctor_get(v_toApplicative_4235_, 1);
    lean_inc_n(v_toPure_4237_, 3);
    lean_dec_ref(v_toApplicative_4235_);
    v___f_4238_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4238_, 0, v_toBind_4236_);
    v___f_4239_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4239_, 0, v_toPure_4237_);
    v___x_4240_ = lean_box(0);
    v___f_4241_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4241_, 0, v___x_4240_);
    lean_closure_set(v___f_4241_, 1, v_toPure_4237_);
    v___f_4242_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4242_, 0, v_toPure_4237_);
    lean_closure_set(v___f_4242_, 1, v___x_4240_);
    lean_closure_set(v___f_4242_, 2, v_f_4234_);
    lean_closure_set(v___f_4242_, 3, v_toBind_4236_);
    lean_closure_set(v___f_4242_, 4, v___f_4241_);
    lean_closure_set(v___f_4242_, 5, v___f_4239_);
    v___x_4243_ = lean_apply_6(
        v_inst_4232_,
        v___f_4238_,
        lean_box(0),
        lean_box(0),
        v_it_4233_,
        v___x_4240_,
        v___f_4242_,
    );
    return v___x_4243_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f(
    mut v_00_u03b1_4244_: *mut LeanObject,
    mut v_00_u03b2_4245_: *mut LeanObject,
    mut v_m_4246_: *mut LeanObject,
    mut v_inst_4247_: *mut LeanObject,
    mut v_inst_4248_: *mut LeanObject,
    mut v_inst_4249_: *mut LeanObject,
    mut v_it_4250_: *mut LeanObject,
    mut v_f_4251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4252_ = lean_ctor_get(v_inst_4247_, 0);
    lean_inc_ref(v_toApplicative_4252_);
    v_toBind_4253_ = lean_ctor_get(v_inst_4247_, 1);
    lean_inc_n(v_toBind_4253_, 2);
    lean_dec_ref(v_inst_4247_);
    v_toPure_4254_ = lean_ctor_get(v_toApplicative_4252_, 1);
    lean_inc_n(v_toPure_4254_, 3);
    lean_dec_ref(v_toApplicative_4252_);
    v___f_4255_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4255_, 0, v_toBind_4253_);
    v___f_4256_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4256_, 0, v_toPure_4254_);
    v___x_4257_ = lean_box(0);
    v___f_4258_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4258_, 0, v___x_4257_);
    lean_closure_set(v___f_4258_, 1, v_toPure_4254_);
    v___f_4259_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4259_, 0, v_toPure_4254_);
    lean_closure_set(v___f_4259_, 1, v___x_4257_);
    lean_closure_set(v___f_4259_, 2, v_f_4251_);
    lean_closure_set(v___f_4259_, 3, v_toBind_4253_);
    lean_closure_set(v___f_4259_, 4, v___f_4258_);
    lean_closure_set(v___f_4259_, 5, v___f_4256_);
    v___x_4260_ = lean_apply_6(
        v_inst_4249_,
        v___f_4255_,
        lean_box(0),
        lean_box(0),
        v_it_4250_,
        v___x_4257_,
        v___f_4259_,
    );
    return v___x_4260_;
}
pub unsafe fn l_Std_IterM_Partial_findM_x3f___boxed(
    mut v_00_u03b1_4261_: *mut LeanObject,
    mut v_00_u03b2_4262_: *mut LeanObject,
    mut v_m_4263_: *mut LeanObject,
    mut v_inst_4264_: *mut LeanObject,
    mut v_inst_4265_: *mut LeanObject,
    mut v_inst_4266_: *mut LeanObject,
    mut v_it_4267_: *mut LeanObject,
    mut v_f_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4269_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4265_);
    return v_res_4269_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f___redArg(
    mut v_inst_4270_: *mut LeanObject,
    mut v_inst_4271_: *mut LeanObject,
    mut v_it_4272_: *mut LeanObject,
    mut v_f_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4274_ = lean_ctor_get(v_inst_4270_, 0);
    lean_inc_ref(v_toApplicative_4274_);
    v_toBind_4275_ = lean_ctor_get(v_inst_4270_, 1);
    lean_inc_n(v_toBind_4275_, 2);
    lean_dec_ref(v_inst_4270_);
    v_toPure_4276_ = lean_ctor_get(v_toApplicative_4274_, 1);
    lean_inc_n(v_toPure_4276_, 3);
    lean_dec_ref(v_toApplicative_4274_);
    v___f_4277_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4277_, 0, v_toBind_4275_);
    v___f_4278_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4278_, 0, v_toPure_4276_);
    v___x_4279_ = lean_box(0);
    v___f_4280_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4280_, 0, v___x_4279_);
    lean_closure_set(v___f_4280_, 1, v_toPure_4276_);
    v___f_4281_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4281_, 0, v_toPure_4276_);
    lean_closure_set(v___f_4281_, 1, v___x_4279_);
    lean_closure_set(v___f_4281_, 2, v_f_4273_);
    lean_closure_set(v___f_4281_, 3, v_toBind_4275_);
    lean_closure_set(v___f_4281_, 4, v___f_4280_);
    lean_closure_set(v___f_4281_, 5, v___f_4278_);
    v___x_4282_ = lean_apply_6(
        v_inst_4271_,
        v___f_4277_,
        lean_box(0),
        lean_box(0),
        v_it_4272_,
        v___x_4279_,
        v___f_4281_,
    );
    return v___x_4282_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f(
    mut v_00_u03b1_4283_: *mut LeanObject,
    mut v_00_u03b2_4284_: *mut LeanObject,
    mut v_m_4285_: *mut LeanObject,
    mut v_inst_4286_: *mut LeanObject,
    mut v_inst_4287_: *mut LeanObject,
    mut v_inst_4288_: *mut LeanObject,
    mut v_inst_4289_: *mut LeanObject,
    mut v_it_4290_: *mut LeanObject,
    mut v_f_4291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4292_ = lean_ctor_get(v_inst_4286_, 0);
    lean_inc_ref(v_toApplicative_4292_);
    v_toBind_4293_ = lean_ctor_get(v_inst_4286_, 1);
    lean_inc_n(v_toBind_4293_, 2);
    lean_dec_ref(v_inst_4286_);
    v_toPure_4294_ = lean_ctor_get(v_toApplicative_4292_, 1);
    lean_inc_n(v_toPure_4294_, 3);
    lean_dec_ref(v_toApplicative_4292_);
    v___f_4295_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4295_, 0, v_toBind_4293_);
    v___f_4296_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4296_, 0, v_toPure_4294_);
    v___x_4297_ = lean_box(0);
    v___f_4298_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4298_, 0, v___x_4297_);
    lean_closure_set(v___f_4298_, 1, v_toPure_4294_);
    v___f_4299_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4299_, 0, v_toPure_4294_);
    lean_closure_set(v___f_4299_, 1, v___x_4297_);
    lean_closure_set(v___f_4299_, 2, v_f_4291_);
    lean_closure_set(v___f_4299_, 3, v_toBind_4293_);
    lean_closure_set(v___f_4299_, 4, v___f_4298_);
    lean_closure_set(v___f_4299_, 5, v___f_4296_);
    v___x_4300_ = lean_apply_6(
        v_inst_4288_,
        v___f_4295_,
        lean_box(0),
        lean_box(0),
        v_it_4290_,
        v___x_4297_,
        v___f_4299_,
    );
    return v___x_4300_;
}
pub unsafe fn l_Std_IterM_Total_findM_x3f___boxed(
    mut v_00_u03b1_4301_: *mut LeanObject,
    mut v_00_u03b2_4302_: *mut LeanObject,
    mut v_m_4303_: *mut LeanObject,
    mut v_inst_4304_: *mut LeanObject,
    mut v_inst_4305_: *mut LeanObject,
    mut v_inst_4306_: *mut LeanObject,
    mut v_inst_4307_: *mut LeanObject,
    mut v_it_4308_: *mut LeanObject,
    mut v_f_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4310_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4305_);
    return v_res_4310_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg___lam__4(
    mut v_toPure_4311_: *mut LeanObject,
    mut v___x_4312_: *mut LeanObject,
    mut v_f_4313_: *mut LeanObject,
    mut v_toBind_4314_: *mut LeanObject,
    mut v___f_4315_: *mut LeanObject,
    mut v___f_4316_: *mut LeanObject,
    mut v_x1_4317_: *mut LeanObject,
    mut v_x2_4318_: *mut LeanObject,
    mut v_x3_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_x1_4317_);
    lean_inc(v_toPure_4311_);
    v___f_4320_ = lean_alloc_closure(
        l_Std_IterM_findM_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4320_, 0, v_toPure_4311_);
    lean_closure_set(v___f_4320_, 1, v___x_4312_);
    lean_closure_set(v___f_4320_, 2, v_x1_4317_);
    v___x_4321_ = lean_apply_1(v_f_4313_, v_x1_4317_);
    v___x_4322_ = lean_apply_2(v_toPure_4311_, lean_box(0), v___x_4321_);
    lean_inc_n(v_toBind_4314_, 2);
    v___x_4323_ = lean_apply_4(
        v_toBind_4314_,
        lean_box(0),
        lean_box(0),
        v___x_4322_,
        v___f_4320_,
    );
    v___x_4324_ = lean_apply_4(
        v_toBind_4314_,
        lean_box(0),
        lean_box(0),
        v___x_4323_,
        v___f_4315_,
    );
    v___x_4325_ = lean_apply_4(
        v_toBind_4314_,
        lean_box(0),
        lean_box(0),
        v___x_4324_,
        v___f_4316_,
    );
    return v___x_4325_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg___lam__4___boxed(
    mut v_toPure_4326_: *mut LeanObject,
    mut v___x_4327_: *mut LeanObject,
    mut v_f_4328_: *mut LeanObject,
    mut v_toBind_4329_: *mut LeanObject,
    mut v___f_4330_: *mut LeanObject,
    mut v___f_4331_: *mut LeanObject,
    mut v_x1_4332_: *mut LeanObject,
    mut v_x2_4333_: *mut LeanObject,
    mut v_x3_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4335_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x3_4334_);
    return v_res_4335_;
}
pub unsafe fn l_Std_IterM_find_x3f___redArg(
    mut v_inst_4336_: *mut LeanObject,
    mut v_inst_4337_: *mut LeanObject,
    mut v_it_4338_: *mut LeanObject,
    mut v_f_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4340_ = lean_ctor_get(v_inst_4336_, 0);
    lean_inc_ref(v_toApplicative_4340_);
    v_toBind_4341_ = lean_ctor_get(v_inst_4336_, 1);
    lean_inc_n(v_toBind_4341_, 2);
    lean_dec_ref(v_inst_4336_);
    v_toPure_4342_ = lean_ctor_get(v_toApplicative_4340_, 1);
    lean_inc_n(v_toPure_4342_, 3);
    lean_dec_ref(v_toApplicative_4340_);
    v___f_4343_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4343_, 0, v_toBind_4341_);
    v___f_4344_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4344_, 0, v_toPure_4342_);
    v___x_4345_ = lean_box(0);
    v___f_4346_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4346_, 0, v___x_4345_);
    lean_closure_set(v___f_4346_, 1, v_toPure_4342_);
    v___f_4347_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4347_, 0, v_toPure_4342_);
    lean_closure_set(v___f_4347_, 1, v___x_4345_);
    lean_closure_set(v___f_4347_, 2, v_f_4339_);
    lean_closure_set(v___f_4347_, 3, v_toBind_4341_);
    lean_closure_set(v___f_4347_, 4, v___f_4346_);
    lean_closure_set(v___f_4347_, 5, v___f_4344_);
    v___x_4348_ = lean_apply_6(
        v_inst_4337_,
        v___f_4343_,
        lean_box(0),
        lean_box(0),
        v_it_4338_,
        v___x_4345_,
        v___f_4347_,
    );
    return v___x_4348_;
}
pub unsafe fn l_Std_IterM_find_x3f(
    mut v_00_u03b1_4349_: *mut LeanObject,
    mut v_00_u03b2_4350_: *mut LeanObject,
    mut v_m_4351_: *mut LeanObject,
    mut v_inst_4352_: *mut LeanObject,
    mut v_inst_4353_: *mut LeanObject,
    mut v_inst_4354_: *mut LeanObject,
    mut v_it_4355_: *mut LeanObject,
    mut v_f_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4357_ = lean_ctor_get(v_inst_4352_, 0);
    lean_inc_ref(v_toApplicative_4357_);
    v_toBind_4358_ = lean_ctor_get(v_inst_4352_, 1);
    lean_inc_n(v_toBind_4358_, 2);
    lean_dec_ref(v_inst_4352_);
    v_toPure_4359_ = lean_ctor_get(v_toApplicative_4357_, 1);
    lean_inc_n(v_toPure_4359_, 3);
    lean_dec_ref(v_toApplicative_4357_);
    v___f_4360_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4360_, 0, v_toBind_4358_);
    v___f_4361_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4361_, 0, v_toPure_4359_);
    v___x_4362_ = lean_box(0);
    v___f_4363_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4363_, 0, v___x_4362_);
    lean_closure_set(v___f_4363_, 1, v_toPure_4359_);
    v___f_4364_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4364_, 0, v_toPure_4359_);
    lean_closure_set(v___f_4364_, 1, v___x_4362_);
    lean_closure_set(v___f_4364_, 2, v_f_4356_);
    lean_closure_set(v___f_4364_, 3, v_toBind_4358_);
    lean_closure_set(v___f_4364_, 4, v___f_4363_);
    lean_closure_set(v___f_4364_, 5, v___f_4361_);
    v___x_4365_ = lean_apply_6(
        v_inst_4354_,
        v___f_4360_,
        lean_box(0),
        lean_box(0),
        v_it_4355_,
        v___x_4362_,
        v___f_4364_,
    );
    return v___x_4365_;
}
pub unsafe fn l_Std_IterM_find_x3f___boxed(
    mut v_00_u03b1_4366_: *mut LeanObject,
    mut v_00_u03b2_4367_: *mut LeanObject,
    mut v_m_4368_: *mut LeanObject,
    mut v_inst_4369_: *mut LeanObject,
    mut v_inst_4370_: *mut LeanObject,
    mut v_inst_4371_: *mut LeanObject,
    mut v_it_4372_: *mut LeanObject,
    mut v_f_4373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4374_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4370_);
    return v_res_4374_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f___redArg(
    mut v_inst_4375_: *mut LeanObject,
    mut v_inst_4376_: *mut LeanObject,
    mut v_it_4377_: *mut LeanObject,
    mut v_f_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4379_ = lean_ctor_get(v_inst_4375_, 0);
    lean_inc_ref(v_toApplicative_4379_);
    v_toBind_4380_ = lean_ctor_get(v_inst_4375_, 1);
    lean_inc_n(v_toBind_4380_, 2);
    lean_dec_ref(v_inst_4375_);
    v_toPure_4381_ = lean_ctor_get(v_toApplicative_4379_, 1);
    lean_inc_n(v_toPure_4381_, 3);
    lean_dec_ref(v_toApplicative_4379_);
    v___f_4382_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4382_, 0, v_toBind_4380_);
    v___f_4383_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4383_, 0, v_toPure_4381_);
    v___x_4384_ = lean_box(0);
    v___f_4385_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4385_, 0, v___x_4384_);
    lean_closure_set(v___f_4385_, 1, v_toPure_4381_);
    v___f_4386_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4386_, 0, v_toPure_4381_);
    lean_closure_set(v___f_4386_, 1, v___x_4384_);
    lean_closure_set(v___f_4386_, 2, v_f_4378_);
    lean_closure_set(v___f_4386_, 3, v_toBind_4380_);
    lean_closure_set(v___f_4386_, 4, v___f_4385_);
    lean_closure_set(v___f_4386_, 5, v___f_4383_);
    v___x_4387_ = lean_apply_6(
        v_inst_4376_,
        v___f_4382_,
        lean_box(0),
        lean_box(0),
        v_it_4377_,
        v___x_4384_,
        v___f_4386_,
    );
    return v___x_4387_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f(
    mut v_00_u03b1_4388_: *mut LeanObject,
    mut v_00_u03b2_4389_: *mut LeanObject,
    mut v_m_4390_: *mut LeanObject,
    mut v_inst_4391_: *mut LeanObject,
    mut v_inst_4392_: *mut LeanObject,
    mut v_inst_4393_: *mut LeanObject,
    mut v_it_4394_: *mut LeanObject,
    mut v_f_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4396_ = lean_ctor_get(v_inst_4391_, 0);
    lean_inc_ref(v_toApplicative_4396_);
    v_toBind_4397_ = lean_ctor_get(v_inst_4391_, 1);
    lean_inc_n(v_toBind_4397_, 2);
    lean_dec_ref(v_inst_4391_);
    v_toPure_4398_ = lean_ctor_get(v_toApplicative_4396_, 1);
    lean_inc_n(v_toPure_4398_, 3);
    lean_dec_ref(v_toApplicative_4396_);
    v___f_4399_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4399_, 0, v_toBind_4397_);
    v___f_4400_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4400_, 0, v_toPure_4398_);
    v___x_4401_ = lean_box(0);
    v___f_4402_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4402_, 0, v___x_4401_);
    lean_closure_set(v___f_4402_, 1, v_toPure_4398_);
    v___f_4403_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4403_, 0, v_toPure_4398_);
    lean_closure_set(v___f_4403_, 1, v___x_4401_);
    lean_closure_set(v___f_4403_, 2, v_f_4395_);
    lean_closure_set(v___f_4403_, 3, v_toBind_4397_);
    lean_closure_set(v___f_4403_, 4, v___f_4402_);
    lean_closure_set(v___f_4403_, 5, v___f_4400_);
    v___x_4404_ = lean_apply_6(
        v_inst_4393_,
        v___f_4399_,
        lean_box(0),
        lean_box(0),
        v_it_4394_,
        v___x_4401_,
        v___f_4403_,
    );
    return v___x_4404_;
}
pub unsafe fn l_Std_IterM_Partial_find_x3f___boxed(
    mut v_00_u03b1_4405_: *mut LeanObject,
    mut v_00_u03b2_4406_: *mut LeanObject,
    mut v_m_4407_: *mut LeanObject,
    mut v_inst_4408_: *mut LeanObject,
    mut v_inst_4409_: *mut LeanObject,
    mut v_inst_4410_: *mut LeanObject,
    mut v_it_4411_: *mut LeanObject,
    mut v_f_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4413_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4409_);
    return v_res_4413_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f___redArg(
    mut v_inst_4414_: *mut LeanObject,
    mut v_inst_4415_: *mut LeanObject,
    mut v_it_4416_: *mut LeanObject,
    mut v_f_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4418_ = lean_ctor_get(v_inst_4414_, 0);
    lean_inc_ref(v_toApplicative_4418_);
    v_toBind_4419_ = lean_ctor_get(v_inst_4414_, 1);
    lean_inc_n(v_toBind_4419_, 2);
    lean_dec_ref(v_inst_4414_);
    v_toPure_4420_ = lean_ctor_get(v_toApplicative_4418_, 1);
    lean_inc_n(v_toPure_4420_, 3);
    lean_dec_ref(v_toApplicative_4418_);
    v___f_4421_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4421_, 0, v_toBind_4419_);
    v___f_4422_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4422_, 0, v_toPure_4420_);
    v___x_4423_ = lean_box(0);
    v___f_4424_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4424_, 0, v___x_4423_);
    lean_closure_set(v___f_4424_, 1, v_toPure_4420_);
    v___f_4425_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4425_, 0, v_toPure_4420_);
    lean_closure_set(v___f_4425_, 1, v___x_4423_);
    lean_closure_set(v___f_4425_, 2, v_f_4417_);
    lean_closure_set(v___f_4425_, 3, v_toBind_4419_);
    lean_closure_set(v___f_4425_, 4, v___f_4424_);
    lean_closure_set(v___f_4425_, 5, v___f_4422_);
    v___x_4426_ = lean_apply_6(
        v_inst_4415_,
        v___f_4421_,
        lean_box(0),
        lean_box(0),
        v_it_4416_,
        v___x_4423_,
        v___f_4425_,
    );
    return v___x_4426_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f(
    mut v_00_u03b1_4427_: *mut LeanObject,
    mut v_00_u03b2_4428_: *mut LeanObject,
    mut v_m_4429_: *mut LeanObject,
    mut v_inst_4430_: *mut LeanObject,
    mut v_inst_4431_: *mut LeanObject,
    mut v_inst_4432_: *mut LeanObject,
    mut v_inst_4433_: *mut LeanObject,
    mut v_it_4434_: *mut LeanObject,
    mut v_f_4435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4436_ = lean_ctor_get(v_inst_4430_, 0);
    lean_inc_ref(v_toApplicative_4436_);
    v_toBind_4437_ = lean_ctor_get(v_inst_4430_, 1);
    lean_inc_n(v_toBind_4437_, 2);
    lean_dec_ref(v_inst_4430_);
    v_toPure_4438_ = lean_ctor_get(v_toApplicative_4436_, 1);
    lean_inc_n(v_toPure_4438_, 3);
    lean_dec_ref(v_toApplicative_4436_);
    v___f_4439_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4439_, 0, v_toBind_4437_);
    v___f_4440_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4440_, 0, v_toPure_4438_);
    v___x_4441_ = lean_box(0);
    v___f_4442_ = lean_alloc_closure(
        l_Std_IterM_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4442_, 0, v___x_4441_);
    lean_closure_set(v___f_4442_, 1, v_toPure_4438_);
    v___f_4443_ = lean_alloc_closure(
        l_Std_IterM_find_x3f___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_4443_, 0, v_toPure_4438_);
    lean_closure_set(v___f_4443_, 1, v___x_4441_);
    lean_closure_set(v___f_4443_, 2, v_f_4435_);
    lean_closure_set(v___f_4443_, 3, v_toBind_4437_);
    lean_closure_set(v___f_4443_, 4, v___f_4442_);
    lean_closure_set(v___f_4443_, 5, v___f_4440_);
    v___x_4444_ = lean_apply_6(
        v_inst_4432_,
        v___f_4439_,
        lean_box(0),
        lean_box(0),
        v_it_4434_,
        v___x_4441_,
        v___f_4443_,
    );
    return v___x_4444_;
}
pub unsafe fn l_Std_IterM_Total_find_x3f___boxed(
    mut v_00_u03b1_4445_: *mut LeanObject,
    mut v_00_u03b2_4446_: *mut LeanObject,
    mut v_m_4447_: *mut LeanObject,
    mut v_inst_4448_: *mut LeanObject,
    mut v_inst_4449_: *mut LeanObject,
    mut v_inst_4450_: *mut LeanObject,
    mut v_inst_4451_: *mut LeanObject,
    mut v_it_4452_: *mut LeanObject,
    mut v_f_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4454_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4449_);
    return v_res_4454_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__0(
    mut v_toBind_4455_: *mut LeanObject,
    mut v_x_4456_: *mut LeanObject,
    mut v_x_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = lean_apply_4(
        v_toBind_4455_,
        lean_box(0),
        lean_box(0),
        v___y_4459_,
        v___y_4458_,
    );
    return v___x_4460_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__1(
    mut v_toPure_4461_: *mut LeanObject,
    mut v_b_4462_: *mut LeanObject,
    mut v_x_4463_: *mut LeanObject,
    mut v_x_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    v___x_4465_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4465_, 0, v_b_4462_);
    v___x_4466_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4466_, 0, v___x_4465_);
    v___x_4467_ = lean_apply_2(v_toPure_4461_, lean_box(0), v___x_4466_);
    return v___x_4467_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg___lam__1___boxed(
    mut v_toPure_4468_: *mut LeanObject,
    mut v_b_4469_: *mut LeanObject,
    mut v_x_4470_: *mut LeanObject,
    mut v_x_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4472_: *mut LeanObject = core::ptr::null_mut();
    v_res_4472_ =
        l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_4468_, v_b_4469_, v_x_4470_, v_x_4471_);
    lean_dec(v_x_4471_);
    return v_res_4472_;
}
pub unsafe fn l_Std_IterM_first_x3f___redArg(
    mut v_inst_4473_: *mut LeanObject,
    mut v_inst_4474_: *mut LeanObject,
    mut v_it_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4476_ = lean_ctor_get(v_inst_4473_, 0);
    lean_inc_ref(v_toApplicative_4476_);
    v_toBind_4477_ = lean_ctor_get(v_inst_4473_, 1);
    lean_inc(v_toBind_4477_);
    lean_dec_ref(v_inst_4473_);
    v_toPure_4478_ = lean_ctor_get(v_toApplicative_4476_, 1);
    lean_inc(v_toPure_4478_);
    lean_dec_ref(v_toApplicative_4476_);
    v___f_4479_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4479_, 0, v_toBind_4477_);
    v___f_4480_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4480_, 0, v_toPure_4478_);
    v___x_4481_ = lean_box(0);
    v___x_4482_ = lean_apply_6(
        v_inst_4474_,
        v___f_4479_,
        lean_box(0),
        lean_box(0),
        v_it_4475_,
        v___x_4481_,
        v___f_4480_,
    );
    return v___x_4482_;
}
pub unsafe fn l_Std_IterM_first_x3f(
    mut v_00_u03b1_4483_: *mut LeanObject,
    mut v_00_u03b2_4484_: *mut LeanObject,
    mut v_m_4485_: *mut LeanObject,
    mut v_inst_4486_: *mut LeanObject,
    mut v_inst_4487_: *mut LeanObject,
    mut v_inst_4488_: *mut LeanObject,
    mut v_it_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4490_ = lean_ctor_get(v_inst_4486_, 0);
    lean_inc_ref(v_toApplicative_4490_);
    v_toBind_4491_ = lean_ctor_get(v_inst_4486_, 1);
    lean_inc(v_toBind_4491_);
    lean_dec_ref(v_inst_4486_);
    v_toPure_4492_ = lean_ctor_get(v_toApplicative_4490_, 1);
    lean_inc(v_toPure_4492_);
    lean_dec_ref(v_toApplicative_4490_);
    v___f_4493_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4493_, 0, v_toBind_4491_);
    v___f_4494_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4494_, 0, v_toPure_4492_);
    v___x_4495_ = lean_box(0);
    v___x_4496_ = lean_apply_6(
        v_inst_4488_,
        v___f_4493_,
        lean_box(0),
        lean_box(0),
        v_it_4489_,
        v___x_4495_,
        v___f_4494_,
    );
    return v___x_4496_;
}
pub unsafe fn l_Std_IterM_first_x3f___boxed(
    mut v_00_u03b1_4497_: *mut LeanObject,
    mut v_00_u03b2_4498_: *mut LeanObject,
    mut v_m_4499_: *mut LeanObject,
    mut v_inst_4500_: *mut LeanObject,
    mut v_inst_4501_: *mut LeanObject,
    mut v_inst_4502_: *mut LeanObject,
    mut v_it_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4504_: *mut LeanObject = core::ptr::null_mut();
    v_res_4504_ = l_Std_IterM_first_x3f(
        v_00_u03b1_4497_,
        v_00_u03b2_4498_,
        v_m_4499_,
        v_inst_4500_,
        v_inst_4501_,
        v_inst_4502_,
        v_it_4503_,
    );
    lean_dec(v_inst_4501_);
    return v_res_4504_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f___redArg(
    mut v_inst_4505_: *mut LeanObject,
    mut v_inst_4506_: *mut LeanObject,
    mut v_it_4507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4508_ = lean_ctor_get(v_inst_4505_, 0);
    lean_inc_ref(v_toApplicative_4508_);
    v_toBind_4509_ = lean_ctor_get(v_inst_4505_, 1);
    lean_inc(v_toBind_4509_);
    lean_dec_ref(v_inst_4505_);
    v_toPure_4510_ = lean_ctor_get(v_toApplicative_4508_, 1);
    lean_inc(v_toPure_4510_);
    lean_dec_ref(v_toApplicative_4508_);
    v___f_4511_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4511_, 0, v_toBind_4509_);
    v___f_4512_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4512_, 0, v_toPure_4510_);
    v___x_4513_ = lean_box(0);
    v___x_4514_ = lean_apply_6(
        v_inst_4506_,
        v___f_4511_,
        lean_box(0),
        lean_box(0),
        v_it_4507_,
        v___x_4513_,
        v___f_4512_,
    );
    return v___x_4514_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f(
    mut v_00_u03b1_4515_: *mut LeanObject,
    mut v_00_u03b2_4516_: *mut LeanObject,
    mut v_m_4517_: *mut LeanObject,
    mut v_inst_4518_: *mut LeanObject,
    mut v_inst_4519_: *mut LeanObject,
    mut v_inst_4520_: *mut LeanObject,
    mut v_inst_4521_: *mut LeanObject,
    mut v_it_4522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4523_ = lean_ctor_get(v_inst_4518_, 0);
    lean_inc_ref(v_toApplicative_4523_);
    v_toBind_4524_ = lean_ctor_get(v_inst_4518_, 1);
    lean_inc(v_toBind_4524_);
    lean_dec_ref(v_inst_4518_);
    v_toPure_4525_ = lean_ctor_get(v_toApplicative_4523_, 1);
    lean_inc(v_toPure_4525_);
    lean_dec_ref(v_toApplicative_4523_);
    v___f_4526_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4526_, 0, v_toBind_4524_);
    v___f_4527_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4527_, 0, v_toPure_4525_);
    v___x_4528_ = lean_box(0);
    v___x_4529_ = lean_apply_6(
        v_inst_4520_,
        v___f_4526_,
        lean_box(0),
        lean_box(0),
        v_it_4522_,
        v___x_4528_,
        v___f_4527_,
    );
    return v___x_4529_;
}
pub unsafe fn l_Std_IterM_Total_first_x3f___boxed(
    mut v_00_u03b1_4530_: *mut LeanObject,
    mut v_00_u03b2_4531_: *mut LeanObject,
    mut v_m_4532_: *mut LeanObject,
    mut v_inst_4533_: *mut LeanObject,
    mut v_inst_4534_: *mut LeanObject,
    mut v_inst_4535_: *mut LeanObject,
    mut v_inst_4536_: *mut LeanObject,
    mut v_it_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4538_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4534_);
    return v_res_4538_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg___lam__1(
    mut v_toPure_4542_: *mut LeanObject,
    mut v_x_4543_: *mut LeanObject,
    mut v_x_4544_: *mut LeanObject,
    mut v_x_4545_: u8,
) -> *mut LeanObject {
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Std_IterM_isEmpty___redArg___lam__1___closed__0;
    v___x_4547_ = lean_apply_2(v_toPure_4542_, lean_box(0), v___x_4546_);
    return v___x_4547_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg___lam__1___boxed(
    mut v_toPure_4548_: *mut LeanObject,
    mut v_x_4549_: *mut LeanObject,
    mut v_x_4550_: *mut LeanObject,
    mut v_x_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_79__boxed_4552_: u8 = 0;
    let mut v_res_4553_: *mut LeanObject = core::ptr::null_mut();
    v_x_79__boxed_4552_ = (lean_unbox(v_x_4551_) as u8);
    v_res_4553_ = l_Std_IterM_isEmpty___redArg___lam__1(
        v_toPure_4548_,
        v_x_4549_,
        v_x_4550_,
        v_x_79__boxed_4552_,
    );
    lean_dec(v_x_4549_);
    return v_res_4553_;
}
pub unsafe fn l_Std_IterM_isEmpty___redArg(
    mut v_inst_4554_: *mut LeanObject,
    mut v_inst_4555_: *mut LeanObject,
    mut v_it_4556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4557_ = lean_ctor_get(v_inst_4554_, 0);
    lean_inc_ref(v_toApplicative_4557_);
    v_toBind_4558_ = lean_ctor_get(v_inst_4554_, 1);
    lean_inc(v_toBind_4558_);
    lean_dec_ref(v_inst_4554_);
    v_toPure_4559_ = lean_ctor_get(v_toApplicative_4557_, 1);
    lean_inc(v_toPure_4559_);
    lean_dec_ref(v_toApplicative_4557_);
    v___f_4560_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4560_, 0, v_toBind_4558_);
    v___f_4561_ = lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4561_, 0, v_toPure_4559_);
    v___x_4562_ = 1;
    v___x_4563_ = lean_box((v___x_4562_) as usize);
    v___x_4564_ = lean_apply_6(
        v_inst_4555_,
        v___f_4560_,
        lean_box(0),
        lean_box(0),
        v_it_4556_,
        v___x_4563_,
        v___f_4561_,
    );
    return v___x_4564_;
}
pub unsafe fn l_Std_IterM_isEmpty(
    mut v_00_u03b1_4565_: *mut LeanObject,
    mut v_00_u03b2_4566_: *mut LeanObject,
    mut v_m_4567_: *mut LeanObject,
    mut v_inst_4568_: *mut LeanObject,
    mut v_inst_4569_: *mut LeanObject,
    mut v_inst_4570_: *mut LeanObject,
    mut v_it_4571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4572_ = lean_ctor_get(v_inst_4568_, 0);
    lean_inc_ref(v_toApplicative_4572_);
    v_toBind_4573_ = lean_ctor_get(v_inst_4568_, 1);
    lean_inc(v_toBind_4573_);
    lean_dec_ref(v_inst_4568_);
    v_toPure_4574_ = lean_ctor_get(v_toApplicative_4572_, 1);
    lean_inc(v_toPure_4574_);
    lean_dec_ref(v_toApplicative_4572_);
    v___f_4575_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4575_, 0, v_toBind_4573_);
    v___f_4576_ = lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4576_, 0, v_toPure_4574_);
    v___x_4577_ = 1;
    v___x_4578_ = lean_box((v___x_4577_) as usize);
    v___x_4579_ = lean_apply_6(
        v_inst_4570_,
        v___f_4575_,
        lean_box(0),
        lean_box(0),
        v_it_4571_,
        v___x_4578_,
        v___f_4576_,
    );
    return v___x_4579_;
}
pub unsafe fn l_Std_IterM_isEmpty___boxed(
    mut v_00_u03b1_4580_: *mut LeanObject,
    mut v_00_u03b2_4581_: *mut LeanObject,
    mut v_m_4582_: *mut LeanObject,
    mut v_inst_4583_: *mut LeanObject,
    mut v_inst_4584_: *mut LeanObject,
    mut v_inst_4585_: *mut LeanObject,
    mut v_it_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4587_: *mut LeanObject = core::ptr::null_mut();
    v_res_4587_ = l_Std_IterM_isEmpty(
        v_00_u03b1_4580_,
        v_00_u03b2_4581_,
        v_m_4582_,
        v_inst_4583_,
        v_inst_4584_,
        v_inst_4585_,
        v_it_4586_,
    );
    lean_dec(v_inst_4584_);
    return v_res_4587_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty___redArg(
    mut v_inst_4588_: *mut LeanObject,
    mut v_inst_4589_: *mut LeanObject,
    mut v_it_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4591_ = lean_ctor_get(v_inst_4588_, 0);
    lean_inc_ref(v_toApplicative_4591_);
    v_toBind_4592_ = lean_ctor_get(v_inst_4588_, 1);
    lean_inc(v_toBind_4592_);
    lean_dec_ref(v_inst_4588_);
    v_toPure_4593_ = lean_ctor_get(v_toApplicative_4591_, 1);
    lean_inc(v_toPure_4593_);
    lean_dec_ref(v_toApplicative_4591_);
    v___f_4594_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4594_, 0, v_toBind_4592_);
    v___f_4595_ = lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4595_, 0, v_toPure_4593_);
    v___x_4596_ = 1;
    v___x_4597_ = lean_box((v___x_4596_) as usize);
    v___x_4598_ = lean_apply_6(
        v_inst_4589_,
        v___f_4594_,
        lean_box(0),
        lean_box(0),
        v_it_4590_,
        v___x_4597_,
        v___f_4595_,
    );
    return v___x_4598_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty(
    mut v_00_u03b1_4599_: *mut LeanObject,
    mut v_00_u03b2_4600_: *mut LeanObject,
    mut v_m_4601_: *mut LeanObject,
    mut v_inst_4602_: *mut LeanObject,
    mut v_inst_4603_: *mut LeanObject,
    mut v_inst_4604_: *mut LeanObject,
    mut v_inst_4605_: *mut LeanObject,
    mut v_it_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4607_ = lean_ctor_get(v_inst_4602_, 0);
    lean_inc_ref(v_toApplicative_4607_);
    v_toBind_4608_ = lean_ctor_get(v_inst_4602_, 1);
    lean_inc(v_toBind_4608_);
    lean_dec_ref(v_inst_4602_);
    v_toPure_4609_ = lean_ctor_get(v_toApplicative_4607_, 1);
    lean_inc(v_toPure_4609_);
    lean_dec_ref(v_toApplicative_4607_);
    v___f_4610_ = lean_alloc_closure(
        l_Std_IterM_first_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4610_, 0, v_toBind_4608_);
    v___f_4611_ = lean_alloc_closure(
        l_Std_IterM_isEmpty___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4611_, 0, v_toPure_4609_);
    v___x_4612_ = 1;
    v___x_4613_ = lean_box((v___x_4612_) as usize);
    v___x_4614_ = lean_apply_6(
        v_inst_4604_,
        v___f_4610_,
        lean_box(0),
        lean_box(0),
        v_it_4606_,
        v___x_4613_,
        v___f_4611_,
    );
    return v___x_4614_;
}
pub unsafe fn l_Std_IterM_Total_isEmpty___boxed(
    mut v_00_u03b1_4615_: *mut LeanObject,
    mut v_00_u03b2_4616_: *mut LeanObject,
    mut v_m_4617_: *mut LeanObject,
    mut v_inst_4618_: *mut LeanObject,
    mut v_inst_4619_: *mut LeanObject,
    mut v_inst_4620_: *mut LeanObject,
    mut v_inst_4621_: *mut LeanObject,
    mut v_it_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4623_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_4619_);
    return v_res_4623_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__1(
    mut v_toPure_4624_: *mut LeanObject,
    mut v_____do__lift_4625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    v___x_4626_ = lean_apply_2(v_toPure_4624_, lean_box(0), v_____do__lift_4625_);
    return v___x_4626_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__0(
    mut v_toPure_4627_: *mut LeanObject,
    mut v_toBind_4628_: *mut LeanObject,
    mut v___f_4629_: *mut LeanObject,
    mut v_x1_4630_: *mut LeanObject,
    mut v_x2_4631_: *mut LeanObject,
    mut v_x3_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    v___x_4633_ = lean_unsigned_to_nat(1);
    v___x_4634_ = lean_nat_add(v_x3_4632_, v___x_4633_);
    v___x_4635_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4635_, 0, v___x_4634_);
    v___x_4636_ = lean_apply_2(v_toPure_4627_, lean_box(0), v___x_4635_);
    v___x_4637_ = lean_apply_4(
        v_toBind_4628_,
        lean_box(0),
        lean_box(0),
        v___x_4636_,
        v___f_4629_,
    );
    return v___x_4637_;
}
pub unsafe fn l_Std_IterM_length___redArg___lam__0___boxed(
    mut v_toPure_4638_: *mut LeanObject,
    mut v_toBind_4639_: *mut LeanObject,
    mut v___f_4640_: *mut LeanObject,
    mut v_x1_4641_: *mut LeanObject,
    mut v_x2_4642_: *mut LeanObject,
    mut v_x3_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4644_: *mut LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Std_IterM_length___redArg___lam__0(
        v_toPure_4638_,
        v_toBind_4639_,
        v___f_4640_,
        v_x1_4641_,
        v_x2_4642_,
        v_x3_4643_,
    );
    lean_dec(v_x3_4643_);
    lean_dec(v_x1_4641_);
    return v_res_4644_;
}
pub unsafe fn l_Std_IterM_length___redArg(
    mut v_inst_4645_: *mut LeanObject,
    mut v_inst_4646_: *mut LeanObject,
    mut v_it_4647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4648_ = lean_ctor_get(v_inst_4646_, 0);
    lean_inc_ref(v_toApplicative_4648_);
    v_toBind_4649_ = lean_ctor_get(v_inst_4646_, 1);
    lean_inc_n(v_toBind_4649_, 2);
    lean_dec_ref(v_inst_4646_);
    v_toPure_4650_ = lean_ctor_get(v_toApplicative_4648_, 1);
    lean_inc_n(v_toPure_4650_, 2);
    lean_dec_ref(v_toApplicative_4648_);
    v___x_4651_ = lean_unsigned_to_nat(0);
    v___f_4652_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4652_, 0, v_toBind_4649_);
    v___f_4653_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4653_, 0, v_toPure_4650_);
    v___f_4654_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4654_, 0, v_toPure_4650_);
    lean_closure_set(v___f_4654_, 1, v_toBind_4649_);
    lean_closure_set(v___f_4654_, 2, v___f_4653_);
    v___x_4655_ = lean_apply_6(
        v_inst_4645_,
        v___f_4652_,
        lean_box(0),
        lean_box(0),
        v_it_4647_,
        v___x_4651_,
        v___f_4654_,
    );
    return v___x_4655_;
}
pub unsafe fn l_Std_IterM_length(
    mut v_00_u03b1_4656_: *mut LeanObject,
    mut v_m_4657_: *mut LeanObject,
    mut v_00_u03b2_4658_: *mut LeanObject,
    mut v_inst_4659_: *mut LeanObject,
    mut v_inst_4660_: *mut LeanObject,
    mut v_inst_4661_: *mut LeanObject,
    mut v_it_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4663_ = lean_ctor_get(v_inst_4661_, 0);
    lean_inc_ref(v_toApplicative_4663_);
    v_toBind_4664_ = lean_ctor_get(v_inst_4661_, 1);
    lean_inc_n(v_toBind_4664_, 2);
    lean_dec_ref(v_inst_4661_);
    v_toPure_4665_ = lean_ctor_get(v_toApplicative_4663_, 1);
    lean_inc_n(v_toPure_4665_, 2);
    lean_dec_ref(v_toApplicative_4663_);
    v___x_4666_ = lean_unsigned_to_nat(0);
    v___f_4667_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4667_, 0, v_toBind_4664_);
    v___f_4668_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4668_, 0, v_toPure_4665_);
    v___f_4669_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4669_, 0, v_toPure_4665_);
    lean_closure_set(v___f_4669_, 1, v_toBind_4664_);
    lean_closure_set(v___f_4669_, 2, v___f_4668_);
    v___x_4670_ = lean_apply_6(
        v_inst_4660_,
        v___f_4667_,
        lean_box(0),
        lean_box(0),
        v_it_4662_,
        v___x_4666_,
        v___f_4669_,
    );
    return v___x_4670_;
}
pub unsafe fn l_Std_IterM_length___boxed(
    mut v_00_u03b1_4671_: *mut LeanObject,
    mut v_m_4672_: *mut LeanObject,
    mut v_00_u03b2_4673_: *mut LeanObject,
    mut v_inst_4674_: *mut LeanObject,
    mut v_inst_4675_: *mut LeanObject,
    mut v_inst_4676_: *mut LeanObject,
    mut v_it_4677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4678_: *mut LeanObject = core::ptr::null_mut();
    v_res_4678_ = l_Std_IterM_length(
        v_00_u03b1_4671_,
        v_m_4672_,
        v_00_u03b2_4673_,
        v_inst_4674_,
        v_inst_4675_,
        v_inst_4676_,
        v_it_4677_,
    );
    lean_dec(v_inst_4674_);
    return v_res_4678_;
}
pub unsafe fn l_Std_IterM_count___redArg(
    mut v_inst_4679_: *mut LeanObject,
    mut v_inst_4680_: *mut LeanObject,
    mut v_it_4681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4682_ = lean_ctor_get(v_inst_4680_, 0);
    lean_inc_ref(v_toApplicative_4682_);
    v_toBind_4683_ = lean_ctor_get(v_inst_4680_, 1);
    lean_inc_n(v_toBind_4683_, 2);
    lean_dec_ref(v_inst_4680_);
    v_toPure_4684_ = lean_ctor_get(v_toApplicative_4682_, 1);
    lean_inc_n(v_toPure_4684_, 2);
    lean_dec_ref(v_toApplicative_4682_);
    v___x_4685_ = lean_unsigned_to_nat(0);
    v___f_4686_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4686_, 0, v_toBind_4683_);
    v___f_4687_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4687_, 0, v_toPure_4684_);
    v___f_4688_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4688_, 0, v_toPure_4684_);
    lean_closure_set(v___f_4688_, 1, v_toBind_4683_);
    lean_closure_set(v___f_4688_, 2, v___f_4687_);
    v___x_4689_ = lean_apply_6(
        v_inst_4679_,
        v___f_4686_,
        lean_box(0),
        lean_box(0),
        v_it_4681_,
        v___x_4685_,
        v___f_4688_,
    );
    return v___x_4689_;
}
pub unsafe fn l_Std_IterM_count(
    mut v_00_u03b1_4690_: *mut LeanObject,
    mut v_m_4691_: *mut LeanObject,
    mut v_00_u03b2_4692_: *mut LeanObject,
    mut v_inst_4693_: *mut LeanObject,
    mut v_inst_4694_: *mut LeanObject,
    mut v_inst_4695_: *mut LeanObject,
    mut v_it_4696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4697_ = lean_ctor_get(v_inst_4695_, 0);
    lean_inc_ref(v_toApplicative_4697_);
    v_toBind_4698_ = lean_ctor_get(v_inst_4695_, 1);
    lean_inc_n(v_toBind_4698_, 2);
    lean_dec_ref(v_inst_4695_);
    v_toPure_4699_ = lean_ctor_get(v_toApplicative_4697_, 1);
    lean_inc_n(v_toPure_4699_, 2);
    lean_dec_ref(v_toApplicative_4697_);
    v___x_4700_ = lean_unsigned_to_nat(0);
    v___f_4701_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4701_, 0, v_toBind_4698_);
    v___f_4702_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4702_, 0, v_toPure_4699_);
    v___f_4703_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4703_, 0, v_toPure_4699_);
    lean_closure_set(v___f_4703_, 1, v_toBind_4698_);
    lean_closure_set(v___f_4703_, 2, v___f_4702_);
    v___x_4704_ = lean_apply_6(
        v_inst_4694_,
        v___f_4701_,
        lean_box(0),
        lean_box(0),
        v_it_4696_,
        v___x_4700_,
        v___f_4703_,
    );
    return v___x_4704_;
}
pub unsafe fn l_Std_IterM_count___boxed(
    mut v_00_u03b1_4705_: *mut LeanObject,
    mut v_m_4706_: *mut LeanObject,
    mut v_00_u03b2_4707_: *mut LeanObject,
    mut v_inst_4708_: *mut LeanObject,
    mut v_inst_4709_: *mut LeanObject,
    mut v_inst_4710_: *mut LeanObject,
    mut v_it_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4712_: *mut LeanObject = core::ptr::null_mut();
    v_res_4712_ = l_Std_IterM_count(
        v_00_u03b1_4705_,
        v_m_4706_,
        v_00_u03b2_4707_,
        v_inst_4708_,
        v_inst_4709_,
        v_inst_4710_,
        v_it_4711_,
    );
    lean_dec(v_inst_4708_);
    return v_res_4712_;
}
pub unsafe fn l_Std_IterM_size___redArg(
    mut v_inst_4713_: *mut LeanObject,
    mut v_inst_4714_: *mut LeanObject,
    mut v_it_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4716_ = lean_ctor_get(v_inst_4714_, 0);
    lean_inc_ref(v_toApplicative_4716_);
    v_toBind_4717_ = lean_ctor_get(v_inst_4714_, 1);
    lean_inc_n(v_toBind_4717_, 2);
    lean_dec_ref(v_inst_4714_);
    v_toPure_4718_ = lean_ctor_get(v_toApplicative_4716_, 1);
    lean_inc_n(v_toPure_4718_, 2);
    lean_dec_ref(v_toApplicative_4716_);
    v___x_4719_ = lean_unsigned_to_nat(0);
    v___f_4720_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4720_, 0, v_toBind_4717_);
    v___f_4721_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4721_, 0, v_toPure_4718_);
    v___f_4722_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4722_, 0, v_toPure_4718_);
    lean_closure_set(v___f_4722_, 1, v_toBind_4717_);
    lean_closure_set(v___f_4722_, 2, v___f_4721_);
    v___x_4723_ = lean_apply_6(
        v_inst_4713_,
        v___f_4720_,
        lean_box(0),
        lean_box(0),
        v_it_4715_,
        v___x_4719_,
        v___f_4722_,
    );
    return v___x_4723_;
}
pub unsafe fn l_Std_IterM_size(
    mut v_00_u03b1_4724_: *mut LeanObject,
    mut v_m_4725_: *mut LeanObject,
    mut v_00_u03b2_4726_: *mut LeanObject,
    mut v_inst_4727_: *mut LeanObject,
    mut v_inst_4728_: *mut LeanObject,
    mut v_inst_4729_: *mut LeanObject,
    mut v_it_4730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4731_ = lean_ctor_get(v_inst_4729_, 0);
    lean_inc_ref(v_toApplicative_4731_);
    v_toBind_4732_ = lean_ctor_get(v_inst_4729_, 1);
    lean_inc_n(v_toBind_4732_, 2);
    lean_dec_ref(v_inst_4729_);
    v_toPure_4733_ = lean_ctor_get(v_toApplicative_4731_, 1);
    lean_inc_n(v_toPure_4733_, 2);
    lean_dec_ref(v_toApplicative_4731_);
    v___x_4734_ = lean_unsigned_to_nat(0);
    v___f_4735_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4735_, 0, v_toBind_4732_);
    v___f_4736_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4736_, 0, v_toPure_4733_);
    v___f_4737_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4737_, 0, v_toPure_4733_);
    lean_closure_set(v___f_4737_, 1, v_toBind_4732_);
    lean_closure_set(v___f_4737_, 2, v___f_4736_);
    v___x_4738_ = lean_apply_6(
        v_inst_4728_,
        v___f_4735_,
        lean_box(0),
        lean_box(0),
        v_it_4730_,
        v___x_4734_,
        v___f_4737_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Std_IterM_size___boxed(
    mut v_00_u03b1_4739_: *mut LeanObject,
    mut v_m_4740_: *mut LeanObject,
    mut v_00_u03b2_4741_: *mut LeanObject,
    mut v_inst_4742_: *mut LeanObject,
    mut v_inst_4743_: *mut LeanObject,
    mut v_inst_4744_: *mut LeanObject,
    mut v_it_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4746_: *mut LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Std_IterM_size(
        v_00_u03b1_4739_,
        v_m_4740_,
        v_00_u03b2_4741_,
        v_inst_4742_,
        v_inst_4743_,
        v_inst_4744_,
        v_it_4745_,
    );
    lean_dec(v_inst_4742_);
    return v_res_4746_;
}
pub unsafe fn l_Std_IterM_Partial_count___redArg(
    mut v_inst_4747_: *mut LeanObject,
    mut v_inst_4748_: *mut LeanObject,
    mut v_it_4749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4750_ = lean_ctor_get(v_inst_4748_, 0);
    lean_inc_ref(v_toApplicative_4750_);
    v_toBind_4751_ = lean_ctor_get(v_inst_4748_, 1);
    lean_inc_n(v_toBind_4751_, 2);
    lean_dec_ref(v_inst_4748_);
    v_toPure_4752_ = lean_ctor_get(v_toApplicative_4750_, 1);
    lean_inc_n(v_toPure_4752_, 2);
    lean_dec_ref(v_toApplicative_4750_);
    v___x_4753_ = lean_unsigned_to_nat(0);
    v___f_4754_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4754_, 0, v_toBind_4751_);
    v___f_4755_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4755_, 0, v_toPure_4752_);
    v___f_4756_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4756_, 0, v_toPure_4752_);
    lean_closure_set(v___f_4756_, 1, v_toBind_4751_);
    lean_closure_set(v___f_4756_, 2, v___f_4755_);
    v___x_4757_ = lean_apply_6(
        v_inst_4747_,
        v___f_4754_,
        lean_box(0),
        lean_box(0),
        v_it_4749_,
        v___x_4753_,
        v___f_4756_,
    );
    return v___x_4757_;
}
pub unsafe fn l_Std_IterM_Partial_count(
    mut v_00_u03b1_4758_: *mut LeanObject,
    mut v_m_4759_: *mut LeanObject,
    mut v_00_u03b2_4760_: *mut LeanObject,
    mut v_inst_4761_: *mut LeanObject,
    mut v_inst_4762_: *mut LeanObject,
    mut v_inst_4763_: *mut LeanObject,
    mut v_it_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4765_ = lean_ctor_get(v_inst_4763_, 0);
    lean_inc_ref(v_toApplicative_4765_);
    v_toBind_4766_ = lean_ctor_get(v_inst_4763_, 1);
    lean_inc_n(v_toBind_4766_, 2);
    lean_dec_ref(v_inst_4763_);
    v_toPure_4767_ = lean_ctor_get(v_toApplicative_4765_, 1);
    lean_inc_n(v_toPure_4767_, 2);
    lean_dec_ref(v_toApplicative_4765_);
    v___x_4768_ = lean_unsigned_to_nat(0);
    v___f_4769_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4769_, 0, v_toBind_4766_);
    v___f_4770_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4770_, 0, v_toPure_4767_);
    v___f_4771_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4771_, 0, v_toPure_4767_);
    lean_closure_set(v___f_4771_, 1, v_toBind_4766_);
    lean_closure_set(v___f_4771_, 2, v___f_4770_);
    v___x_4772_ = lean_apply_6(
        v_inst_4762_,
        v___f_4769_,
        lean_box(0),
        lean_box(0),
        v_it_4764_,
        v___x_4768_,
        v___f_4771_,
    );
    return v___x_4772_;
}
pub unsafe fn l_Std_IterM_Partial_count___boxed(
    mut v_00_u03b1_4773_: *mut LeanObject,
    mut v_m_4774_: *mut LeanObject,
    mut v_00_u03b2_4775_: *mut LeanObject,
    mut v_inst_4776_: *mut LeanObject,
    mut v_inst_4777_: *mut LeanObject,
    mut v_inst_4778_: *mut LeanObject,
    mut v_it_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4780_: *mut LeanObject = core::ptr::null_mut();
    v_res_4780_ = l_Std_IterM_Partial_count(
        v_00_u03b1_4773_,
        v_m_4774_,
        v_00_u03b2_4775_,
        v_inst_4776_,
        v_inst_4777_,
        v_inst_4778_,
        v_it_4779_,
    );
    lean_dec(v_inst_4776_);
    return v_res_4780_;
}
pub unsafe fn l_Std_IterM_Partial_size___redArg(
    mut v_inst_4781_: *mut LeanObject,
    mut v_inst_4782_: *mut LeanObject,
    mut v_it_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4784_ = lean_ctor_get(v_inst_4782_, 0);
    lean_inc_ref(v_toApplicative_4784_);
    v_toBind_4785_ = lean_ctor_get(v_inst_4782_, 1);
    lean_inc_n(v_toBind_4785_, 2);
    lean_dec_ref(v_inst_4782_);
    v_toPure_4786_ = lean_ctor_get(v_toApplicative_4784_, 1);
    lean_inc_n(v_toPure_4786_, 2);
    lean_dec_ref(v_toApplicative_4784_);
    v___x_4787_ = lean_unsigned_to_nat(0);
    v___f_4788_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4788_, 0, v_toBind_4785_);
    v___f_4789_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4789_, 0, v_toPure_4786_);
    v___f_4790_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4790_, 0, v_toPure_4786_);
    lean_closure_set(v___f_4790_, 1, v_toBind_4785_);
    lean_closure_set(v___f_4790_, 2, v___f_4789_);
    v___x_4791_ = lean_apply_6(
        v_inst_4781_,
        v___f_4788_,
        lean_box(0),
        lean_box(0),
        v_it_4783_,
        v___x_4787_,
        v___f_4790_,
    );
    return v___x_4791_;
}
pub unsafe fn l_Std_IterM_Partial_size(
    mut v_00_u03b1_4792_: *mut LeanObject,
    mut v_m_4793_: *mut LeanObject,
    mut v_00_u03b2_4794_: *mut LeanObject,
    mut v_inst_4795_: *mut LeanObject,
    mut v_inst_4796_: *mut LeanObject,
    mut v_inst_4797_: *mut LeanObject,
    mut v_it_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4799_ = lean_ctor_get(v_inst_4797_, 0);
    lean_inc_ref(v_toApplicative_4799_);
    v_toBind_4800_ = lean_ctor_get(v_inst_4797_, 1);
    lean_inc_n(v_toBind_4800_, 2);
    lean_dec_ref(v_inst_4797_);
    v_toPure_4801_ = lean_ctor_get(v_toApplicative_4799_, 1);
    lean_inc_n(v_toPure_4801_, 2);
    lean_dec_ref(v_toApplicative_4799_);
    v___x_4802_ = lean_unsigned_to_nat(0);
    v___f_4803_ = lean_alloc_closure(
        l_Std_IterM_fold___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4803_, 0, v_toBind_4800_);
    v___f_4804_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4804_, 0, v_toPure_4801_);
    v___f_4805_ = lean_alloc_closure(
        l_Std_IterM_length___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_4805_, 0, v_toPure_4801_);
    lean_closure_set(v___f_4805_, 1, v_toBind_4800_);
    lean_closure_set(v___f_4805_, 2, v___f_4804_);
    v___x_4806_ = lean_apply_6(
        v_inst_4796_,
        v___f_4803_,
        lean_box(0),
        lean_box(0),
        v_it_4798_,
        v___x_4802_,
        v___f_4805_,
    );
    return v___x_4806_;
}
pub unsafe fn l_Std_IterM_Partial_size___boxed(
    mut v_00_u03b1_4807_: *mut LeanObject,
    mut v_m_4808_: *mut LeanObject,
    mut v_00_u03b2_4809_: *mut LeanObject,
    mut v_inst_4810_: *mut LeanObject,
    mut v_inst_4811_: *mut LeanObject,
    mut v_inst_4812_: *mut LeanObject,
    mut v_it_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4814_: *mut LeanObject = core::ptr::null_mut();
    v_res_4814_ = l_Std_IterM_Partial_size(
        v_00_u03b1_4807_,
        v_m_4808_,
        v_00_u03b2_4809_,
        v_inst_4810_,
        v_inst_4811_,
        v_inst_4812_,
        v_it_4813_,
    );
    lean_dec(v_inst_4810_);
    return v_res_4814_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Loop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
}
