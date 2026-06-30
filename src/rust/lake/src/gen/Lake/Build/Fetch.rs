// Lean compiler output
// Module: Lake.Build.Fetch
// Imports: Lake.Build.Info Lake.Build.Store Lake.Build.Context Lake.Config.Module Lake.Util.EquipT Lake.Util.Cycle Lake.Build.Infos
use crate::ffi::lean_string_append;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lake::Build::Context::{
    initialize_Lake_Build_Context, runtime_initialize_Lake_Build_Context,
};
use crate::r#gen::Lake::Build::Info::{
    initialize_Lake_Build_Info, runtime_initialize_Lake_Build_Info,
};
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Key::l_Lake_BuildKey_toString;
use crate::r#gen::Lake::Build::Store::{
    initialize_Lake_Build_Store, runtime_initialize_Lake_Build_Store,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_Module_keyword;
use crate::r#gen::Lake::Config::Module::{
    initialize_Lake_Config_Module, runtime_initialize_Lake_Config_Module,
};
use crate::r#gen::Lake::Util::Cycle::{
    initialize_Lake_Util_Cycle, l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg,
    l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg,
    runtime_initialize_Lake_Util_Cycle,
};
use crate::r#gen::Lake::Util::EquipT::{
    initialize_Lake_Util_EquipT, runtime_initialize_Lake_Util_EquipT,
};
pub static l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 32, 0]};
static mut l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_buildCycleError___closed__0_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            98, 117, 105, 108, 100, 32, 99, 121, 99, 108, 101, 32, 100, 101, 116, 101, 99, 116,
            101, 100, 58, 10, 0,
        ],
    };
static mut l_Lake_buildCycleError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildCycleError___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__1_value: leanh::LeanClosureObject<3> =
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
        m_fun: l_ST_Prim_mkRef___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0(
    mut v_pkg_x3f_439_: *mut leanh::LeanObject,
    mut v_x_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_pkg_x3f_439_);
    return v_pkg_x3f_439_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed(
    mut v_pkg_x3f_441_: *mut leanh::LeanObject,
    mut v_x_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lake_withCurrPackage_x3f___redArg___lam__0(v_pkg_x3f_441_, v_x_442_);
    leanh::lean_dec(v_x_442_);
    leanh::lean_dec(v_pkg_x3f_441_);
    return v_res_443_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg(
    mut v_inst_444_: *mut leanh::LeanObject,
    mut v_pkg_x3f_445_: *mut leanh::LeanObject,
    mut v_x_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_447_ = leanh::lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_447_, 0, v_pkg_x3f_445_);
    v___x_448_ =
        leanh::lean_apply_3(v_inst_444_, leanh::lean_box(0), v___f_447_, v_x_446_);
    return v___x_448_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f(
    mut v_m_449_: *mut leanh::LeanObject,
    mut v_00_u03b1_450_: *mut leanh::LeanObject,
    mut v_inst_451_: *mut leanh::LeanObject,
    mut v_pkg_x3f_452_: *mut leanh::LeanObject,
    mut v_x_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_454_ = leanh::lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_454_, 0, v_pkg_x3f_452_);
    v___x_455_ =
        leanh::lean_apply_3(v_inst_451_, leanh::lean_box(0), v___f_454_, v_x_453_);
    return v___x_455_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0(
    mut v___x_456_: *mut leanh::LeanObject,
    mut v_x_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_456_);
    return v___x_456_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0___boxed(
    mut v___x_458_: *mut leanh::LeanObject,
    mut v_x_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_460_ = l_Lake_withCurrPackage___redArg___lam__0(v___x_458_, v_x_459_);
    leanh::lean_dec(v_x_459_);
    leanh::lean_dec(v___x_458_);
    return v_res_460_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg(
    mut v_inst_461_: *mut leanh::LeanObject,
    mut v_pkg_462_: *mut leanh::LeanObject,
    mut v_x_463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_464_, 0, v_pkg_462_);
    v___f_465_ = leanh::lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_465_, 0, v___x_464_);
    v___x_466_ =
        leanh::lean_apply_3(v_inst_461_, leanh::lean_box(0), v___f_465_, v_x_463_);
    return v___x_466_;
}
pub unsafe fn l_Lake_withCurrPackage(
    mut v_m_467_: *mut leanh::LeanObject,
    mut v_00_u03b1_468_: *mut leanh::LeanObject,
    mut v_inst_469_: *mut leanh::LeanObject,
    mut v_pkg_470_: *mut leanh::LeanObject,
    mut v_x_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_472_, 0, v_pkg_470_);
    v___f_473_ = leanh::lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_473_, 0, v___x_472_);
    v___x_474_ =
        leanh::lean_apply_3(v_inst_469_, leanh::lean_box(0), v___f_473_, v_x_471_);
    return v___x_474_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg(
    mut v_inst_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_475_);
    return v_inst_475_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg___boxed(
    mut v_inst_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Lake_getCurrPackage_x3f___redArg(v_inst_476_);
    leanh::lean_dec(v_inst_476_);
    return v_res_477_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f(
    mut v_m_478_: *mut leanh::LeanObject,
    mut v_inst_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_479_);
    return v_inst_479_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___boxed(
    mut v_m_480_: *mut leanh::LeanObject,
    mut v_inst_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lake_getCurrPackage_x3f(v_m_480_, v_inst_481_);
    leanh::lean_dec(v_inst_481_);
    return v_res_482_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_484_) == 0 {
                    v___x_486_ = l_List_reverse___redArg(v_a_485_);
                    return v___x_486_;
                } else {
                    v_head_487_ = leanh::lean_ctor_get(v_a_484_, 0);
                    v_tail_488_ = leanh::lean_ctor_get(v_a_484_, 1);
                    v_isSharedCheck_499_ = (!leanh::lean_is_exclusive(v_a_484_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_490_ = v_a_484_;
                        v_isShared_491_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_488_);
                        leanh::lean_inc(v_head_487_);
                        leanh::lean_dec(v_a_484_);
                        v___x_490_ = leanh::lean_box(0);
                        v_isShared_491_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_492_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0;
                v___x_493_ = l_Lake_BuildKey_toString(v_head_487_);
                v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
                leanh::lean_dec_ref(v___x_493_);
                if v_isShared_491_ == 0 {
                    leanh::lean_ctor_set(v___x_490_, 1, v_a_485_);
                    leanh::lean_ctor_set(v___x_490_, 0, v___x_494_);
                    v___x_496_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_498_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_498_, 1, v_a_485_);
                    v___x_496_ = v_reuseFailAlloc_498_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_484_ = v_tail_488_;
                v_a_485_ = v___x_496_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(
    mut v_cycle_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0;
    v___x_503_ = leanh::lean_box(0);
    v___x_504_ =
        l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
            v_cycle_501_,
            v___x_503_,
        );
    v___x_505_ = l_String_intercalate(v___x_502_, v___x_504_);
    return v___x_505_;
}
pub unsafe fn l_Lake_buildCycleError(
    mut v_cycle_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ = l_Lake_buildCycleError___closed__0;
    v___x_509_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(v_cycle_507_);
    v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
    leanh::lean_dec_ref(v___x_509_);
    return v___x_510_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
    mut v_inst_511_: *mut leanh::LeanObject,
    mut v_00_u03b1_512_: *mut leanh::LeanObject,
    mut v_cycle_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
    mut v___y_515_: *mut leanh::LeanObject,
    mut v___y_516_: *mut leanh::LeanObject,
    mut v___y_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Lake_buildCycleError(v_cycle_513_);
    v___x_519_ = leanh::lean_apply_2(v_inst_511_, leanh::lean_box(0), v___x_518_);
    return v___x_519_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed(
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v_00_u03b1_521_: *mut leanh::LeanObject,
    mut v_cycle_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
    mut v___y_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
    mut v___y_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
        v_inst_520_,
        v_00_u03b1_521_,
        v_cycle_522_,
        v___y_523_,
        v___y_524_,
        v___y_525_,
        v___y_526_,
    );
    leanh::lean_dec_ref(v___y_526_);
    leanh::lean_dec(v___y_525_);
    leanh::lean_dec(v___y_524_);
    leanh::lean_dec(v___y_523_);
    return v_res_527_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
    mut v_inst_530_: *mut leanh::LeanObject,
    mut v_inst_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_532_ = leanh::lean_alloc_closure(
        l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_532_, 0, v_inst_531_);
    v___f_533_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0;
    v___f_534_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1;
    v___x_535_ = l_ReaderT_instMonad___redArg(v_inst_530_);
    v___x_536_ = l_StateRefT_x27_instMonad___redArg(v___x_535_);
    v___x_537_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_536_);
    v___x_538_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
        v___f_533_, v___f_534_, v___x_537_,
    );
    v___x_539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
    leanh::lean_ctor_set(v___x_539_, 1, v___f_532_);
    return v___x_539_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(
    mut v_m_540_: *mut leanh::LeanObject,
    mut v_inst_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
        v_inst_541_,
        v_inst_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__0(
    mut v_toApplicative_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_547_ = leanh::lean_ctor_get(v_toApplicative_544_, 1);
    leanh::lean_inc(v_toPure_547_);
    leanh::lean_dec_ref(v_toApplicative_544_);
    v___x_548_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_548_, 0, v_a_545_);
    leanh::lean_ctor_set(v___x_548_, 1, v_a_546_);
    v___x_549_ = leanh::lean_apply_2(v_toPure_547_, leanh::lean_box(0), v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__1(
    mut v_toApplicative_550_: *mut leanh::LeanObject,
    mut v_a_551_: *mut leanh::LeanObject,
    mut v_inst_552_: *mut leanh::LeanObject,
    mut v_toBind_553_: *mut leanh::LeanObject,
    mut v_a_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_555_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_555_, 0, v_toApplicative_550_);
    leanh::lean_closure_set(v___f_555_, 1, v_a_554_);
    v___x_556_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_556_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_556_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_556_, 2, v_a_551_);
    v___x_557_ = leanh::lean_apply_2(v_inst_552_, leanh::lean_box(0), v___x_556_);
    v___x_558_ = leanh::lean_apply_4(
        v_toBind_553_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_557_,
        v___f_555_,
    );
    return v___x_558_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2(
    mut v_toApplicative_559_: *mut leanh::LeanObject,
    mut v_inst_560_: *mut leanh::LeanObject,
    mut v_toBind_561_: *mut leanh::LeanObject,
    mut v_build_562_: *mut leanh::LeanObject,
    mut v___x_563_: *mut leanh::LeanObject,
    mut v_stack_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
    mut v_a_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_561_);
    leanh::lean_inc(v_a_566_);
    v___f_567_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_567_, 0, v_toApplicative_559_);
    leanh::lean_closure_set(v___f_567_, 1, v_a_566_);
    leanh::lean_closure_set(v___f_567_, 2, v_inst_560_);
    leanh::lean_closure_set(v___f_567_, 3, v_toBind_561_);
    leanh::lean_inc_ref(v_a_565_);
    v___x_568_ =
        leanh::lean_apply_4(v_build_562_, v___x_563_, v_stack_564_, v_a_566_, v_a_565_);
    v___x_569_ = leanh::lean_apply_4(
        v_toBind_561_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_568_,
        v___f_567_,
    );
    return v___x_569_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2___boxed(
    mut v_toApplicative_570_: *mut leanh::LeanObject,
    mut v_inst_571_: *mut leanh::LeanObject,
    mut v_toBind_572_: *mut leanh::LeanObject,
    mut v_build_573_: *mut leanh::LeanObject,
    mut v___x_574_: *mut leanh::LeanObject,
    mut v_stack_575_: *mut leanh::LeanObject,
    mut v_a_576_: *mut leanh::LeanObject,
    mut v_a_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lake_RecBuildT_run___redArg___lam__2(
        v_toApplicative_570_,
        v_inst_571_,
        v_toBind_572_,
        v_build_573_,
        v___x_574_,
        v_stack_575_,
        v_a_576_,
        v_a_577_,
    );
    leanh::lean_dec_ref(v_a_576_);
    return v_res_578_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg(
    mut v_inst_579_: *mut leanh::LeanObject,
    mut v_inst_580_: *mut leanh::LeanObject,
    mut v_stack_581_: *mut leanh::LeanObject,
    mut v_store_582_: *mut leanh::LeanObject,
    mut v_build_583_: *mut leanh::LeanObject,
    mut v_a_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_585_ = leanh::lean_ctor_get(v_inst_579_, 0);
    leanh::lean_inc_ref(v_toApplicative_585_);
    v_toBind_586_ = leanh::lean_ctor_get(v_inst_579_, 1);
    leanh::lean_inc_n(v_toBind_586_, 2);
    leanh::lean_dec_ref(v_inst_579_);
    v___x_587_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_a_584_);
    leanh::lean_inc(v_inst_580_);
    v___f_588_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_588_, 0, v_toApplicative_585_);
    leanh::lean_closure_set(v___f_588_, 1, v_inst_580_);
    leanh::lean_closure_set(v___f_588_, 2, v_toBind_586_);
    leanh::lean_closure_set(v___f_588_, 3, v_build_583_);
    leanh::lean_closure_set(v___f_588_, 4, v___x_587_);
    leanh::lean_closure_set(v___f_588_, 5, v_stack_581_);
    leanh::lean_closure_set(v___f_588_, 6, v_a_584_);
    v___x_589_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_589_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_589_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_589_, 2, v_store_582_);
    v___x_590_ = leanh::lean_apply_2(v_inst_580_, leanh::lean_box(0), v___x_589_);
    v___x_591_ = leanh::lean_apply_4(
        v_toBind_586_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_590_,
        v___f_588_,
    );
    return v___x_591_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___boxed(
    mut v_inst_592_: *mut leanh::LeanObject,
    mut v_inst_593_: *mut leanh::LeanObject,
    mut v_stack_594_: *mut leanh::LeanObject,
    mut v_store_595_: *mut leanh::LeanObject,
    mut v_build_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lake_RecBuildT_run___redArg(
        v_inst_592_,
        v_inst_593_,
        v_stack_594_,
        v_store_595_,
        v_build_596_,
        v_a_597_,
    );
    leanh::lean_dec_ref(v_a_597_);
    return v_res_598_;
}
pub unsafe fn l_Lake_RecBuildT_run(
    mut v_m_599_: *mut leanh::LeanObject,
    mut v_00_u03b1_600_: *mut leanh::LeanObject,
    mut v_inst_601_: *mut leanh::LeanObject,
    mut v_inst_602_: *mut leanh::LeanObject,
    mut v_stack_603_: *mut leanh::LeanObject,
    mut v_store_604_: *mut leanh::LeanObject,
    mut v_build_605_: *mut leanh::LeanObject,
    mut v_a_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_607_ = leanh::lean_ctor_get(v_inst_601_, 0);
    leanh::lean_inc_ref(v_toApplicative_607_);
    v_toBind_608_ = leanh::lean_ctor_get(v_inst_601_, 1);
    leanh::lean_inc_n(v_toBind_608_, 2);
    leanh::lean_dec_ref(v_inst_601_);
    v___x_609_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_a_606_);
    leanh::lean_inc(v_inst_602_);
    v___f_610_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_610_, 0, v_toApplicative_607_);
    leanh::lean_closure_set(v___f_610_, 1, v_inst_602_);
    leanh::lean_closure_set(v___f_610_, 2, v_toBind_608_);
    leanh::lean_closure_set(v___f_610_, 3, v_build_605_);
    leanh::lean_closure_set(v___f_610_, 4, v___x_609_);
    leanh::lean_closure_set(v___f_610_, 5, v_stack_603_);
    leanh::lean_closure_set(v___f_610_, 6, v_a_606_);
    v___x_611_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_611_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_611_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_611_, 2, v_store_604_);
    v___x_612_ = leanh::lean_apply_2(v_inst_602_, leanh::lean_box(0), v___x_611_);
    v___x_613_ = leanh::lean_apply_4(
        v_toBind_608_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_612_,
        v___f_610_,
    );
    return v___x_613_;
}
pub unsafe fn l_Lake_RecBuildT_run___boxed(
    mut v_m_614_: *mut leanh::LeanObject,
    mut v_00_u03b1_615_: *mut leanh::LeanObject,
    mut v_inst_616_: *mut leanh::LeanObject,
    mut v_inst_617_: *mut leanh::LeanObject,
    mut v_stack_618_: *mut leanh::LeanObject,
    mut v_store_619_: *mut leanh::LeanObject,
    mut v_build_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lake_RecBuildT_run(
        v_m_614_,
        v_00_u03b1_615_,
        v_inst_616_,
        v_inst_617_,
        v_stack_618_,
        v_store_619_,
        v_build_620_,
        v_a_621_,
    );
    leanh::lean_dec_ref(v_a_621_);
    return v_res_622_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0(
    mut v_x_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_624_ = leanh::lean_ctor_get(v_x_623_, 0);
    leanh::lean_inc(v_fst_624_);
    return v_fst_624_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(
    mut v_x_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lake_RecBuildT_run_x27___redArg___lam__0(v_x_625_);
    leanh::lean_dec_ref(v_x_625_);
    return v_res_626_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__1(
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_toPure_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_630_, 0, v_a_627_);
    leanh::lean_ctor_set(v___x_630_, 1, v_a_629_);
    v___x_631_ = leanh::lean_apply_2(v_toPure_628_, leanh::lean_box(0), v___x_630_);
    return v___x_631_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__2(
    mut v_toPure_632_: *mut leanh::LeanObject,
    mut v_a_633_: *mut leanh::LeanObject,
    mut v_inst_634_: *mut leanh::LeanObject,
    mut v_toBind_635_: *mut leanh::LeanObject,
    mut v_a_636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_637_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_637_, 0, v_a_636_);
    leanh::lean_closure_set(v___f_637_, 1, v_toPure_632_);
    v___x_638_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_638_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_638_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_638_, 2, v_a_633_);
    v___x_639_ = leanh::lean_apply_2(v_inst_634_, leanh::lean_box(0), v___x_638_);
    v___x_640_ = leanh::lean_apply_4(
        v_toBind_635_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_639_,
        v___f_637_,
    );
    return v___x_640_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3(
    mut v_toPure_641_: *mut leanh::LeanObject,
    mut v_inst_642_: *mut leanh::LeanObject,
    mut v_toBind_643_: *mut leanh::LeanObject,
    mut v_build_644_: *mut leanh::LeanObject,
    mut v___x_645_: *mut leanh::LeanObject,
    mut v___x_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_643_);
    leanh::lean_inc(v_a_648_);
    v___f_649_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_649_, 0, v_toPure_641_);
    leanh::lean_closure_set(v___f_649_, 1, v_a_648_);
    leanh::lean_closure_set(v___f_649_, 2, v_inst_642_);
    leanh::lean_closure_set(v___f_649_, 3, v_toBind_643_);
    leanh::lean_inc_ref(v_a_647_);
    v___x_650_ =
        leanh::lean_apply_4(v_build_644_, v___x_645_, v___x_646_, v_a_648_, v_a_647_);
    v___x_651_ = leanh::lean_apply_4(
        v_toBind_643_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_650_,
        v___f_649_,
    );
    return v___x_651_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed(
    mut v_toPure_652_: *mut leanh::LeanObject,
    mut v_inst_653_: *mut leanh::LeanObject,
    mut v_toBind_654_: *mut leanh::LeanObject,
    mut v_build_655_: *mut leanh::LeanObject,
    mut v___x_656_: *mut leanh::LeanObject,
    mut v___x_657_: *mut leanh::LeanObject,
    mut v_a_658_: *mut leanh::LeanObject,
    mut v_a_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lake_RecBuildT_run_x27___redArg___lam__3(
        v_toPure_652_,
        v_inst_653_,
        v_toBind_654_,
        v_build_655_,
        v___x_656_,
        v___x_657_,
        v_a_658_,
        v_a_659_,
    );
    leanh::lean_dec_ref(v_a_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg(
    mut v_inst_664_: *mut leanh::LeanObject,
    mut v_inst_665_: *mut leanh::LeanObject,
    mut v_build_666_: *mut leanh::LeanObject,
    mut v_a_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_668_ = leanh::lean_ctor_get(v_inst_664_, 0);
    leanh::lean_inc_ref(v_toApplicative_668_);
    v_toFunctor_669_ = leanh::lean_ctor_get(v_toApplicative_668_, 0);
    leanh::lean_inc_ref(v_toFunctor_669_);
    v_toBind_670_ = leanh::lean_ctor_get(v_inst_664_, 1);
    leanh::lean_inc_n(v_toBind_670_, 2);
    leanh::lean_dec_ref(v_inst_664_);
    v_toPure_671_ = leanh::lean_ctor_get(v_toApplicative_668_, 1);
    leanh::lean_inc(v_toPure_671_);
    leanh::lean_dec_ref(v_toApplicative_668_);
    v_map_672_ = leanh::lean_ctor_get(v_toFunctor_669_, 0);
    leanh::lean_inc(v_map_672_);
    leanh::lean_dec_ref(v_toFunctor_669_);
    v___f_673_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_674_ = leanh::lean_box(0);
    v___x_675_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_a_667_);
    leanh::lean_inc(v_inst_665_);
    v___f_676_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_676_, 0, v_toPure_671_);
    leanh::lean_closure_set(v___f_676_, 1, v_inst_665_);
    leanh::lean_closure_set(v___f_676_, 2, v_toBind_670_);
    leanh::lean_closure_set(v___f_676_, 3, v_build_666_);
    leanh::lean_closure_set(v___f_676_, 4, v___x_675_);
    leanh::lean_closure_set(v___f_676_, 5, v___x_674_);
    leanh::lean_closure_set(v___f_676_, 6, v_a_667_);
    v___x_677_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_678_ = leanh::lean_apply_2(v_inst_665_, leanh::lean_box(0), v___x_677_);
    v___x_679_ = leanh::lean_apply_4(
        v_toBind_670_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_678_,
        v___f_676_,
    );
    v___x_680_ = leanh::lean_apply_4(
        v_map_672_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_673_,
        v___x_679_,
    );
    return v___x_680_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___boxed(
    mut v_inst_681_: *mut leanh::LeanObject,
    mut v_inst_682_: *mut leanh::LeanObject,
    mut v_build_683_: *mut leanh::LeanObject,
    mut v_a_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_685_ =
        l_Lake_RecBuildT_run_x27___redArg(v_inst_681_, v_inst_682_, v_build_683_, v_a_684_);
    leanh::lean_dec_ref(v_a_684_);
    return v_res_685_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27(
    mut v_m_686_: *mut leanh::LeanObject,
    mut v_00_u03b1_687_: *mut leanh::LeanObject,
    mut v_inst_688_: *mut leanh::LeanObject,
    mut v_inst_689_: *mut leanh::LeanObject,
    mut v_build_690_: *mut leanh::LeanObject,
    mut v_a_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_692_ = leanh::lean_ctor_get(v_inst_688_, 0);
    leanh::lean_inc_ref(v_toApplicative_692_);
    v_toFunctor_693_ = leanh::lean_ctor_get(v_toApplicative_692_, 0);
    leanh::lean_inc_ref(v_toFunctor_693_);
    v_toBind_694_ = leanh::lean_ctor_get(v_inst_688_, 1);
    leanh::lean_inc_n(v_toBind_694_, 2);
    leanh::lean_dec_ref(v_inst_688_);
    v_toPure_695_ = leanh::lean_ctor_get(v_toApplicative_692_, 1);
    leanh::lean_inc(v_toPure_695_);
    leanh::lean_dec_ref(v_toApplicative_692_);
    v_map_696_ = leanh::lean_ctor_get(v_toFunctor_693_, 0);
    leanh::lean_inc(v_map_696_);
    leanh::lean_dec_ref(v_toFunctor_693_);
    v___f_697_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_698_ = leanh::lean_box(0);
    v___x_699_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_a_691_);
    leanh::lean_inc(v_inst_689_);
    v___f_700_ = leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_700_, 0, v_toPure_695_);
    leanh::lean_closure_set(v___f_700_, 1, v_inst_689_);
    leanh::lean_closure_set(v___f_700_, 2, v_toBind_694_);
    leanh::lean_closure_set(v___f_700_, 3, v_build_690_);
    leanh::lean_closure_set(v___f_700_, 4, v___x_699_);
    leanh::lean_closure_set(v___f_700_, 5, v___x_698_);
    leanh::lean_closure_set(v___f_700_, 6, v_a_691_);
    v___x_701_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_702_ = leanh::lean_apply_2(v_inst_689_, leanh::lean_box(0), v___x_701_);
    v___x_703_ = leanh::lean_apply_4(
        v_toBind_694_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_702_,
        v___f_700_,
    );
    v___x_704_ = leanh::lean_apply_4(
        v_map_696_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_697_,
        v___x_703_,
    );
    return v___x_704_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___boxed(
    mut v_m_705_: *mut leanh::LeanObject,
    mut v_00_u03b1_706_: *mut leanh::LeanObject,
    mut v_inst_707_: *mut leanh::LeanObject,
    mut v_inst_708_: *mut leanh::LeanObject,
    mut v_build_709_: *mut leanh::LeanObject,
    mut v_a_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_711_ = l_Lake_RecBuildT_run_x27(
        v_m_705_,
        v_00_u03b1_706_,
        v_inst_707_,
        v_inst_708_,
        v_build_709_,
        v_a_710_,
    );
    leanh::lean_dec_ref(v_a_710_);
    return v_res_711_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg(
    mut v_f_712_: *mut leanh::LeanObject,
    mut v_a_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_a_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_717_);
    leanh::lean_inc(v_a_716_);
    leanh::lean_inc(v_a_715_);
    leanh::lean_inc(v_a_714_);
    v___x_720_ = leanh::lean_apply_7(
        v_f_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
        v_a_716_,
        v_a_717_,
        v_a_718_,
        leanh::lean_box(0),
    );
    return v___x_720_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg___boxed(
    mut v_f_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_a_723_: *mut leanh::LeanObject,
    mut v_a_724_: *mut leanh::LeanObject,
    mut v_a_725_: *mut leanh::LeanObject,
    mut v_a_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
    mut v_a_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lake_FetchM_ofFn___redArg(
        v_f_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_,
    );
    leanh::lean_dec_ref(v_a_726_);
    leanh::lean_dec(v_a_725_);
    leanh::lean_dec(v_a_724_);
    leanh::lean_dec(v_a_723_);
    return v_res_729_;
}
pub unsafe fn l_Lake_FetchM_ofFn(
    mut v_00_u03b1_730_: *mut leanh::LeanObject,
    mut v_f_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
    mut v_a_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_736_);
    leanh::lean_inc(v_a_735_);
    leanh::lean_inc(v_a_734_);
    leanh::lean_inc(v_a_733_);
    v___x_739_ = leanh::lean_apply_7(
        v_f_731_,
        v_a_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
        v_a_737_,
        leanh::lean_box(0),
    );
    return v___x_739_;
}
pub unsafe fn l_Lake_FetchM_ofFn___boxed(
    mut v_00_u03b1_740_: *mut leanh::LeanObject,
    mut v_f_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
    mut v_a_744_: *mut leanh::LeanObject,
    mut v_a_745_: *mut leanh::LeanObject,
    mut v_a_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lake_FetchM_ofFn(
        v_00_u03b1_740_,
        v_f_741_,
        v_a_742_,
        v_a_743_,
        v_a_744_,
        v_a_745_,
        v_a_746_,
        v_a_747_,
    );
    leanh::lean_dec_ref(v_a_746_);
    leanh::lean_dec(v_a_745_);
    leanh::lean_dec(v_a_744_);
    leanh::lean_dec(v_a_743_);
    return v_res_749_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg(
    mut v_self_750_: *mut leanh::LeanObject,
    mut v_fetch_751_: *mut leanh::LeanObject,
    mut v_pkg_x3f_752_: *mut leanh::LeanObject,
    mut v_stack_753_: *mut leanh::LeanObject,
    mut v_store_754_: *mut leanh::LeanObject,
    mut v_ctx_755_: *mut leanh::LeanObject,
    mut v_log_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = leanh::lean_apply_7(
        v_self_750_,
        v_fetch_751_,
        v_pkg_x3f_752_,
        v_stack_753_,
        v_store_754_,
        v_ctx_755_,
        v_log_756_,
        leanh::lean_box(0),
    );
    return v___x_758_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg___boxed(
    mut v_self_759_: *mut leanh::LeanObject,
    mut v_fetch_760_: *mut leanh::LeanObject,
    mut v_pkg_x3f_761_: *mut leanh::LeanObject,
    mut v_stack_762_: *mut leanh::LeanObject,
    mut v_store_763_: *mut leanh::LeanObject,
    mut v_ctx_764_: *mut leanh::LeanObject,
    mut v_log_765_: *mut leanh::LeanObject,
    mut v_a_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lake_FetchM_toFn___redArg(
        v_self_759_,
        v_fetch_760_,
        v_pkg_x3f_761_,
        v_stack_762_,
        v_store_763_,
        v_ctx_764_,
        v_log_765_,
    );
    return v_res_767_;
}
pub unsafe fn l_Lake_FetchM_toFn(
    mut v_00_u03b1_768_: *mut leanh::LeanObject,
    mut v_self_769_: *mut leanh::LeanObject,
    mut v_fetch_770_: *mut leanh::LeanObject,
    mut v_pkg_x3f_771_: *mut leanh::LeanObject,
    mut v_stack_772_: *mut leanh::LeanObject,
    mut v_store_773_: *mut leanh::LeanObject,
    mut v_ctx_774_: *mut leanh::LeanObject,
    mut v_log_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = leanh::lean_apply_7(
        v_self_769_,
        v_fetch_770_,
        v_pkg_x3f_771_,
        v_stack_772_,
        v_store_773_,
        v_ctx_774_,
        v_log_775_,
        leanh::lean_box(0),
    );
    return v___x_777_;
}
pub unsafe fn l_Lake_FetchM_toFn___boxed(
    mut v_00_u03b1_778_: *mut leanh::LeanObject,
    mut v_self_779_: *mut leanh::LeanObject,
    mut v_fetch_780_: *mut leanh::LeanObject,
    mut v_pkg_x3f_781_: *mut leanh::LeanObject,
    mut v_stack_782_: *mut leanh::LeanObject,
    mut v_store_783_: *mut leanh::LeanObject,
    mut v_ctx_784_: *mut leanh::LeanObject,
    mut v_log_785_: *mut leanh::LeanObject,
    mut v_a_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lake_FetchM_toFn(
        v_00_u03b1_778_,
        v_self_779_,
        v_fetch_780_,
        v_pkg_x3f_781_,
        v_stack_782_,
        v_store_783_,
        v_ctx_784_,
        v_log_785_,
    );
    return v_res_787_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___redArg(
    mut v_self_788_: *mut leanh::LeanObject,
    mut v_a_789_: *mut leanh::LeanObject,
    mut v_a_790_: *mut leanh::LeanObject,
    mut v_a_791_: *mut leanh::LeanObject,
    mut v_a_792_: *mut leanh::LeanObject,
    mut v_a_793_: *mut leanh::LeanObject,
    mut v_a_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_793_);
    leanh::lean_inc(v_a_792_);
    leanh::lean_inc(v_a_791_);
    leanh::lean_inc(v_a_790_);
    v___x_796_ = leanh::lean_apply_7(
        v_a_789_,
        v_self_788_,
        v_a_790_,
        v_a_791_,
        v_a_792_,
        v_a_793_,
        v_a_794_,
        leanh::lean_box(0),
    );
    return v___x_796_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___redArg___boxed(
    mut v_self_797_: *mut leanh::LeanObject,
    mut v_a_798_: *mut leanh::LeanObject,
    mut v_a_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
    mut v_a_801_: *mut leanh::LeanObject,
    mut v_a_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lake_BuildInfo_fetch___redArg(
        v_self_797_,
        v_a_798_,
        v_a_799_,
        v_a_800_,
        v_a_801_,
        v_a_802_,
        v_a_803_,
    );
    leanh::lean_dec_ref(v_a_802_);
    leanh::lean_dec(v_a_801_);
    leanh::lean_dec(v_a_800_);
    leanh::lean_dec(v_a_799_);
    return v_res_805_;
}
pub unsafe fn l_Lake_BuildInfo_fetch(
    mut v_00_u03b1_806_: *mut leanh::LeanObject,
    mut v_self_807_: *mut leanh::LeanObject,
    mut v_inst_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_813_);
    leanh::lean_inc(v_a_812_);
    leanh::lean_inc(v_a_811_);
    leanh::lean_inc(v_a_810_);
    v___x_816_ = leanh::lean_apply_7(
        v_a_809_,
        v_self_807_,
        v_a_810_,
        v_a_811_,
        v_a_812_,
        v_a_813_,
        v_a_814_,
        leanh::lean_box(0),
    );
    return v___x_816_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___boxed(
    mut v_00_u03b1_817_: *mut leanh::LeanObject,
    mut v_self_818_: *mut leanh::LeanObject,
    mut v_inst_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Lake_BuildInfo_fetch(
        v_00_u03b1_817_,
        v_self_818_,
        v_inst_819_,
        v_a_820_,
        v_a_821_,
        v_a_822_,
        v_a_823_,
        v_a_824_,
        v_a_825_,
    );
    leanh::lean_dec_ref(v_a_824_);
    leanh::lean_dec(v_a_823_);
    leanh::lean_dec(v_a_822_);
    leanh::lean_dec(v_a_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg(
    mut v_self_828_: *mut leanh::LeanObject,
    mut v_mod_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
    mut v_a_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_837_ = leanh::lean_ctor_get(v_mod_829_, 0);
    v_pkg_838_ = leanh::lean_ctor_get(v_lib_837_, 0);
    v_name_839_ = leanh::lean_ctor_get(v_mod_829_, 1);
    v_keyName_840_ = leanh::lean_ctor_get(v_pkg_838_, 2);
    leanh::lean_inc(v_name_839_);
    leanh::lean_inc(v_keyName_840_);
    v___x_841_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_841_, 0, v_keyName_840_);
    leanh::lean_ctor_set(v___x_841_, 1, v_name_839_);
    v___x_842_ = l_Lake_Module_keyword;
    v___x_843_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_843_, 0, v___x_841_);
    leanh::lean_ctor_set(v___x_843_, 1, v___x_842_);
    leanh::lean_ctor_set(v___x_843_, 2, v_mod_829_);
    leanh::lean_ctor_set(v___x_843_, 3, v_self_828_);
    leanh::lean_inc_ref(v_a_834_);
    leanh::lean_inc(v_a_833_);
    leanh::lean_inc(v_a_832_);
    leanh::lean_inc(v_a_831_);
    v___x_844_ = leanh::lean_apply_7(
        v_a_830_,
        v___x_843_,
        v_a_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
        v_a_835_,
        leanh::lean_box(0),
    );
    return v___x_844_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg___boxed(
    mut v_self_845_: *mut leanh::LeanObject,
    mut v_mod_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lake_ModuleFacet_fetch___redArg(
        v_self_845_,
        v_mod_846_,
        v_a_847_,
        v_a_848_,
        v_a_849_,
        v_a_850_,
        v_a_851_,
        v_a_852_,
    );
    leanh::lean_dec_ref(v_a_851_);
    leanh::lean_dec(v_a_850_);
    leanh::lean_dec(v_a_849_);
    leanh::lean_dec(v_a_848_);
    return v_res_854_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch(
    mut v_00_u03b1_855_: *mut leanh::LeanObject,
    mut v_self_856_: *mut leanh::LeanObject,
    mut v_mod_857_: *mut leanh::LeanObject,
    mut v_a_858_: *mut leanh::LeanObject,
    mut v_a_859_: *mut leanh::LeanObject,
    mut v_a_860_: *mut leanh::LeanObject,
    mut v_a_861_: *mut leanh::LeanObject,
    mut v_a_862_: *mut leanh::LeanObject,
    mut v_a_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Lake_ModuleFacet_fetch___redArg(
        v_self_856_,
        v_mod_857_,
        v_a_858_,
        v_a_859_,
        v_a_860_,
        v_a_861_,
        v_a_862_,
        v_a_863_,
    );
    return v___x_865_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___boxed(
    mut v_00_u03b1_866_: *mut leanh::LeanObject,
    mut v_self_867_: *mut leanh::LeanObject,
    mut v_mod_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
    mut v_a_873_: *mut leanh::LeanObject,
    mut v_a_874_: *mut leanh::LeanObject,
    mut v_a_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_876_ = l_Lake_ModuleFacet_fetch(
        v_00_u03b1_866_,
        v_self_867_,
        v_mod_868_,
        v_a_869_,
        v_a_870_,
        v_a_871_,
        v_a_872_,
        v_a_873_,
        v_a_874_,
    );
    leanh::lean_dec_ref(v_a_873_);
    leanh::lean_dec(v_a_872_);
    leanh::lean_dec(v_a_871_);
    leanh::lean_dec(v_a_870_);
    return v_res_876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Fetch(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Store(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Fetch(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Fetch(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Store(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Cycle(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Fetch(builtin);
}