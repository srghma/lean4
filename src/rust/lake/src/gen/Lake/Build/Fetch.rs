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
pub static l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 32, 0]};
static mut l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_buildCycleError___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_buildCycleError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildCycleError___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__1_value: crate::leanh::LeanClosureObject<3> =
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
        m_fun: l_ST_Prim_mkRef___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0(
    mut v_pkg_x3f_439_: *mut crate::leanh::LeanObject,
    mut v_x_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pkg_x3f_439_);
    return v_pkg_x3f_439_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed(
    mut v_pkg_x3f_441_: *mut crate::leanh::LeanObject,
    mut v_x_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lake_withCurrPackage_x3f___redArg___lam__0(v_pkg_x3f_441_, v_x_442_);
    crate::leanh::lean_dec(v_x_442_);
    crate::leanh::lean_dec(v_pkg_x3f_441_);
    return v_res_443_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg(
    mut v_inst_444_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_445_: *mut crate::leanh::LeanObject,
    mut v_x_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_447_ = crate::leanh::lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_447_, 0, v_pkg_x3f_445_);
    v___x_448_ =
        crate::leanh::lean_apply_3(v_inst_444_, crate::leanh::lean_box(0), v___f_447_, v_x_446_);
    return v___x_448_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f(
    mut v_m_449_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_450_: *mut crate::leanh::LeanObject,
    mut v_inst_451_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_452_: *mut crate::leanh::LeanObject,
    mut v_x_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_454_ = crate::leanh::lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_454_, 0, v_pkg_x3f_452_);
    v___x_455_ =
        crate::leanh::lean_apply_3(v_inst_451_, crate::leanh::lean_box(0), v___f_454_, v_x_453_);
    return v___x_455_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0(
    mut v___x_456_: *mut crate::leanh::LeanObject,
    mut v_x_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_456_);
    return v___x_456_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0___boxed(
    mut v___x_458_: *mut crate::leanh::LeanObject,
    mut v_x_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_460_ = l_Lake_withCurrPackage___redArg___lam__0(v___x_458_, v_x_459_);
    crate::leanh::lean_dec(v_x_459_);
    crate::leanh::lean_dec(v___x_458_);
    return v_res_460_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg(
    mut v_inst_461_: *mut crate::leanh::LeanObject,
    mut v_pkg_462_: *mut crate::leanh::LeanObject,
    mut v_x_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_464_, 0, v_pkg_462_);
    v___f_465_ = crate::leanh::lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_465_, 0, v___x_464_);
    v___x_466_ =
        crate::leanh::lean_apply_3(v_inst_461_, crate::leanh::lean_box(0), v___f_465_, v_x_463_);
    return v___x_466_;
}
pub unsafe fn l_Lake_withCurrPackage(
    mut v_m_467_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_468_: *mut crate::leanh::LeanObject,
    mut v_inst_469_: *mut crate::leanh::LeanObject,
    mut v_pkg_470_: *mut crate::leanh::LeanObject,
    mut v_x_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_472_, 0, v_pkg_470_);
    v___f_473_ = crate::leanh::lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_473_, 0, v___x_472_);
    v___x_474_ =
        crate::leanh::lean_apply_3(v_inst_469_, crate::leanh::lean_box(0), v___f_473_, v_x_471_);
    return v___x_474_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg(
    mut v_inst_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_475_);
    return v_inst_475_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg___boxed(
    mut v_inst_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Lake_getCurrPackage_x3f___redArg(v_inst_476_);
    crate::leanh::lean_dec(v_inst_476_);
    return v_res_477_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f(
    mut v_m_478_: *mut crate::leanh::LeanObject,
    mut v_inst_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_479_);
    return v_inst_479_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___boxed(
    mut v_m_480_: *mut crate::leanh::LeanObject,
    mut v_inst_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lake_getCurrPackage_x3f(v_m_480_, v_inst_481_);
    crate::leanh::lean_dec(v_inst_481_);
    return v_res_482_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
    mut v_a_484_: *mut crate::leanh::LeanObject,
    mut v_a_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_484_) == 0 {
                    v___x_486_ = l_List_reverse___redArg(v_a_485_);
                    return v___x_486_;
                } else {
                    v_head_487_ = crate::leanh::lean_ctor_get(v_a_484_, 0);
                    v_tail_488_ = crate::leanh::lean_ctor_get(v_a_484_, 1);
                    v_isSharedCheck_499_ = (!crate::leanh::lean_is_exclusive(v_a_484_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_490_ = v_a_484_;
                        v_isShared_491_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_488_);
                        crate::leanh::lean_inc(v_head_487_);
                        crate::leanh::lean_dec(v_a_484_);
                        v___x_490_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v___x_493_);
                if v_isShared_491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_490_, 1, v_a_485_);
                    crate::leanh::lean_ctor_set(v___x_490_, 0, v___x_494_);
                    v___x_496_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_498_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 1, v_a_485_);
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
    mut v_cycle_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0;
    v___x_503_ = crate::leanh::lean_box(0);
    v___x_504_ =
        l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
            v_cycle_501_,
            v___x_503_,
        );
    v___x_505_ = l_String_intercalate(v___x_502_, v___x_504_);
    return v___x_505_;
}
pub unsafe fn l_Lake_buildCycleError(
    mut v_cycle_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ = l_Lake_buildCycleError___closed__0;
    v___x_509_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(v_cycle_507_);
    v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
    crate::leanh::lean_dec_ref(v___x_509_);
    return v___x_510_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
    mut v_inst_511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_512_: *mut crate::leanh::LeanObject,
    mut v_cycle_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
    mut v___y_516_: *mut crate::leanh::LeanObject,
    mut v___y_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Lake_buildCycleError(v_cycle_513_);
    v___x_519_ = crate::leanh::lean_apply_2(v_inst_511_, crate::leanh::lean_box(0), v___x_518_);
    return v___x_519_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed(
    mut v_inst_520_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_521_: *mut crate::leanh::LeanObject,
    mut v_cycle_522_: *mut crate::leanh::LeanObject,
    mut v___y_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
        v_inst_520_,
        v_00_u03b1_521_,
        v_cycle_522_,
        v___y_523_,
        v___y_524_,
        v___y_525_,
        v___y_526_,
    );
    crate::leanh::lean_dec_ref(v___y_526_);
    crate::leanh::lean_dec(v___y_525_);
    crate::leanh::lean_dec(v___y_524_);
    crate::leanh::lean_dec(v___y_523_);
    return v_res_527_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
    mut v_inst_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_532_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_532_, 0, v_inst_531_);
    v___f_533_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0;
    v___f_534_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1;
    v___x_535_ = l_ReaderT_instMonad___redArg(v_inst_530_);
    v___x_536_ = l_StateRefT_x27_instMonad___redArg(v___x_535_);
    v___x_537_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_536_);
    v___x_538_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
        v___f_533_, v___f_534_, v___x_537_,
    );
    v___x_539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
    crate::leanh::lean_ctor_set(v___x_539_, 1, v___f_532_);
    return v___x_539_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(
    mut v_m_540_: *mut crate::leanh::LeanObject,
    mut v_inst_541_: *mut crate::leanh::LeanObject,
    mut v_inst_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
        v_inst_541_,
        v_inst_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__0(
    mut v_toApplicative_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_547_ = crate::leanh::lean_ctor_get(v_toApplicative_544_, 1);
    crate::leanh::lean_inc(v_toPure_547_);
    crate::leanh::lean_dec_ref(v_toApplicative_544_);
    v___x_548_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_548_, 0, v_a_545_);
    crate::leanh::lean_ctor_set(v___x_548_, 1, v_a_546_);
    v___x_549_ = crate::leanh::lean_apply_2(v_toPure_547_, crate::leanh::lean_box(0), v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__1(
    mut v_toApplicative_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_inst_552_: *mut crate::leanh::LeanObject,
    mut v_toBind_553_: *mut crate::leanh::LeanObject,
    mut v_a_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_555_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_555_, 0, v_toApplicative_550_);
    crate::leanh::lean_closure_set(v___f_555_, 1, v_a_554_);
    v___x_556_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_556_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_556_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_556_, 2, v_a_551_);
    v___x_557_ = crate::leanh::lean_apply_2(v_inst_552_, crate::leanh::lean_box(0), v___x_556_);
    v___x_558_ = crate::leanh::lean_apply_4(
        v_toBind_553_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_557_,
        v___f_555_,
    );
    return v___x_558_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2(
    mut v_toApplicative_559_: *mut crate::leanh::LeanObject,
    mut v_inst_560_: *mut crate::leanh::LeanObject,
    mut v_toBind_561_: *mut crate::leanh::LeanObject,
    mut v_build_562_: *mut crate::leanh::LeanObject,
    mut v___x_563_: *mut crate::leanh::LeanObject,
    mut v_stack_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_561_);
    crate::leanh::lean_inc(v_a_566_);
    v___f_567_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_567_, 0, v_toApplicative_559_);
    crate::leanh::lean_closure_set(v___f_567_, 1, v_a_566_);
    crate::leanh::lean_closure_set(v___f_567_, 2, v_inst_560_);
    crate::leanh::lean_closure_set(v___f_567_, 3, v_toBind_561_);
    crate::leanh::lean_inc_ref(v_a_565_);
    v___x_568_ =
        crate::leanh::lean_apply_4(v_build_562_, v___x_563_, v_stack_564_, v_a_566_, v_a_565_);
    v___x_569_ = crate::leanh::lean_apply_4(
        v_toBind_561_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_568_,
        v___f_567_,
    );
    return v___x_569_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2___boxed(
    mut v_toApplicative_570_: *mut crate::leanh::LeanObject,
    mut v_inst_571_: *mut crate::leanh::LeanObject,
    mut v_toBind_572_: *mut crate::leanh::LeanObject,
    mut v_build_573_: *mut crate::leanh::LeanObject,
    mut v___x_574_: *mut crate::leanh::LeanObject,
    mut v_stack_575_: *mut crate::leanh::LeanObject,
    mut v_a_576_: *mut crate::leanh::LeanObject,
    mut v_a_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_576_);
    return v_res_578_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg(
    mut v_inst_579_: *mut crate::leanh::LeanObject,
    mut v_inst_580_: *mut crate::leanh::LeanObject,
    mut v_stack_581_: *mut crate::leanh::LeanObject,
    mut v_store_582_: *mut crate::leanh::LeanObject,
    mut v_build_583_: *mut crate::leanh::LeanObject,
    mut v_a_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_585_ = crate::leanh::lean_ctor_get(v_inst_579_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_585_);
    v_toBind_586_ = crate::leanh::lean_ctor_get(v_inst_579_, 1);
    crate::leanh::lean_inc_n(v_toBind_586_, 2);
    crate::leanh::lean_dec_ref(v_inst_579_);
    v___x_587_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_a_584_);
    crate::leanh::lean_inc(v_inst_580_);
    v___f_588_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_588_, 0, v_toApplicative_585_);
    crate::leanh::lean_closure_set(v___f_588_, 1, v_inst_580_);
    crate::leanh::lean_closure_set(v___f_588_, 2, v_toBind_586_);
    crate::leanh::lean_closure_set(v___f_588_, 3, v_build_583_);
    crate::leanh::lean_closure_set(v___f_588_, 4, v___x_587_);
    crate::leanh::lean_closure_set(v___f_588_, 5, v_stack_581_);
    crate::leanh::lean_closure_set(v___f_588_, 6, v_a_584_);
    v___x_589_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_589_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_589_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_589_, 2, v_store_582_);
    v___x_590_ = crate::leanh::lean_apply_2(v_inst_580_, crate::leanh::lean_box(0), v___x_589_);
    v___x_591_ = crate::leanh::lean_apply_4(
        v_toBind_586_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_590_,
        v___f_588_,
    );
    return v___x_591_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___boxed(
    mut v_inst_592_: *mut crate::leanh::LeanObject,
    mut v_inst_593_: *mut crate::leanh::LeanObject,
    mut v_stack_594_: *mut crate::leanh::LeanObject,
    mut v_store_595_: *mut crate::leanh::LeanObject,
    mut v_build_596_: *mut crate::leanh::LeanObject,
    mut v_a_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lake_RecBuildT_run___redArg(
        v_inst_592_,
        v_inst_593_,
        v_stack_594_,
        v_store_595_,
        v_build_596_,
        v_a_597_,
    );
    crate::leanh::lean_dec_ref(v_a_597_);
    return v_res_598_;
}
pub unsafe fn l_Lake_RecBuildT_run(
    mut v_m_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_600_: *mut crate::leanh::LeanObject,
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_stack_603_: *mut crate::leanh::LeanObject,
    mut v_store_604_: *mut crate::leanh::LeanObject,
    mut v_build_605_: *mut crate::leanh::LeanObject,
    mut v_a_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_607_ = crate::leanh::lean_ctor_get(v_inst_601_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_607_);
    v_toBind_608_ = crate::leanh::lean_ctor_get(v_inst_601_, 1);
    crate::leanh::lean_inc_n(v_toBind_608_, 2);
    crate::leanh::lean_dec_ref(v_inst_601_);
    v___x_609_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_a_606_);
    crate::leanh::lean_inc(v_inst_602_);
    v___f_610_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_610_, 0, v_toApplicative_607_);
    crate::leanh::lean_closure_set(v___f_610_, 1, v_inst_602_);
    crate::leanh::lean_closure_set(v___f_610_, 2, v_toBind_608_);
    crate::leanh::lean_closure_set(v___f_610_, 3, v_build_605_);
    crate::leanh::lean_closure_set(v___f_610_, 4, v___x_609_);
    crate::leanh::lean_closure_set(v___f_610_, 5, v_stack_603_);
    crate::leanh::lean_closure_set(v___f_610_, 6, v_a_606_);
    v___x_611_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_611_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_611_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_611_, 2, v_store_604_);
    v___x_612_ = crate::leanh::lean_apply_2(v_inst_602_, crate::leanh::lean_box(0), v___x_611_);
    v___x_613_ = crate::leanh::lean_apply_4(
        v_toBind_608_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_612_,
        v___f_610_,
    );
    return v___x_613_;
}
pub unsafe fn l_Lake_RecBuildT_run___boxed(
    mut v_m_614_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_615_: *mut crate::leanh::LeanObject,
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_stack_618_: *mut crate::leanh::LeanObject,
    mut v_store_619_: *mut crate::leanh::LeanObject,
    mut v_build_620_: *mut crate::leanh::LeanObject,
    mut v_a_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_621_);
    return v_res_622_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0(
    mut v_x_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_624_ = crate::leanh::lean_ctor_get(v_x_623_, 0);
    crate::leanh::lean_inc(v_fst_624_);
    return v_fst_624_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(
    mut v_x_625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lake_RecBuildT_run_x27___redArg___lam__0(v_x_625_);
    crate::leanh::lean_dec_ref(v_x_625_);
    return v_res_626_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__1(
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_toPure_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_630_, 0, v_a_627_);
    crate::leanh::lean_ctor_set(v___x_630_, 1, v_a_629_);
    v___x_631_ = crate::leanh::lean_apply_2(v_toPure_628_, crate::leanh::lean_box(0), v___x_630_);
    return v___x_631_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__2(
    mut v_toPure_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
    mut v_toBind_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_637_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_637_, 0, v_a_636_);
    crate::leanh::lean_closure_set(v___f_637_, 1, v_toPure_632_);
    v___x_638_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_638_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_638_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_638_, 2, v_a_633_);
    v___x_639_ = crate::leanh::lean_apply_2(v_inst_634_, crate::leanh::lean_box(0), v___x_638_);
    v___x_640_ = crate::leanh::lean_apply_4(
        v_toBind_635_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_639_,
        v___f_637_,
    );
    return v___x_640_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3(
    mut v_toPure_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_toBind_643_: *mut crate::leanh::LeanObject,
    mut v_build_644_: *mut crate::leanh::LeanObject,
    mut v___x_645_: *mut crate::leanh::LeanObject,
    mut v___x_646_: *mut crate::leanh::LeanObject,
    mut v_a_647_: *mut crate::leanh::LeanObject,
    mut v_a_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_643_);
    crate::leanh::lean_inc(v_a_648_);
    v___f_649_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_649_, 0, v_toPure_641_);
    crate::leanh::lean_closure_set(v___f_649_, 1, v_a_648_);
    crate::leanh::lean_closure_set(v___f_649_, 2, v_inst_642_);
    crate::leanh::lean_closure_set(v___f_649_, 3, v_toBind_643_);
    crate::leanh::lean_inc_ref(v_a_647_);
    v___x_650_ =
        crate::leanh::lean_apply_4(v_build_644_, v___x_645_, v___x_646_, v_a_648_, v_a_647_);
    v___x_651_ = crate::leanh::lean_apply_4(
        v_toBind_643_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_650_,
        v___f_649_,
    );
    return v___x_651_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed(
    mut v_toPure_652_: *mut crate::leanh::LeanObject,
    mut v_inst_653_: *mut crate::leanh::LeanObject,
    mut v_toBind_654_: *mut crate::leanh::LeanObject,
    mut v_build_655_: *mut crate::leanh::LeanObject,
    mut v___x_656_: *mut crate::leanh::LeanObject,
    mut v___x_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg(
    mut v_inst_664_: *mut crate::leanh::LeanObject,
    mut v_inst_665_: *mut crate::leanh::LeanObject,
    mut v_build_666_: *mut crate::leanh::LeanObject,
    mut v_a_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_668_ = crate::leanh::lean_ctor_get(v_inst_664_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_668_);
    v_toFunctor_669_ = crate::leanh::lean_ctor_get(v_toApplicative_668_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_669_);
    v_toBind_670_ = crate::leanh::lean_ctor_get(v_inst_664_, 1);
    crate::leanh::lean_inc_n(v_toBind_670_, 2);
    crate::leanh::lean_dec_ref(v_inst_664_);
    v_toPure_671_ = crate::leanh::lean_ctor_get(v_toApplicative_668_, 1);
    crate::leanh::lean_inc(v_toPure_671_);
    crate::leanh::lean_dec_ref(v_toApplicative_668_);
    v_map_672_ = crate::leanh::lean_ctor_get(v_toFunctor_669_, 0);
    crate::leanh::lean_inc(v_map_672_);
    crate::leanh::lean_dec_ref(v_toFunctor_669_);
    v___f_673_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_674_ = crate::leanh::lean_box(0);
    v___x_675_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_a_667_);
    crate::leanh::lean_inc(v_inst_665_);
    v___f_676_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_676_, 0, v_toPure_671_);
    crate::leanh::lean_closure_set(v___f_676_, 1, v_inst_665_);
    crate::leanh::lean_closure_set(v___f_676_, 2, v_toBind_670_);
    crate::leanh::lean_closure_set(v___f_676_, 3, v_build_666_);
    crate::leanh::lean_closure_set(v___f_676_, 4, v___x_675_);
    crate::leanh::lean_closure_set(v___f_676_, 5, v___x_674_);
    crate::leanh::lean_closure_set(v___f_676_, 6, v_a_667_);
    v___x_677_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_678_ = crate::leanh::lean_apply_2(v_inst_665_, crate::leanh::lean_box(0), v___x_677_);
    v___x_679_ = crate::leanh::lean_apply_4(
        v_toBind_670_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_678_,
        v___f_676_,
    );
    v___x_680_ = crate::leanh::lean_apply_4(
        v_map_672_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_673_,
        v___x_679_,
    );
    return v___x_680_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___boxed(
    mut v_inst_681_: *mut crate::leanh::LeanObject,
    mut v_inst_682_: *mut crate::leanh::LeanObject,
    mut v_build_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_685_ =
        l_Lake_RecBuildT_run_x27___redArg(v_inst_681_, v_inst_682_, v_build_683_, v_a_684_);
    crate::leanh::lean_dec_ref(v_a_684_);
    return v_res_685_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27(
    mut v_m_686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_687_: *mut crate::leanh::LeanObject,
    mut v_inst_688_: *mut crate::leanh::LeanObject,
    mut v_inst_689_: *mut crate::leanh::LeanObject,
    mut v_build_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_692_ = crate::leanh::lean_ctor_get(v_inst_688_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_692_);
    v_toFunctor_693_ = crate::leanh::lean_ctor_get(v_toApplicative_692_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_693_);
    v_toBind_694_ = crate::leanh::lean_ctor_get(v_inst_688_, 1);
    crate::leanh::lean_inc_n(v_toBind_694_, 2);
    crate::leanh::lean_dec_ref(v_inst_688_);
    v_toPure_695_ = crate::leanh::lean_ctor_get(v_toApplicative_692_, 1);
    crate::leanh::lean_inc(v_toPure_695_);
    crate::leanh::lean_dec_ref(v_toApplicative_692_);
    v_map_696_ = crate::leanh::lean_ctor_get(v_toFunctor_693_, 0);
    crate::leanh::lean_inc(v_map_696_);
    crate::leanh::lean_dec_ref(v_toFunctor_693_);
    v___f_697_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_698_ = crate::leanh::lean_box(0);
    v___x_699_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_a_691_);
    crate::leanh::lean_inc(v_inst_689_);
    v___f_700_ = crate::leanh::lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_700_, 0, v_toPure_695_);
    crate::leanh::lean_closure_set(v___f_700_, 1, v_inst_689_);
    crate::leanh::lean_closure_set(v___f_700_, 2, v_toBind_694_);
    crate::leanh::lean_closure_set(v___f_700_, 3, v_build_690_);
    crate::leanh::lean_closure_set(v___f_700_, 4, v___x_699_);
    crate::leanh::lean_closure_set(v___f_700_, 5, v___x_698_);
    crate::leanh::lean_closure_set(v___f_700_, 6, v_a_691_);
    v___x_701_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_702_ = crate::leanh::lean_apply_2(v_inst_689_, crate::leanh::lean_box(0), v___x_701_);
    v___x_703_ = crate::leanh::lean_apply_4(
        v_toBind_694_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_702_,
        v___f_700_,
    );
    v___x_704_ = crate::leanh::lean_apply_4(
        v_map_696_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_697_,
        v___x_703_,
    );
    return v___x_704_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___boxed(
    mut v_m_705_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_706_: *mut crate::leanh::LeanObject,
    mut v_inst_707_: *mut crate::leanh::LeanObject,
    mut v_inst_708_: *mut crate::leanh::LeanObject,
    mut v_build_709_: *mut crate::leanh::LeanObject,
    mut v_a_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_711_ = l_Lake_RecBuildT_run_x27(
        v_m_705_,
        v_00_u03b1_706_,
        v_inst_707_,
        v_inst_708_,
        v_build_709_,
        v_a_710_,
    );
    crate::leanh::lean_dec_ref(v_a_710_);
    return v_res_711_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg(
    mut v_f_712_: *mut crate::leanh::LeanObject,
    mut v_a_713_: *mut crate::leanh::LeanObject,
    mut v_a_714_: *mut crate::leanh::LeanObject,
    mut v_a_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
    mut v_a_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_717_);
    crate::leanh::lean_inc(v_a_716_);
    crate::leanh::lean_inc(v_a_715_);
    crate::leanh::lean_inc(v_a_714_);
    v___x_720_ = crate::leanh::lean_apply_7(
        v_f_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
        v_a_716_,
        v_a_717_,
        v_a_718_,
        crate::leanh::lean_box(0),
    );
    return v___x_720_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg___boxed(
    mut v_f_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
    mut v_a_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
    mut v_a_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lake_FetchM_ofFn___redArg(
        v_f_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_,
    );
    crate::leanh::lean_dec_ref(v_a_726_);
    crate::leanh::lean_dec(v_a_725_);
    crate::leanh::lean_dec(v_a_724_);
    crate::leanh::lean_dec(v_a_723_);
    return v_res_729_;
}
pub unsafe fn l_Lake_FetchM_ofFn(
    mut v_00_u03b1_730_: *mut crate::leanh::LeanObject,
    mut v_f_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
    mut v_a_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
    mut v_a_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
    mut v_a_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_736_);
    crate::leanh::lean_inc(v_a_735_);
    crate::leanh::lean_inc(v_a_734_);
    crate::leanh::lean_inc(v_a_733_);
    v___x_739_ = crate::leanh::lean_apply_7(
        v_f_731_,
        v_a_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
        v_a_737_,
        crate::leanh::lean_box(0),
    );
    return v___x_739_;
}
pub unsafe fn l_Lake_FetchM_ofFn___boxed(
    mut v_00_u03b1_740_: *mut crate::leanh::LeanObject,
    mut v_f_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
    mut v_a_745_: *mut crate::leanh::LeanObject,
    mut v_a_746_: *mut crate::leanh::LeanObject,
    mut v_a_747_: *mut crate::leanh::LeanObject,
    mut v_a_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_746_);
    crate::leanh::lean_dec(v_a_745_);
    crate::leanh::lean_dec(v_a_744_);
    crate::leanh::lean_dec(v_a_743_);
    return v_res_749_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg(
    mut v_self_750_: *mut crate::leanh::LeanObject,
    mut v_fetch_751_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_752_: *mut crate::leanh::LeanObject,
    mut v_stack_753_: *mut crate::leanh::LeanObject,
    mut v_store_754_: *mut crate::leanh::LeanObject,
    mut v_ctx_755_: *mut crate::leanh::LeanObject,
    mut v_log_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = crate::leanh::lean_apply_7(
        v_self_750_,
        v_fetch_751_,
        v_pkg_x3f_752_,
        v_stack_753_,
        v_store_754_,
        v_ctx_755_,
        v_log_756_,
        crate::leanh::lean_box(0),
    );
    return v___x_758_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg___boxed(
    mut v_self_759_: *mut crate::leanh::LeanObject,
    mut v_fetch_760_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_761_: *mut crate::leanh::LeanObject,
    mut v_stack_762_: *mut crate::leanh::LeanObject,
    mut v_store_763_: *mut crate::leanh::LeanObject,
    mut v_ctx_764_: *mut crate::leanh::LeanObject,
    mut v_log_765_: *mut crate::leanh::LeanObject,
    mut v_a_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_768_: *mut crate::leanh::LeanObject,
    mut v_self_769_: *mut crate::leanh::LeanObject,
    mut v_fetch_770_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_771_: *mut crate::leanh::LeanObject,
    mut v_stack_772_: *mut crate::leanh::LeanObject,
    mut v_store_773_: *mut crate::leanh::LeanObject,
    mut v_ctx_774_: *mut crate::leanh::LeanObject,
    mut v_log_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = crate::leanh::lean_apply_7(
        v_self_769_,
        v_fetch_770_,
        v_pkg_x3f_771_,
        v_stack_772_,
        v_store_773_,
        v_ctx_774_,
        v_log_775_,
        crate::leanh::lean_box(0),
    );
    return v___x_777_;
}
pub unsafe fn l_Lake_FetchM_toFn___boxed(
    mut v_00_u03b1_778_: *mut crate::leanh::LeanObject,
    mut v_self_779_: *mut crate::leanh::LeanObject,
    mut v_fetch_780_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_781_: *mut crate::leanh::LeanObject,
    mut v_stack_782_: *mut crate::leanh::LeanObject,
    mut v_store_783_: *mut crate::leanh::LeanObject,
    mut v_ctx_784_: *mut crate::leanh::LeanObject,
    mut v_log_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_self_788_: *mut crate::leanh::LeanObject,
    mut v_a_789_: *mut crate::leanh::LeanObject,
    mut v_a_790_: *mut crate::leanh::LeanObject,
    mut v_a_791_: *mut crate::leanh::LeanObject,
    mut v_a_792_: *mut crate::leanh::LeanObject,
    mut v_a_793_: *mut crate::leanh::LeanObject,
    mut v_a_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_793_);
    crate::leanh::lean_inc(v_a_792_);
    crate::leanh::lean_inc(v_a_791_);
    crate::leanh::lean_inc(v_a_790_);
    v___x_796_ = crate::leanh::lean_apply_7(
        v_a_789_,
        v_self_788_,
        v_a_790_,
        v_a_791_,
        v_a_792_,
        v_a_793_,
        v_a_794_,
        crate::leanh::lean_box(0),
    );
    return v___x_796_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___redArg___boxed(
    mut v_self_797_: *mut crate::leanh::LeanObject,
    mut v_a_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lake_BuildInfo_fetch___redArg(
        v_self_797_,
        v_a_798_,
        v_a_799_,
        v_a_800_,
        v_a_801_,
        v_a_802_,
        v_a_803_,
    );
    crate::leanh::lean_dec_ref(v_a_802_);
    crate::leanh::lean_dec(v_a_801_);
    crate::leanh::lean_dec(v_a_800_);
    crate::leanh::lean_dec(v_a_799_);
    return v_res_805_;
}
pub unsafe fn l_Lake_BuildInfo_fetch(
    mut v_00_u03b1_806_: *mut crate::leanh::LeanObject,
    mut v_self_807_: *mut crate::leanh::LeanObject,
    mut v_inst_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_a_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_813_);
    crate::leanh::lean_inc(v_a_812_);
    crate::leanh::lean_inc(v_a_811_);
    crate::leanh::lean_inc(v_a_810_);
    v___x_816_ = crate::leanh::lean_apply_7(
        v_a_809_,
        v_self_807_,
        v_a_810_,
        v_a_811_,
        v_a_812_,
        v_a_813_,
        v_a_814_,
        crate::leanh::lean_box(0),
    );
    return v___x_816_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___boxed(
    mut v_00_u03b1_817_: *mut crate::leanh::LeanObject,
    mut v_self_818_: *mut crate::leanh::LeanObject,
    mut v_inst_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_824_);
    crate::leanh::lean_dec(v_a_823_);
    crate::leanh::lean_dec(v_a_822_);
    crate::leanh::lean_dec(v_a_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg(
    mut v_self_828_: *mut crate::leanh::LeanObject,
    mut v_mod_829_: *mut crate::leanh::LeanObject,
    mut v_a_830_: *mut crate::leanh::LeanObject,
    mut v_a_831_: *mut crate::leanh::LeanObject,
    mut v_a_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_837_ = crate::leanh::lean_ctor_get(v_mod_829_, 0);
    v_pkg_838_ = crate::leanh::lean_ctor_get(v_lib_837_, 0);
    v_name_839_ = crate::leanh::lean_ctor_get(v_mod_829_, 1);
    v_keyName_840_ = crate::leanh::lean_ctor_get(v_pkg_838_, 2);
    crate::leanh::lean_inc(v_name_839_);
    crate::leanh::lean_inc(v_keyName_840_);
    v___x_841_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_841_, 0, v_keyName_840_);
    crate::leanh::lean_ctor_set(v___x_841_, 1, v_name_839_);
    v___x_842_ = l_Lake_Module_keyword;
    v___x_843_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_843_, 0, v___x_841_);
    crate::leanh::lean_ctor_set(v___x_843_, 1, v___x_842_);
    crate::leanh::lean_ctor_set(v___x_843_, 2, v_mod_829_);
    crate::leanh::lean_ctor_set(v___x_843_, 3, v_self_828_);
    crate::leanh::lean_inc_ref(v_a_834_);
    crate::leanh::lean_inc(v_a_833_);
    crate::leanh::lean_inc(v_a_832_);
    crate::leanh::lean_inc(v_a_831_);
    v___x_844_ = crate::leanh::lean_apply_7(
        v_a_830_,
        v___x_843_,
        v_a_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
        v_a_835_,
        crate::leanh::lean_box(0),
    );
    return v___x_844_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg___boxed(
    mut v_self_845_: *mut crate::leanh::LeanObject,
    mut v_mod_846_: *mut crate::leanh::LeanObject,
    mut v_a_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_851_);
    crate::leanh::lean_dec(v_a_850_);
    crate::leanh::lean_dec(v_a_849_);
    crate::leanh::lean_dec(v_a_848_);
    return v_res_854_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch(
    mut v_00_u03b1_855_: *mut crate::leanh::LeanObject,
    mut v_self_856_: *mut crate::leanh::LeanObject,
    mut v_mod_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
    mut v_a_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_866_: *mut crate::leanh::LeanObject,
    mut v_self_867_: *mut crate::leanh::LeanObject,
    mut v_mod_868_: *mut crate::leanh::LeanObject,
    mut v_a_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_a_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_873_);
    crate::leanh::lean_dec(v_a_872_);
    crate::leanh::lean_dec(v_a_871_);
    crate::leanh::lean_dec(v_a_870_);
    return v_res_876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Fetch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Fetch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Fetch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Cycle(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Fetch(builtin);
}
