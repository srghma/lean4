// Lean compiler output
// Module: Lake.Build.Fetch
// Imports: Lake.Build.Info Lake.Build.Store Lake.Build.Context Lake.Config.Module Lake.Util.EquipT Lake.Util.Cycle Lake.Build.Infos
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
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 32, 0]};
static mut l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_buildCycleError___closed__0_value: LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        98, 117, 105, 108, 100, 32, 99, 121, 99, 108, 101, 32, 100, 101, 116, 101, 99, 116, 101,
        100, 58, 10, 0,
    ],
};
static mut l_Lake_buildCycleError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_buildCycleError___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_RecBuildT_run_x27___redArg___closed__1_value: LeanClosureObject<3> =
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
        m_fun: l_ST_Prim_mkRef___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_RecBuildT_run_x27___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RecBuildT_run_x27___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0(
    mut v_pkg_x3f_439_: *mut LeanObject,
    mut v_x_440_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_pkg_x3f_439_);
    return v_pkg_x3f_439_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed(
    mut v_pkg_x3f_441_: *mut LeanObject,
    mut v_x_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lake_withCurrPackage_x3f___redArg___lam__0(v_pkg_x3f_441_, v_x_442_);
    lean_dec(v_x_442_);
    lean_dec(v_pkg_x3f_441_);
    return v_res_443_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f___redArg(
    mut v_inst_444_: *mut LeanObject,
    mut v_pkg_x3f_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___f_447_ = lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_447_, 0, v_pkg_x3f_445_);
    v___x_448_ = lean_apply_3(v_inst_444_, lean_box(0), v___f_447_, v_x_446_);
    return v___x_448_;
}
pub unsafe fn l_Lake_withCurrPackage_x3f(
    mut v_m_449_: *mut LeanObject,
    mut v_00_u03b1_450_: *mut LeanObject,
    mut v_inst_451_: *mut LeanObject,
    mut v_pkg_x3f_452_: *mut LeanObject,
    mut v_x_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___f_454_ = lean_alloc_closure(
        l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_454_, 0, v_pkg_x3f_452_);
    v___x_455_ = lean_apply_3(v_inst_451_, lean_box(0), v___f_454_, v_x_453_);
    return v___x_455_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0(
    mut v___x_456_: *mut LeanObject,
    mut v_x_457_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_456_);
    return v___x_456_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg___lam__0___boxed(
    mut v___x_458_: *mut LeanObject,
    mut v_x_459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_460_: *mut LeanObject = core::ptr::null_mut();
    v_res_460_ = l_Lake_withCurrPackage___redArg___lam__0(v___x_458_, v_x_459_);
    lean_dec(v_x_459_);
    lean_dec(v___x_458_);
    return v_res_460_;
}
pub unsafe fn l_Lake_withCurrPackage___redArg(
    mut v_inst_461_: *mut LeanObject,
    mut v_pkg_462_: *mut LeanObject,
    mut v_x_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_464_, 0, v_pkg_462_);
    v___f_465_ = lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_465_, 0, v___x_464_);
    v___x_466_ = lean_apply_3(v_inst_461_, lean_box(0), v___f_465_, v_x_463_);
    return v___x_466_;
}
pub unsafe fn l_Lake_withCurrPackage(
    mut v_m_467_: *mut LeanObject,
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_inst_469_: *mut LeanObject,
    mut v_pkg_470_: *mut LeanObject,
    mut v_x_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_472_, 0, v_pkg_470_);
    v___f_473_ = lean_alloc_closure(
        l_Lake_withCurrPackage___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_473_, 0, v___x_472_);
    v___x_474_ = lean_apply_3(v_inst_469_, lean_box(0), v___f_473_, v_x_471_);
    return v___x_474_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg(
    mut v_inst_475_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_475_);
    return v_inst_475_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___redArg___boxed(
    mut v_inst_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_477_: *mut LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Lake_getCurrPackage_x3f___redArg(v_inst_476_);
    lean_dec(v_inst_476_);
    return v_res_477_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f(
    mut v_m_478_: *mut LeanObject,
    mut v_inst_479_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_479_);
    return v_inst_479_;
}
pub unsafe fn l_Lake_getCurrPackage_x3f___boxed(
    mut v_m_480_: *mut LeanObject,
    mut v_inst_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_482_: *mut LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lake_getCurrPackage_x3f(v_m_480_, v_inst_481_);
    lean_dec(v_inst_481_);
    return v_res_482_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
    mut v_a_484_: *mut LeanObject,
    mut v_a_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_484_) == 0 {
                    v___x_486_ = l_List_reverse___redArg(v_a_485_);
                    return v___x_486_;
                } else {
                    v_head_487_ = lean_ctor_get(v_a_484_, 0);
                    v_tail_488_ = lean_ctor_get(v_a_484_, 1);
                    v_isSharedCheck_499_ = (!lean_is_exclusive(v_a_484_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_490_ = v_a_484_;
                        v_isShared_491_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_488_);
                        lean_inc(v_head_487_);
                        lean_dec(v_a_484_);
                        v___x_490_ = lean_box(0);
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
                lean_dec_ref(v___x_493_);
                if v_isShared_491_ == 0 {
                    lean_ctor_set(v___x_490_, 1, v_a_485_);
                    lean_ctor_set(v___x_490_, 0, v___x_494_);
                    v___x_496_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
                    lean_ctor_set(v_reuseFailAlloc_498_, 1, v_a_485_);
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
    mut v_cycle_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0;
    v___x_503_ = lean_box(0);
    v___x_504_ =
        l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(
            v_cycle_501_,
            v___x_503_,
        );
    v___x_505_ = l_String_intercalate(v___x_502_, v___x_504_);
    return v___x_505_;
}
pub unsafe fn l_Lake_buildCycleError(mut v_cycle_507_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    v___x_508_ = l_Lake_buildCycleError___closed__0;
    v___x_509_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(v_cycle_507_);
    v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
    lean_dec_ref(v___x_509_);
    return v___x_510_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
    mut v_inst_511_: *mut LeanObject,
    mut v_00_u03b1_512_: *mut LeanObject,
    mut v_cycle_513_: *mut LeanObject,
    mut v___y_514_: *mut LeanObject,
    mut v___y_515_: *mut LeanObject,
    mut v___y_516_: *mut LeanObject,
    mut v___y_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Lake_buildCycleError(v_cycle_513_);
    v___x_519_ = lean_apply_2(v_inst_511_, lean_box(0), v___x_518_);
    return v___x_519_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed(
    mut v_inst_520_: *mut LeanObject,
    mut v_00_u03b1_521_: *mut LeanObject,
    mut v_cycle_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
    mut v___y_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
    mut v___y_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_527_: *mut LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(
        v_inst_520_,
        v_00_u03b1_521_,
        v_cycle_522_,
        v___y_523_,
        v___y_524_,
        v___y_525_,
        v___y_526_,
    );
    lean_dec_ref(v___y_526_);
    lean_dec(v___y_525_);
    lean_dec(v___y_524_);
    lean_dec(v___y_523_);
    return v_res_527_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
    mut v_inst_530_: *mut LeanObject,
    mut v_inst_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___f_532_ = lean_alloc_closure(
        l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_532_, 0, v_inst_531_);
    v___f_533_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0;
    v___f_534_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1;
    v___x_535_ = l_ReaderT_instMonad___redArg(v_inst_530_);
    v___x_536_ = l_StateRefT_x27_instMonad___redArg(v___x_535_);
    v___x_537_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_536_);
    v___x_538_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
        v___f_533_, v___f_534_, v___x_537_,
    );
    v___x_539_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_539_, 0, v___x_538_);
    lean_ctor_set(v___x_539_, 1, v___f_532_);
    return v___x_539_;
}
pub unsafe fn l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(
    mut v_m_540_: *mut LeanObject,
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(
        v_inst_541_,
        v_inst_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__0(
    mut v_toApplicative_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_547_ = lean_ctor_get(v_toApplicative_544_, 1);
    lean_inc(v_toPure_547_);
    lean_dec_ref(v_toApplicative_544_);
    v___x_548_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_548_, 0, v_a_545_);
    lean_ctor_set(v___x_548_, 1, v_a_546_);
    v___x_549_ = lean_apply_2(v_toPure_547_, lean_box(0), v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__1(
    mut v_toApplicative_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_inst_552_: *mut LeanObject,
    mut v_toBind_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___f_555_ = lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_555_, 0, v_toApplicative_550_);
    lean_closure_set(v___f_555_, 1, v_a_554_);
    v___x_556_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_556_, 0, lean_box(0));
    lean_closure_set(v___x_556_, 1, lean_box(0));
    lean_closure_set(v___x_556_, 2, v_a_551_);
    v___x_557_ = lean_apply_2(v_inst_552_, lean_box(0), v___x_556_);
    v___x_558_ = lean_apply_4(
        v_toBind_553_,
        lean_box(0),
        lean_box(0),
        v___x_557_,
        v___f_555_,
    );
    return v___x_558_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2(
    mut v_toApplicative_559_: *mut LeanObject,
    mut v_inst_560_: *mut LeanObject,
    mut v_toBind_561_: *mut LeanObject,
    mut v_build_562_: *mut LeanObject,
    mut v___x_563_: *mut LeanObject,
    mut v_stack_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_561_);
    lean_inc(v_a_566_);
    v___f_567_ = lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_567_, 0, v_toApplicative_559_);
    lean_closure_set(v___f_567_, 1, v_a_566_);
    lean_closure_set(v___f_567_, 2, v_inst_560_);
    lean_closure_set(v___f_567_, 3, v_toBind_561_);
    lean_inc_ref(v_a_565_);
    v___x_568_ = lean_apply_4(v_build_562_, v___x_563_, v_stack_564_, v_a_566_, v_a_565_);
    v___x_569_ = lean_apply_4(
        v_toBind_561_,
        lean_box(0),
        lean_box(0),
        v___x_568_,
        v___f_567_,
    );
    return v___x_569_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___lam__2___boxed(
    mut v_toApplicative_570_: *mut LeanObject,
    mut v_inst_571_: *mut LeanObject,
    mut v_toBind_572_: *mut LeanObject,
    mut v_build_573_: *mut LeanObject,
    mut v___x_574_: *mut LeanObject,
    mut v_stack_575_: *mut LeanObject,
    mut v_a_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_576_);
    return v_res_578_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg(
    mut v_inst_579_: *mut LeanObject,
    mut v_inst_580_: *mut LeanObject,
    mut v_stack_581_: *mut LeanObject,
    mut v_store_582_: *mut LeanObject,
    mut v_build_583_: *mut LeanObject,
    mut v_a_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_585_ = lean_ctor_get(v_inst_579_, 0);
    lean_inc_ref(v_toApplicative_585_);
    v_toBind_586_ = lean_ctor_get(v_inst_579_, 1);
    lean_inc_n(v_toBind_586_, 2);
    lean_dec_ref(v_inst_579_);
    v___x_587_ = lean_box(0);
    lean_inc_ref(v_a_584_);
    lean_inc(v_inst_580_);
    v___f_588_ = lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_588_, 0, v_toApplicative_585_);
    lean_closure_set(v___f_588_, 1, v_inst_580_);
    lean_closure_set(v___f_588_, 2, v_toBind_586_);
    lean_closure_set(v___f_588_, 3, v_build_583_);
    lean_closure_set(v___f_588_, 4, v___x_587_);
    lean_closure_set(v___f_588_, 5, v_stack_581_);
    lean_closure_set(v___f_588_, 6, v_a_584_);
    v___x_589_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_589_, 0, lean_box(0));
    lean_closure_set(v___x_589_, 1, lean_box(0));
    lean_closure_set(v___x_589_, 2, v_store_582_);
    v___x_590_ = lean_apply_2(v_inst_580_, lean_box(0), v___x_589_);
    v___x_591_ = lean_apply_4(
        v_toBind_586_,
        lean_box(0),
        lean_box(0),
        v___x_590_,
        v___f_588_,
    );
    return v___x_591_;
}
pub unsafe fn l_Lake_RecBuildT_run___redArg___boxed(
    mut v_inst_592_: *mut LeanObject,
    mut v_inst_593_: *mut LeanObject,
    mut v_stack_594_: *mut LeanObject,
    mut v_store_595_: *mut LeanObject,
    mut v_build_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_598_: *mut LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lake_RecBuildT_run___redArg(
        v_inst_592_,
        v_inst_593_,
        v_stack_594_,
        v_store_595_,
        v_build_596_,
        v_a_597_,
    );
    lean_dec_ref(v_a_597_);
    return v_res_598_;
}
pub unsafe fn l_Lake_RecBuildT_run(
    mut v_m_599_: *mut LeanObject,
    mut v_00_u03b1_600_: *mut LeanObject,
    mut v_inst_601_: *mut LeanObject,
    mut v_inst_602_: *mut LeanObject,
    mut v_stack_603_: *mut LeanObject,
    mut v_store_604_: *mut LeanObject,
    mut v_build_605_: *mut LeanObject,
    mut v_a_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_607_ = lean_ctor_get(v_inst_601_, 0);
    lean_inc_ref(v_toApplicative_607_);
    v_toBind_608_ = lean_ctor_get(v_inst_601_, 1);
    lean_inc_n(v_toBind_608_, 2);
    lean_dec_ref(v_inst_601_);
    v___x_609_ = lean_box(0);
    lean_inc_ref(v_a_606_);
    lean_inc(v_inst_602_);
    v___f_610_ = lean_alloc_closure(
        l_Lake_RecBuildT_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_610_, 0, v_toApplicative_607_);
    lean_closure_set(v___f_610_, 1, v_inst_602_);
    lean_closure_set(v___f_610_, 2, v_toBind_608_);
    lean_closure_set(v___f_610_, 3, v_build_605_);
    lean_closure_set(v___f_610_, 4, v___x_609_);
    lean_closure_set(v___f_610_, 5, v_stack_603_);
    lean_closure_set(v___f_610_, 6, v_a_606_);
    v___x_611_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_611_, 0, lean_box(0));
    lean_closure_set(v___x_611_, 1, lean_box(0));
    lean_closure_set(v___x_611_, 2, v_store_604_);
    v___x_612_ = lean_apply_2(v_inst_602_, lean_box(0), v___x_611_);
    v___x_613_ = lean_apply_4(
        v_toBind_608_,
        lean_box(0),
        lean_box(0),
        v___x_612_,
        v___f_610_,
    );
    return v___x_613_;
}
pub unsafe fn l_Lake_RecBuildT_run___boxed(
    mut v_m_614_: *mut LeanObject,
    mut v_00_u03b1_615_: *mut LeanObject,
    mut v_inst_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
    mut v_stack_618_: *mut LeanObject,
    mut v_store_619_: *mut LeanObject,
    mut v_build_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_622_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_621_);
    return v_res_622_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0(
    mut v_x_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_624_: *mut LeanObject = core::ptr::null_mut();
    v_fst_624_ = lean_ctor_get(v_x_623_, 0);
    lean_inc(v_fst_624_);
    return v_fst_624_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(
    mut v_x_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_626_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lake_RecBuildT_run_x27___redArg___lam__0(v_x_625_);
    lean_dec_ref(v_x_625_);
    return v_res_626_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__1(
    mut v_a_627_: *mut LeanObject,
    mut v_toPure_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_630_, 0, v_a_627_);
    lean_ctor_set(v___x_630_, 1, v_a_629_);
    v___x_631_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_630_);
    return v___x_631_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__2(
    mut v_toPure_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
    mut v_inst_634_: *mut LeanObject,
    mut v_toBind_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___f_637_ = lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_637_, 0, v_a_636_);
    lean_closure_set(v___f_637_, 1, v_toPure_632_);
    v___x_638_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_638_, 0, lean_box(0));
    lean_closure_set(v___x_638_, 1, lean_box(0));
    lean_closure_set(v___x_638_, 2, v_a_633_);
    v___x_639_ = lean_apply_2(v_inst_634_, lean_box(0), v___x_638_);
    v___x_640_ = lean_apply_4(
        v_toBind_635_,
        lean_box(0),
        lean_box(0),
        v___x_639_,
        v___f_637_,
    );
    return v___x_640_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3(
    mut v_toPure_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_toBind_643_: *mut LeanObject,
    mut v_build_644_: *mut LeanObject,
    mut v___x_645_: *mut LeanObject,
    mut v___x_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_643_);
    lean_inc(v_a_648_);
    v___f_649_ = lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_649_, 0, v_toPure_641_);
    lean_closure_set(v___f_649_, 1, v_a_648_);
    lean_closure_set(v___f_649_, 2, v_inst_642_);
    lean_closure_set(v___f_649_, 3, v_toBind_643_);
    lean_inc_ref(v_a_647_);
    v___x_650_ = lean_apply_4(v_build_644_, v___x_645_, v___x_646_, v_a_648_, v_a_647_);
    v___x_651_ = lean_apply_4(
        v_toBind_643_,
        lean_box(0),
        lean_box(0),
        v___x_650_,
        v___f_649_,
    );
    return v___x_651_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed(
    mut v_toPure_652_: *mut LeanObject,
    mut v_inst_653_: *mut LeanObject,
    mut v_toBind_654_: *mut LeanObject,
    mut v_build_655_: *mut LeanObject,
    mut v___x_656_: *mut LeanObject,
    mut v___x_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg(
    mut v_inst_664_: *mut LeanObject,
    mut v_inst_665_: *mut LeanObject,
    mut v_build_666_: *mut LeanObject,
    mut v_a_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_668_ = lean_ctor_get(v_inst_664_, 0);
    lean_inc_ref(v_toApplicative_668_);
    v_toFunctor_669_ = lean_ctor_get(v_toApplicative_668_, 0);
    lean_inc_ref(v_toFunctor_669_);
    v_toBind_670_ = lean_ctor_get(v_inst_664_, 1);
    lean_inc_n(v_toBind_670_, 2);
    lean_dec_ref(v_inst_664_);
    v_toPure_671_ = lean_ctor_get(v_toApplicative_668_, 1);
    lean_inc(v_toPure_671_);
    lean_dec_ref(v_toApplicative_668_);
    v_map_672_ = lean_ctor_get(v_toFunctor_669_, 0);
    lean_inc(v_map_672_);
    lean_dec_ref(v_toFunctor_669_);
    v___f_673_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_674_ = lean_box(0);
    v___x_675_ = lean_box(0);
    lean_inc_ref(v_a_667_);
    lean_inc(v_inst_665_);
    v___f_676_ = lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_676_, 0, v_toPure_671_);
    lean_closure_set(v___f_676_, 1, v_inst_665_);
    lean_closure_set(v___f_676_, 2, v_toBind_670_);
    lean_closure_set(v___f_676_, 3, v_build_666_);
    lean_closure_set(v___f_676_, 4, v___x_675_);
    lean_closure_set(v___f_676_, 5, v___x_674_);
    lean_closure_set(v___f_676_, 6, v_a_667_);
    v___x_677_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_678_ = lean_apply_2(v_inst_665_, lean_box(0), v___x_677_);
    v___x_679_ = lean_apply_4(
        v_toBind_670_,
        lean_box(0),
        lean_box(0),
        v___x_678_,
        v___f_676_,
    );
    v___x_680_ = lean_apply_4(v_map_672_, lean_box(0), lean_box(0), v___f_673_, v___x_679_);
    return v___x_680_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___redArg___boxed(
    mut v_inst_681_: *mut LeanObject,
    mut v_inst_682_: *mut LeanObject,
    mut v_build_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_685_: *mut LeanObject = core::ptr::null_mut();
    v_res_685_ =
        l_Lake_RecBuildT_run_x27___redArg(v_inst_681_, v_inst_682_, v_build_683_, v_a_684_);
    lean_dec_ref(v_a_684_);
    return v_res_685_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27(
    mut v_m_686_: *mut LeanObject,
    mut v_00_u03b1_687_: *mut LeanObject,
    mut v_inst_688_: *mut LeanObject,
    mut v_inst_689_: *mut LeanObject,
    mut v_build_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_692_ = lean_ctor_get(v_inst_688_, 0);
    lean_inc_ref(v_toApplicative_692_);
    v_toFunctor_693_ = lean_ctor_get(v_toApplicative_692_, 0);
    lean_inc_ref(v_toFunctor_693_);
    v_toBind_694_ = lean_ctor_get(v_inst_688_, 1);
    lean_inc_n(v_toBind_694_, 2);
    lean_dec_ref(v_inst_688_);
    v_toPure_695_ = lean_ctor_get(v_toApplicative_692_, 1);
    lean_inc(v_toPure_695_);
    lean_dec_ref(v_toApplicative_692_);
    v_map_696_ = lean_ctor_get(v_toFunctor_693_, 0);
    lean_inc(v_map_696_);
    lean_dec_ref(v_toFunctor_693_);
    v___f_697_ = l_Lake_RecBuildT_run_x27___redArg___closed__0;
    v___x_698_ = lean_box(0);
    v___x_699_ = lean_box(0);
    lean_inc_ref(v_a_691_);
    lean_inc(v_inst_689_);
    v___f_700_ = lean_alloc_closure(
        l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_700_, 0, v_toPure_695_);
    lean_closure_set(v___f_700_, 1, v_inst_689_);
    lean_closure_set(v___f_700_, 2, v_toBind_694_);
    lean_closure_set(v___f_700_, 3, v_build_690_);
    lean_closure_set(v___f_700_, 4, v___x_699_);
    lean_closure_set(v___f_700_, 5, v___x_698_);
    lean_closure_set(v___f_700_, 6, v_a_691_);
    v___x_701_ = l_Lake_RecBuildT_run_x27___redArg___closed__1;
    v___x_702_ = lean_apply_2(v_inst_689_, lean_box(0), v___x_701_);
    v___x_703_ = lean_apply_4(
        v_toBind_694_,
        lean_box(0),
        lean_box(0),
        v___x_702_,
        v___f_700_,
    );
    v___x_704_ = lean_apply_4(v_map_696_, lean_box(0), lean_box(0), v___f_697_, v___x_703_);
    return v___x_704_;
}
pub unsafe fn l_Lake_RecBuildT_run_x27___boxed(
    mut v_m_705_: *mut LeanObject,
    mut v_00_u03b1_706_: *mut LeanObject,
    mut v_inst_707_: *mut LeanObject,
    mut v_inst_708_: *mut LeanObject,
    mut v_build_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_711_: *mut LeanObject = core::ptr::null_mut();
    v_res_711_ = l_Lake_RecBuildT_run_x27(
        v_m_705_,
        v_00_u03b1_706_,
        v_inst_707_,
        v_inst_708_,
        v_build_709_,
        v_a_710_,
    );
    lean_dec_ref(v_a_710_);
    return v_res_711_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg(
    mut v_f_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
    mut v_a_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_717_);
    lean_inc(v_a_716_);
    lean_inc(v_a_715_);
    lean_inc(v_a_714_);
    v___x_720_ = lean_apply_7(
        v_f_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
        v_a_716_,
        v_a_717_,
        v_a_718_,
        lean_box(0),
    );
    return v___x_720_;
}
pub unsafe fn l_Lake_FetchM_ofFn___redArg___boxed(
    mut v_f_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lake_FetchM_ofFn___redArg(
        v_f_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_,
    );
    lean_dec_ref(v_a_726_);
    lean_dec(v_a_725_);
    lean_dec(v_a_724_);
    lean_dec(v_a_723_);
    return v_res_729_;
}
pub unsafe fn l_Lake_FetchM_ofFn(
    mut v_00_u03b1_730_: *mut LeanObject,
    mut v_f_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_736_);
    lean_inc(v_a_735_);
    lean_inc(v_a_734_);
    lean_inc(v_a_733_);
    v___x_739_ = lean_apply_7(
        v_f_731_,
        v_a_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
        v_a_737_,
        lean_box(0),
    );
    return v___x_739_;
}
pub unsafe fn l_Lake_FetchM_ofFn___boxed(
    mut v_00_u03b1_740_: *mut LeanObject,
    mut v_f_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
    mut v_a_745_: *mut LeanObject,
    mut v_a_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_749_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_746_);
    lean_dec(v_a_745_);
    lean_dec(v_a_744_);
    lean_dec(v_a_743_);
    return v_res_749_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg(
    mut v_self_750_: *mut LeanObject,
    mut v_fetch_751_: *mut LeanObject,
    mut v_pkg_x3f_752_: *mut LeanObject,
    mut v_stack_753_: *mut LeanObject,
    mut v_store_754_: *mut LeanObject,
    mut v_ctx_755_: *mut LeanObject,
    mut v_log_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_apply_7(
        v_self_750_,
        v_fetch_751_,
        v_pkg_x3f_752_,
        v_stack_753_,
        v_store_754_,
        v_ctx_755_,
        v_log_756_,
        lean_box(0),
    );
    return v___x_758_;
}
pub unsafe fn l_Lake_FetchM_toFn___redArg___boxed(
    mut v_self_759_: *mut LeanObject,
    mut v_fetch_760_: *mut LeanObject,
    mut v_pkg_x3f_761_: *mut LeanObject,
    mut v_stack_762_: *mut LeanObject,
    mut v_store_763_: *mut LeanObject,
    mut v_ctx_764_: *mut LeanObject,
    mut v_log_765_: *mut LeanObject,
    mut v_a_766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_767_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_768_: *mut LeanObject,
    mut v_self_769_: *mut LeanObject,
    mut v_fetch_770_: *mut LeanObject,
    mut v_pkg_x3f_771_: *mut LeanObject,
    mut v_stack_772_: *mut LeanObject,
    mut v_store_773_: *mut LeanObject,
    mut v_ctx_774_: *mut LeanObject,
    mut v_log_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = lean_apply_7(
        v_self_769_,
        v_fetch_770_,
        v_pkg_x3f_771_,
        v_stack_772_,
        v_store_773_,
        v_ctx_774_,
        v_log_775_,
        lean_box(0),
    );
    return v___x_777_;
}
pub unsafe fn l_Lake_FetchM_toFn___boxed(
    mut v_00_u03b1_778_: *mut LeanObject,
    mut v_self_779_: *mut LeanObject,
    mut v_fetch_780_: *mut LeanObject,
    mut v_pkg_x3f_781_: *mut LeanObject,
    mut v_stack_782_: *mut LeanObject,
    mut v_store_783_: *mut LeanObject,
    mut v_ctx_784_: *mut LeanObject,
    mut v_log_785_: *mut LeanObject,
    mut v_a_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_787_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_self_788_: *mut LeanObject,
    mut v_a_789_: *mut LeanObject,
    mut v_a_790_: *mut LeanObject,
    mut v_a_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_793_);
    lean_inc(v_a_792_);
    lean_inc(v_a_791_);
    lean_inc(v_a_790_);
    v___x_796_ = lean_apply_7(
        v_a_789_,
        v_self_788_,
        v_a_790_,
        v_a_791_,
        v_a_792_,
        v_a_793_,
        v_a_794_,
        lean_box(0),
    );
    return v___x_796_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___redArg___boxed(
    mut v_self_797_: *mut LeanObject,
    mut v_a_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_805_: *mut LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lake_BuildInfo_fetch___redArg(
        v_self_797_,
        v_a_798_,
        v_a_799_,
        v_a_800_,
        v_a_801_,
        v_a_802_,
        v_a_803_,
    );
    lean_dec_ref(v_a_802_);
    lean_dec(v_a_801_);
    lean_dec(v_a_800_);
    lean_dec(v_a_799_);
    return v_res_805_;
}
pub unsafe fn l_Lake_BuildInfo_fetch(
    mut v_00_u03b1_806_: *mut LeanObject,
    mut v_self_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
    mut v_a_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_813_);
    lean_inc(v_a_812_);
    lean_inc(v_a_811_);
    lean_inc(v_a_810_);
    v___x_816_ = lean_apply_7(
        v_a_809_,
        v_self_807_,
        v_a_810_,
        v_a_811_,
        v_a_812_,
        v_a_813_,
        v_a_814_,
        lean_box(0),
    );
    return v___x_816_;
}
pub unsafe fn l_Lake_BuildInfo_fetch___boxed(
    mut v_00_u03b1_817_: *mut LeanObject,
    mut v_self_818_: *mut LeanObject,
    mut v_inst_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_827_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_824_);
    lean_dec(v_a_823_);
    lean_dec(v_a_822_);
    lean_dec(v_a_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg(
    mut v_self_828_: *mut LeanObject,
    mut v_mod_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v_lib_837_ = lean_ctor_get(v_mod_829_, 0);
    v_pkg_838_ = lean_ctor_get(v_lib_837_, 0);
    v_name_839_ = lean_ctor_get(v_mod_829_, 1);
    v_keyName_840_ = lean_ctor_get(v_pkg_838_, 2);
    lean_inc(v_name_839_);
    lean_inc(v_keyName_840_);
    v___x_841_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_841_, 0, v_keyName_840_);
    lean_ctor_set(v___x_841_, 1, v_name_839_);
    v___x_842_ = l_Lake_Module_keyword;
    v___x_843_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_843_, 0, v___x_841_);
    lean_ctor_set(v___x_843_, 1, v___x_842_);
    lean_ctor_set(v___x_843_, 2, v_mod_829_);
    lean_ctor_set(v___x_843_, 3, v_self_828_);
    lean_inc_ref(v_a_834_);
    lean_inc(v_a_833_);
    lean_inc(v_a_832_);
    lean_inc(v_a_831_);
    v___x_844_ = lean_apply_7(
        v_a_830_,
        v___x_843_,
        v_a_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
        v_a_835_,
        lean_box(0),
    );
    return v___x_844_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch___redArg___boxed(
    mut v_self_845_: *mut LeanObject,
    mut v_mod_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
    mut v_a_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
    mut v_a_851_: *mut LeanObject,
    mut v_a_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_854_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_851_);
    lean_dec(v_a_850_);
    lean_dec(v_a_849_);
    lean_dec(v_a_848_);
    return v_res_854_;
}
pub unsafe fn l_Lake_ModuleFacet_fetch(
    mut v_00_u03b1_855_: *mut LeanObject,
    mut v_self_856_: *mut LeanObject,
    mut v_mod_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_866_: *mut LeanObject,
    mut v_self_867_: *mut LeanObject,
    mut v_mod_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
    mut v_a_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
    mut v_a_873_: *mut LeanObject,
    mut v_a_874_: *mut LeanObject,
    mut v_a_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_876_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_873_);
    lean_dec(v_a_872_);
    lean_dec(v_a_871_);
    lean_dec(v_a_870_);
    return v_res_876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Fetch(builtin);
}
