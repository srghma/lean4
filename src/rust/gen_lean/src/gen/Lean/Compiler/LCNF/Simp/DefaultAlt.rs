// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DefaultAlt
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::AlphaEqv::l_Lean_Compiler_LCNF_Code_alphaEqv;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_eraseCode___redArg, l_Lean_Compiler_LCNF_eraseParams___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, l_Lean_Compiler_LCNF_Simp_markSimplified___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
static mut l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 68, 101, 102, 97, 117, 108, 116, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 97, 100, 100, 68, 101, 102, 97, 117, 108, 116, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(
    mut v_upperBound_425_: *mut crate::leanh::LeanObject,
    mut v_alts_426_: *mut crate::leanh::LeanObject,
    mut v_code_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
    mut v_b_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_430_: u8 = 0;
    let mut v___x_431_: u8 = 0;
    let mut v_n_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: u8 = 0;
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_430_ = lean_nat_dec_lt(v_a_428_, v_upperBound_425_);
                if v___x_430_ == 0 {
                    crate::leanh::lean_dec(v_a_428_);
                    crate::leanh::lean_dec_ref(v_code_427_);
                    return v_b_429_;
                } else {
                    v___x_431_ = 0;
                    v_n_432_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_441_ = lean_array_fget_borrowed(v_alts_426_, v_a_428_);
                    match crate::leanh::lean_obj_tag(v___x_441_) {
                        0 => {
                            v_code_442_ = crate::leanh::lean_ctor_get(v___x_441_, 2);
                            crate::leanh::lean_inc_ref(v_code_442_);
                            v___y_438_ = v_code_442_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_code_443_ = crate::leanh::lean_ctor_get(v___x_441_, 1);
                            crate::leanh::lean_inc_ref(v_code_443_);
                            v___y_438_ = v_code_443_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_code_444_ = crate::leanh::lean_ctor_get(v___x_441_, 0);
                            crate::leanh::lean_inc_ref(v_code_444_);
                            v___y_438_ = v_code_444_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_435_ = lean_nat_add(v_a_428_, v_n_432_);
                crate::leanh::lean_dec(v_a_428_);
                v_a_428_ = v___x_435_;
                v_b_429_ = v_a_434_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_code_427_);
                v___x_439_ =
                    l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_431_, v___y_438_, v_code_427_);
                if v___x_439_ == 0 {
                    v_a_434_ = v_b_429_;
                    state = 1;
                    continue;
                } else {
                    v___x_440_ = lean_nat_add(v_b_429_, v_n_432_);
                    crate::leanh::lean_dec(v_b_429_);
                    v_a_434_ = v___x_440_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(
    mut v_upperBound_445_: *mut crate::leanh::LeanObject,
    mut v_alts_446_: *mut crate::leanh::LeanObject,
    mut v_code_447_: *mut crate::leanh::LeanObject,
    mut v_a_448_: *mut crate::leanh::LeanObject,
    mut v_b_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_445_, v_alts_446_, v_code_447_, v_a_448_, v_b_449_);
    crate::leanh::lean_dec_ref(v_alts_446_);
    crate::leanh::lean_dec(v_upperBound_445_);
    return v_res_450_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = 0;
    v___x_452_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_451_);
    return v___x_452_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(
    mut v_alts_453_: *mut crate::leanh::LeanObject,
    mut v_i_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0);
    v_n_456_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_457_ = lean_nat_add(v_i_454_, v_n_456_);
    v___x_458_ = lean_array_get_size(v_alts_453_);
    v___x_459_ = lean_array_get_borrowed(v___x_455_, v_alts_453_, v_i_454_);
    match crate::leanh::lean_obj_tag(v___x_459_) {
        0 => {
            let mut v_code_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_460_ = crate::leanh::lean_ctor_get(v___x_459_, 2);
            crate::leanh::lean_inc_ref(v_code_460_);
            v___x_461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_458_, v_alts_453_, v_code_460_, v___x_457_, v_n_456_);
            return v___x_461_;
        }
        1 => {
            let mut v_code_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_462_ = crate::leanh::lean_ctor_get(v___x_459_, 1);
            crate::leanh::lean_inc_ref(v_code_462_);
            v___x_463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_458_, v_alts_453_, v_code_462_, v___x_457_, v_n_456_);
            return v___x_463_;
        }
        _ => {
            let mut v_code_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_464_ = crate::leanh::lean_ctor_get(v___x_459_, 0);
            crate::leanh::lean_inc_ref(v_code_464_);
            v___x_465_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_458_, v_alts_453_, v_code_464_, v___x_457_, v_n_456_);
            return v___x_465_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___boxed(
    mut v_alts_466_: *mut crate::leanh::LeanObject,
    mut v_i_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_466_, v_i_467_);
    crate::leanh::lean_dec(v_i_467_);
    crate::leanh::lean_dec_ref(v_alts_466_);
    return v_res_468_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0(
    mut v_upperBound_469_: *mut crate::leanh::LeanObject,
    mut v_alts_470_: *mut crate::leanh::LeanObject,
    mut v_code_471_: *mut crate::leanh::LeanObject,
    mut v_inst_472_: *mut crate::leanh::LeanObject,
    mut v_R_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
    mut v_b_475_: *mut crate::leanh::LeanObject,
    mut v_c_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_469_, v_alts_470_, v_code_471_, v_a_474_, v_b_475_);
    return v___x_477_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___boxed(
    mut v_upperBound_478_: *mut crate::leanh::LeanObject,
    mut v_alts_479_: *mut crate::leanh::LeanObject,
    mut v_code_480_: *mut crate::leanh::LeanObject,
    mut v_inst_481_: *mut crate::leanh::LeanObject,
    mut v_R_482_: *mut crate::leanh::LeanObject,
    mut v_a_483_: *mut crate::leanh::LeanObject,
    mut v_b_484_: *mut crate::leanh::LeanObject,
    mut v_c_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_478_, v_alts_479_, v_code_480_, v_inst_481_, v_R_482_, v_a_483_, v_b_484_, v_c_485_);
    crate::leanh::lean_dec_ref(v_alts_479_);
    crate::leanh::lean_dec(v_upperBound_478_);
    return v_res_486_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(
    mut v_upperBound_487_: *mut crate::leanh::LeanObject,
    mut v_alts_488_: *mut crate::leanh::LeanObject,
    mut v_a_489_: *mut crate::leanh::LeanObject,
    mut v_b_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: u8 = 0;
    let mut v_fst_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_496_ = lean_nat_dec_lt(v_a_489_, v_upperBound_487_);
                if v___x_496_ == 0 {
                    crate::leanh::lean_dec(v_a_489_);
                    return v_b_490_;
                } else {
                    v_fst_497_ = crate::leanh::lean_ctor_get(v_b_490_, 0);
                    v_snd_498_ = crate::leanh::lean_ctor_get(v_b_490_, 1);
                    v_isSharedCheck_511_ = (!crate::leanh::lean_is_exclusive(v_b_490_)) as u8;
                    if v_isSharedCheck_511_ == 0 {
                        v___x_500_ = v_b_490_;
                        v_isShared_501_ = v_isSharedCheck_511_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_498_);
                        crate::leanh::lean_inc(v_fst_497_);
                        crate::leanh::lean_dec(v_b_490_);
                        v___x_500_ = crate::leanh::lean_box(0);
                        v_isShared_501_ = v_isSharedCheck_511_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_493_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_494_ = lean_nat_add(v_a_489_, v___x_493_);
                crate::leanh::lean_dec(v_a_489_);
                v_a_489_ = v___x_494_;
                v_b_490_ = v_a_492_;
                state = 0;
                continue;
            }
            2 => {
                v___x_502_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_488_, v_a_489_);
                v___x_503_ = lean_nat_dec_lt(v_snd_498_, v___x_502_);
                if v___x_503_ == 0 {
                    crate::leanh::lean_dec(v___x_502_);
                    if v_isShared_501_ == 0 {
                        v___x_505_ = v___x_500_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fst_497_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 1, v_snd_498_);
                        v___x_505_ = v_reuseFailAlloc_506_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_498_);
                    crate::leanh::lean_dec(v_fst_497_);
                    v___x_507_ = lean_array_fget_borrowed(v_alts_488_, v_a_489_);
                    crate::leanh::lean_inc(v___x_507_);
                    if v_isShared_501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_500_, 1, v___x_502_);
                        crate::leanh::lean_ctor_set(v___x_500_, 0, v___x_507_);
                        v___x_509_ = v___x_500_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_502_);
                        v___x_509_ = v_reuseFailAlloc_510_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_492_ = v___x_505_;
                state = 1;
                continue;
            }
            4 => {
                v_a_492_ = v___x_509_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg___boxed(
    mut v_upperBound_512_: *mut crate::leanh::LeanObject,
    mut v_alts_513_: *mut crate::leanh::LeanObject,
    mut v_a_514_: *mut crate::leanh::LeanObject,
    mut v_b_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v_upperBound_512_, v_alts_513_, v_a_514_, v_b_515_);
    crate::leanh::lean_dec_ref(v_alts_513_);
    crate::leanh::lean_dec(v_upperBound_512_);
    return v_res_516_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(
    mut v_alts_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxAlt_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_max_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0);
                v___x_519_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_520_ = lean_array_get_size(v_alts_517_);
                v___x_521_ = crate::leanh::lean_unsigned_to_nat(0);
                v_maxAlt_522_ = lean_array_get_borrowed(v___x_518_, v_alts_517_, v___x_521_);
                v_max_523_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_517_, v___x_521_);
                crate::leanh::lean_inc(v_maxAlt_522_);
                v___x_524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_524_, 0, v_maxAlt_522_);
                crate::leanh::lean_ctor_set(v___x_524_, 1, v_max_523_);
                v___x_525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v___x_520_, v_alts_517_, v___x_519_, v___x_524_);
                v_fst_526_ = crate::leanh::lean_ctor_get(v___x_525_, 0);
                v_snd_527_ = crate::leanh::lean_ctor_get(v___x_525_, 1);
                v_isSharedCheck_534_ = (!crate::leanh::lean_is_exclusive(v___x_525_)) as u8;
                if v_isSharedCheck_534_ == 0 {
                    v___x_529_ = v___x_525_;
                    v_isShared_530_ = v_isSharedCheck_534_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_527_);
                    crate::leanh::lean_inc(v_fst_526_);
                    crate::leanh::lean_dec(v___x_525_);
                    v___x_529_ = crate::leanh::lean_box(0);
                    v_isShared_530_ = v_isSharedCheck_534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_530_ == 0 {
                    v___x_532_ = v___x_529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 1, v_snd_527_);
                    v___x_532_ = v_reuseFailAlloc_533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs___boxed(
    mut v_alts_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_536_ =
        l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(
            v_alts_535_,
        );
    crate::leanh::lean_dec_ref(v_alts_535_);
    return v_res_536_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0(
    mut v_upperBound_537_: *mut crate::leanh::LeanObject,
    mut v_alts_538_: *mut crate::leanh::LeanObject,
    mut v_inst_539_: *mut crate::leanh::LeanObject,
    mut v_R_540_: *mut crate::leanh::LeanObject,
    mut v_a_541_: *mut crate::leanh::LeanObject,
    mut v_b_542_: *mut crate::leanh::LeanObject,
    mut v_c_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v_upperBound_537_, v_alts_538_, v_a_541_, v_b_542_);
    return v___x_544_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___boxed(
    mut v_upperBound_545_: *mut crate::leanh::LeanObject,
    mut v_alts_546_: *mut crate::leanh::LeanObject,
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_R_548_: *mut crate::leanh::LeanObject,
    mut v_a_549_: *mut crate::leanh::LeanObject,
    mut v_b_550_: *mut crate::leanh::LeanObject,
    mut v_c_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0(v_upperBound_545_, v_alts_546_, v_inst_547_, v_R_548_, v_a_549_, v_b_550_, v_c_551_);
    crate::leanh::lean_dec_ref(v_alts_546_);
    crate::leanh::lean_dec(v_upperBound_545_);
    return v_res_552_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_553_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(
    mut v_msg_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v_toFunctor_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v___f_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_596_: u8 = 0;
    let mut v_toFunctor_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___f_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443__overap_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_unused_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_unused_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_unused_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut v_unused_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_567_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0);
                v___x_568_ = l_StateRefT_x27_instMonad___redArg(v___x_567_);
                v_toApplicative_569_ = crate::leanh::lean_ctor_get(v___x_568_, 0);
                v_isSharedCheck_633_ = (!crate::leanh::lean_is_exclusive(v___x_568_)) as u8;
                if v_isSharedCheck_633_ == 0 {
                    v_unused_634_ = crate::leanh::lean_ctor_get(v___x_568_, 1);
                    crate::leanh::lean_dec(v_unused_634_);
                    v___x_571_ = v___x_568_;
                    v_isShared_572_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_569_);
                    crate::leanh::lean_dec(v___x_568_);
                    v___x_571_ = crate::leanh::lean_box(0);
                    v_isShared_572_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_573_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 0);
                v_toSeq_574_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 2);
                v_toSeqLeft_575_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 3);
                v_toSeqRight_576_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 4);
                v_isSharedCheck_631_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_569_)) as u8;
                if v_isSharedCheck_631_ == 0 {
                    v_unused_632_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 1);
                    crate::leanh::lean_dec(v_unused_632_);
                    v___x_578_ = v_toApplicative_569_;
                    v_isShared_579_ = v_isSharedCheck_631_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_576_);
                    crate::leanh::lean_inc(v_toSeqLeft_575_);
                    crate::leanh::lean_inc(v_toSeq_574_);
                    crate::leanh::lean_inc(v_toFunctor_573_);
                    crate::leanh::lean_dec(v_toApplicative_569_);
                    v___x_578_ = crate::leanh::lean_box(0);
                    v_isShared_579_ = v_isSharedCheck_631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_580_ =
                    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1;
                v___f_581_ =
                    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_573_);
                v___f_582_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_582_, 0, v_toFunctor_573_);
                v___f_583_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_583_, 0, v_toFunctor_573_);
                v___x_584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_584_, 0, v___f_582_);
                crate::leanh::lean_ctor_set(v___x_584_, 1, v___f_583_);
                v___f_585_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_585_, 0, v_toSeqRight_576_);
                v___f_586_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_586_, 0, v_toSeqLeft_575_);
                v___f_587_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_587_, 0, v_toSeq_574_);
                if v_isShared_579_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_578_, 4, v___f_585_);
                    crate::leanh::lean_ctor_set(v___x_578_, 3, v___f_586_);
                    crate::leanh::lean_ctor_set(v___x_578_, 2, v___f_587_);
                    crate::leanh::lean_ctor_set(v___x_578_, 1, v___f_580_);
                    crate::leanh::lean_ctor_set(v___x_578_, 0, v___x_584_);
                    v___x_589_ = v___x_578_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 1, v___f_580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 2, v___f_587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 3, v___f_586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 4, v___f_585_);
                    v___x_589_ = v_reuseFailAlloc_630_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_571_, 1, v___f_581_);
                    crate::leanh::lean_ctor_set(v___x_571_, 0, v___x_589_);
                    v___x_591_ = v___x_571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 1, v___f_581_);
                    v___x_591_ = v_reuseFailAlloc_629_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_592_ = l_StateRefT_x27_instMonad___redArg(v___x_591_);
                v_toApplicative_593_ = crate::leanh::lean_ctor_get(v___x_592_, 0);
                v_isSharedCheck_627_ = (!crate::leanh::lean_is_exclusive(v___x_592_)) as u8;
                if v_isSharedCheck_627_ == 0 {
                    v_unused_628_ = crate::leanh::lean_ctor_get(v___x_592_, 1);
                    crate::leanh::lean_dec(v_unused_628_);
                    v___x_595_ = v___x_592_;
                    v_isShared_596_ = v_isSharedCheck_627_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_593_);
                    crate::leanh::lean_dec(v___x_592_);
                    v___x_595_ = crate::leanh::lean_box(0);
                    v_isShared_596_ = v_isSharedCheck_627_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_597_ = crate::leanh::lean_ctor_get(v_toApplicative_593_, 0);
                v_toSeq_598_ = crate::leanh::lean_ctor_get(v_toApplicative_593_, 2);
                v_toSeqLeft_599_ = crate::leanh::lean_ctor_get(v_toApplicative_593_, 3);
                v_toSeqRight_600_ = crate::leanh::lean_ctor_get(v_toApplicative_593_, 4);
                v_isSharedCheck_625_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_593_)) as u8;
                if v_isSharedCheck_625_ == 0 {
                    v_unused_626_ = crate::leanh::lean_ctor_get(v_toApplicative_593_, 1);
                    crate::leanh::lean_dec(v_unused_626_);
                    v___x_602_ = v_toApplicative_593_;
                    v_isShared_603_ = v_isSharedCheck_625_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_600_);
                    crate::leanh::lean_inc(v_toSeqLeft_599_);
                    crate::leanh::lean_inc(v_toSeq_598_);
                    crate::leanh::lean_inc(v_toFunctor_597_);
                    crate::leanh::lean_dec(v_toApplicative_593_);
                    v___x_602_ = crate::leanh::lean_box(0);
                    v_isShared_603_ = v_isSharedCheck_625_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_604_ =
                    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3;
                v___f_605_ =
                    l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_597_);
                v___f_606_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_606_, 0, v_toFunctor_597_);
                v___f_607_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_607_, 0, v_toFunctor_597_);
                v___x_608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_608_, 0, v___f_606_);
                crate::leanh::lean_ctor_set(v___x_608_, 1, v___f_607_);
                v___f_609_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_609_, 0, v_toSeqRight_600_);
                v___f_610_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_610_, 0, v_toSeqLeft_599_);
                v___f_611_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_611_, 0, v_toSeq_598_);
                if v_isShared_603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_602_, 4, v___f_609_);
                    crate::leanh::lean_ctor_set(v___x_602_, 3, v___f_610_);
                    crate::leanh::lean_ctor_set(v___x_602_, 2, v___f_611_);
                    crate::leanh::lean_ctor_set(v___x_602_, 1, v___f_604_);
                    crate::leanh::lean_ctor_set(v___x_602_, 0, v___x_608_);
                    v___x_613_ = v___x_602_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 1, v___f_604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 2, v___f_611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 3, v___f_610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 4, v___f_609_);
                    v___x_613_ = v_reuseFailAlloc_624_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_595_, 1, v___f_605_);
                    crate::leanh::lean_ctor_set(v___x_595_, 0, v___x_613_);
                    v___x_615_ = v___x_595_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_623_, 1, v___f_605_);
                    v___x_615_ = v_reuseFailAlloc_623_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_616_ = l_ReaderT_instMonad___redArg(v___x_615_);
                v___x_617_ = l_StateRefT_x27_instMonad___redArg(v___x_616_);
                v___x_618_ = crate::leanh::lean_box(0);
                v___x_619_ = l_instInhabitedOfMonad___redArg(v___x_617_, v___x_618_);
                v___f_620_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_620_, 0, v___x_619_);
                v___x_3443__overap_621_ = lean_panic_fn_borrowed(v___f_620_, v_msg_558_);
                crate::leanh::lean_dec_ref(v___f_620_);
                crate::leanh::lean_inc(v___y_565_);
                crate::leanh::lean_inc_ref(v___y_564_);
                crate::leanh::lean_inc(v___y_563_);
                crate::leanh::lean_inc_ref(v___y_562_);
                crate::leanh::lean_inc_ref(v___y_561_);
                crate::leanh::lean_inc(v___y_560_);
                crate::leanh::lean_inc_ref(v___y_559_);
                v___x_622_ = crate::leanh::lean_apply_8(
                    v___x_3443__overap_621_,
                    v___y_559_,
                    v___y_560_,
                    v___y_561_,
                    v___y_562_,
                    v___y_563_,
                    v___y_564_,
                    v___y_565_,
                    crate::leanh::lean_box(0),
                );
                return v___x_622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(
    mut v_msg_635_: *mut crate::leanh::LeanObject,
    mut v___y_636_: *mut crate::leanh::LeanObject,
    mut v___y_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
    mut v___y_642_: *mut crate::leanh::LeanObject,
    mut v___y_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_644_ = l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(
        v_msg_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_,
        v___y_642_,
    );
    crate::leanh::lean_dec(v___y_642_);
    crate::leanh::lean_dec_ref(v___y_641_);
    crate::leanh::lean_dec(v___y_640_);
    crate::leanh::lean_dec_ref(v___y_639_);
    crate::leanh::lean_dec_ref(v___y_638_);
    crate::leanh::lean_dec(v___y_637_);
    crate::leanh::lean_dec_ref(v___y_636_);
    return v_res_644_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2;
    v___x_649_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_650_ = crate::leanh::lean_unsigned_to_nat(63);
    v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1;
    v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0;
    v___x_653_ =
        l_mkPanicMessageWithDecl(v___x_652_, v___x_651_, v___x_650_, v___x_649_, v___x_648_);
    return v___x_653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(
    mut v_snd_654_: *mut crate::leanh::LeanObject,
    mut v_fst_655_: *mut crate::leanh::LeanObject,
    mut v_as_656_: *mut crate::leanh::LeanObject,
    mut v_sz_657_: usize,
    mut v_i_658_: usize,
    mut v_b_659_: *mut crate::leanh::LeanObject,
    mut v___y_660_: *mut crate::leanh::LeanObject,
    mut v___y_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
    mut v___y_664_: *mut crate::leanh::LeanObject,
    mut v___y_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: usize = 0;
    let mut v___x_671_: usize = 0;
    let mut v___x_673_: u8 = 0;
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_679_: u8 = 0;
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v___y_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_707_: u8 = 0;
    let mut v_a_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v___y_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_673_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
                if v___x_673_ == 0 {
                    crate::leanh::lean_dec_ref(v_fst_655_);
                    v___x_674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_674_, 0, v_b_659_);
                    return v___x_674_;
                } else {
                    v_fst_675_ = crate::leanh::lean_ctor_get(v_b_659_, 0);
                    v_snd_676_ = crate::leanh::lean_ctor_get(v_b_659_, 1);
                    v_isSharedCheck_735_ = (!crate::leanh::lean_is_exclusive(v_b_659_)) as u8;
                    if v_isSharedCheck_735_ == 0 {
                        v___x_678_ = v_b_659_;
                        v_isShared_679_ = v_isSharedCheck_735_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_676_);
                        crate::leanh::lean_inc(v_fst_675_);
                        crate::leanh::lean_dec(v_b_659_);
                        v___x_678_ = crate::leanh::lean_box(0);
                        v_isShared_679_ = v_isSharedCheck_735_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_670_ = 1usize;
                v___x_671_ = lean_usize_add(v_i_658_, v___x_670_);
                v_i_658_ = v___x_671_;
                v_b_659_ = v_a_669_;
                state = 0;
                continue;
            }
            2 => {
                v___x_680_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_681_ = lean_nat_dec_eq(v_snd_654_, v___x_680_);
                v_a_687_ = lean_array_uget_borrowed(v_as_656_, v_i_658_);
                v___x_688_ = 0;
                match crate::leanh::lean_obj_tag(v_a_687_) {
                    0 => {
                        v_code_732_ = crate::leanh::lean_ctor_get(v_a_687_, 2);
                        crate::leanh::lean_inc_ref(v_code_732_);
                        v___y_728_ = v_code_732_;
                        state = 12;
                        continue;
                    }
                    1 => {
                        v_code_733_ = crate::leanh::lean_ctor_get(v_a_687_, 1);
                        crate::leanh::lean_inc_ref(v_code_733_);
                        v___y_728_ = v_code_733_;
                        state = 12;
                        continue;
                    }
                    _ => {
                        v_code_734_ = crate::leanh::lean_ctor_get(v_a_687_, 0);
                        crate::leanh::lean_inc_ref(v_code_734_);
                        v___y_728_ = v_code_734_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_683_ = crate::leanh::lean_box((v___x_681_) as usize);
                if v_isShared_679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_678_, 1, v___x_683_);
                    v___x_685_ = v___x_678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
                    v___x_685_ = v_reuseFailAlloc_686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_669_ = v___x_685_;
                state = 1;
                continue;
            }
            5 => {
                v___x_692_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_688_, v___y_690_, v___y_691_);
                if v___x_692_ == 0 {
                    crate::leanh::lean_del_object(v___x_678_);
                    crate::leanh::lean_inc(v_a_687_);
                    v___x_693_ = lean_array_push(v_fst_675_, v_a_687_);
                    v___x_694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_694_, 0, v___x_693_);
                    crate::leanh::lean_ctor_set(v___x_694_, 1, v_snd_676_);
                    v_a_669_ = v___x_694_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_687_) == 0 {
                        v_params_695_ = crate::leanh::lean_ctor_get(v_a_687_, 1);
                        v_code_696_ = crate::leanh::lean_ctor_get(v_a_687_, 2);
                        v___x_697_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                            v___x_688_,
                            v_params_695_,
                            v___y_664_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_697_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_697_, 1);
                            v___x_698_ = (crate::leanh::lean_unbox(v_snd_676_) as u8);
                            crate::leanh::lean_dec(v_snd_676_);
                            if v___x_698_ == 0 {
                                v___x_699_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                    v___x_688_,
                                    v_code_696_,
                                    v___y_664_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_699_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_699_, 1);
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_678_);
                                    crate::leanh::lean_dec(v_fst_675_);
                                    crate::leanh::lean_dec_ref(v_fst_655_);
                                    v_a_700_ = crate::leanh::lean_ctor_get(v___x_699_, 0);
                                    v_isSharedCheck_707_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_699_)) as u8;
                                    if v_isSharedCheck_707_ == 0 {
                                        v___x_702_ = v___x_699_;
                                        v_isShared_703_ = v_isSharedCheck_707_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_700_);
                                        crate::leanh::lean_dec(v___x_699_);
                                        v___x_702_ = crate::leanh::lean_box(0);
                                        v_isShared_703_ = v_isSharedCheck_707_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_678_);
                            crate::leanh::lean_dec(v_snd_676_);
                            crate::leanh::lean_dec(v_fst_675_);
                            crate::leanh::lean_dec_ref(v_fst_655_);
                            v_a_708_ = crate::leanh::lean_ctor_get(v___x_697_, 0);
                            v_isSharedCheck_715_ =
                                (!crate::leanh::lean_is_exclusive(v___x_697_)) as u8;
                            if v_isSharedCheck_715_ == 0 {
                                v___x_710_ = v___x_697_;
                                v_isShared_711_ = v_isSharedCheck_715_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_708_);
                                crate::leanh::lean_dec(v___x_697_);
                                v___x_710_ = crate::leanh::lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_715_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_678_);
                        v___x_716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3);
                        v___x_717_ = l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(
                            v___x_716_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_,
                            v___y_665_, v___y_666_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_717_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_717_, 1);
                            v___x_718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_718_, 0, v_fst_675_);
                            crate::leanh::lean_ctor_set(v___x_718_, 1, v_snd_676_);
                            v_a_669_ = v___x_718_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_676_);
                            crate::leanh::lean_dec(v_fst_675_);
                            crate::leanh::lean_dec_ref(v_fst_655_);
                            v_a_719_ = crate::leanh::lean_ctor_get(v___x_717_, 0);
                            v_isSharedCheck_726_ =
                                (!crate::leanh::lean_is_exclusive(v___x_717_)) as u8;
                            if v_isSharedCheck_726_ == 0 {
                                v___x_721_ = v___x_717_;
                                v_isShared_722_ = v_isSharedCheck_726_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_719_);
                                crate::leanh::lean_dec(v___x_717_);
                                v___x_721_ = crate::leanh::lean_box(0);
                                v_isShared_722_ = v_isSharedCheck_726_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_703_ == 0 {
                    v___x_705_ = v___x_702_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
                    v___x_705_ = v_reuseFailAlloc_706_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_705_;
            }
            8 => {
                if v_isShared_711_ == 0 {
                    v___x_713_ = v___x_710_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_713_;
            }
            10 => {
                if v_isShared_722_ == 0 {
                    v___x_724_ = v___x_721_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
                    v___x_724_ = v_reuseFailAlloc_725_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_724_;
            }
            12 => match crate::leanh::lean_obj_tag(v_fst_655_) {
                0 => {
                    v_code_729_ = crate::leanh::lean_ctor_get(v_fst_655_, 2);
                    crate::leanh::lean_inc_ref(v_code_729_);
                    v___y_690_ = v___y_728_;
                    v___y_691_ = v_code_729_;
                    state = 5;
                    continue;
                }
                1 => {
                    v_code_730_ = crate::leanh::lean_ctor_get(v_fst_655_, 1);
                    crate::leanh::lean_inc_ref(v_code_730_);
                    v___y_690_ = v___y_728_;
                    v___y_691_ = v_code_730_;
                    state = 5;
                    continue;
                }
                _ => {
                    v_code_731_ = crate::leanh::lean_ctor_get(v_fst_655_, 0);
                    crate::leanh::lean_inc_ref(v_code_731_);
                    v___y_690_ = v___y_728_;
                    v___y_691_ = v_code_731_;
                    state = 5;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(
    mut v_snd_736_: *mut crate::leanh::LeanObject,
    mut v_fst_737_: *mut crate::leanh::LeanObject,
    mut v_as_738_: *mut crate::leanh::LeanObject,
    mut v_sz_739_: *mut crate::leanh::LeanObject,
    mut v_i_740_: *mut crate::leanh::LeanObject,
    mut v_b_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_750_: usize = 0;
    let mut v_i_boxed_751_: usize = 0;
    let mut v_res_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_750_ = crate::leanh::lean_unbox_usize(v_sz_739_);
    crate::leanh::lean_dec(v_sz_739_);
    v_i_boxed_751_ = crate::leanh::lean_unbox_usize(v_i_740_);
    crate::leanh::lean_dec(v_i_740_);
    v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_snd_736_, v_fst_737_, v_as_738_, v_sz_boxed_750_, v_i_boxed_751_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
    crate::leanh::lean_dec(v___y_748_);
    crate::leanh::lean_dec_ref(v___y_747_);
    crate::leanh::lean_dec(v___y_746_);
    crate::leanh::lean_dec_ref(v___y_745_);
    crate::leanh::lean_dec_ref(v___y_744_);
    crate::leanh::lean_dec(v___y_743_);
    crate::leanh::lean_dec_ref(v___y_742_);
    crate::leanh::lean_dec_ref(v_as_738_);
    crate::leanh::lean_dec(v_snd_736_);
    return v_res_752_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(
    mut v___x_753_: *mut crate::leanh::LeanObject,
    mut v_as_754_: *mut crate::leanh::LeanObject,
    mut v_i_755_: usize,
    mut v_stop_756_: usize,
) -> u8 {
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: u8 = 0;
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: usize = 0;
    let mut v___x_763_: usize = 0;
    let mut v___x_765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_757_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
                if v___x_757_ == 0 {
                    v___x_758_ = 1;
                    v___x_759_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
                    if crate::leanh::lean_obj_tag(v___x_759_) == 2 {
                        return v___x_758_;
                    } else {
                        v___x_760_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_761_ = lean_nat_dec_le(v___x_753_, v___x_760_);
                        if v___x_761_ == 0 {
                            v___x_762_ = 1usize;
                            v___x_763_ = lean_usize_add(v_i_755_, v___x_762_);
                            v_i_755_ = v___x_763_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_758_;
                        }
                    }
                } else {
                    v___x_765_ = 0;
                    return v___x_765_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2___boxed(
    mut v___x_766_: *mut crate::leanh::LeanObject,
    mut v_as_767_: *mut crate::leanh::LeanObject,
    mut v_i_768_: *mut crate::leanh::LeanObject,
    mut v_stop_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_770_: usize = 0;
    let mut v_stop_boxed_771_: usize = 0;
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_770_ = crate::leanh::lean_unbox_usize(v_i_768_);
    crate::leanh::lean_dec(v_i_768_);
    v_stop_boxed_771_ = crate::leanh::lean_unbox_usize(v_stop_769_);
    crate::leanh::lean_dec(v_stop_769_);
    v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(v___x_766_, v_as_767_, v_i_boxed_770_, v_stop_boxed_771_);
    crate::leanh::lean_dec_ref(v_as_767_);
    crate::leanh::lean_dec(v___x_766_);
    v_r_773_ = crate::leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addDefaultAlt(
    mut v_alts_780_: *mut crate::leanh::LeanObject,
    mut v_a_781_: *mut crate::leanh::LeanObject,
    mut v_a_782_: *mut crate::leanh::LeanObject,
    mut v_a_783_: *mut crate::leanh::LeanObject,
    mut v_a_784_: *mut crate::leanh::LeanObject,
    mut v_a_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_798_: u8 = 0;
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_805_: usize = 0;
    let mut v___x_806_: usize = 0;
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_818_: u8 = 0;
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_822_: u8 = 0;
    let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: u8 = 0;
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: usize = 0;
    let mut v___x_837_: usize = 0;
    let mut v___x_838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_795_ = lean_array_get_size(v_alts_780_);
                v___x_796_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_833_ = lean_nat_dec_le(v___x_795_, v___x_796_);
                if v___x_833_ == 0 {
                    v___x_834_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_835_ = lean_nat_dec_lt(v___x_834_, v___x_795_);
                    if v___x_835_ == 0 {
                        v___y_798_ = v___x_833_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_835_ == 0 {
                            v___y_798_ = v___x_833_;
                            state = 2;
                            continue;
                        } else {
                            v___x_836_ = 0usize;
                            v___x_837_ = lean_usize_of_nat(v___x_795_);
                            v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(v___x_795_, v_alts_780_, v___x_836_, v___x_837_);
                            v___y_798_ = v___x_838_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___y_798_ = v___x_833_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_792_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_792_, 0, v___y_791_);
                v___x_793_ = lean_array_push(v___y_790_, v___x_792_);
                v___x_794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_794_, 0, v___x_793_);
                return v___x_794_;
            }
            2 => {
                if v___y_798_ == 0 {
                    v___x_799_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(v_alts_780_);
                    v_fst_800_ = crate::leanh::lean_ctor_get(v___x_799_, 0);
                    crate::leanh::lean_inc(v_fst_800_);
                    v_snd_801_ = crate::leanh::lean_ctor_get(v___x_799_, 1);
                    crate::leanh::lean_inc(v_snd_801_);
                    crate::leanh::lean_dec_ref(v___x_799_);
                    v___x_802_ = lean_nat_dec_eq(v_snd_801_, v___x_796_);
                    if v___x_802_ == 0 {
                        v___x_803_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_782_);
                        if crate::leanh::lean_obj_tag(v___x_803_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_803_, 1);
                            v___x_804_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1;
                            v_sz_805_ = lean_array_size(v_alts_780_);
                            v___x_806_ = 0usize;
                            crate::leanh::lean_inc(v_fst_800_);
                            v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_snd_801_, v_fst_800_, v_alts_780_, v_sz_805_, v___x_806_, v___x_804_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
                            crate::leanh::lean_dec_ref(v_alts_780_);
                            crate::leanh::lean_dec(v_snd_801_);
                            if crate::leanh::lean_obj_tag(v___x_807_) == 0 {
                                v_a_808_ = crate::leanh::lean_ctor_get(v___x_807_, 0);
                                crate::leanh::lean_inc(v_a_808_);
                                crate::leanh::lean_dec_ref_known(v___x_807_, 1);
                                match crate::leanh::lean_obj_tag(v_fst_800_) {
                                    0 => {
                                        v_fst_809_ = crate::leanh::lean_ctor_get(v_a_808_, 0);
                                        crate::leanh::lean_inc(v_fst_809_);
                                        crate::leanh::lean_dec(v_a_808_);
                                        v_code_810_ = crate::leanh::lean_ctor_get(v_fst_800_, 2);
                                        crate::leanh::lean_inc_ref(v_code_810_);
                                        crate::leanh::lean_dec_ref_known(v_fst_800_, 3);
                                        v___y_790_ = v_fst_809_;
                                        v___y_791_ = v_code_810_;
                                        state = 1;
                                        continue;
                                    }
                                    1 => {
                                        v_fst_811_ = crate::leanh::lean_ctor_get(v_a_808_, 0);
                                        crate::leanh::lean_inc(v_fst_811_);
                                        crate::leanh::lean_dec(v_a_808_);
                                        v_code_812_ = crate::leanh::lean_ctor_get(v_fst_800_, 1);
                                        crate::leanh::lean_inc_ref(v_code_812_);
                                        crate::leanh::lean_dec_ref_known(v_fst_800_, 2);
                                        v___y_790_ = v_fst_811_;
                                        v___y_791_ = v_code_812_;
                                        state = 1;
                                        continue;
                                    }
                                    _ => {
                                        v_fst_813_ = crate::leanh::lean_ctor_get(v_a_808_, 0);
                                        crate::leanh::lean_inc(v_fst_813_);
                                        crate::leanh::lean_dec(v_a_808_);
                                        v_code_814_ = crate::leanh::lean_ctor_get(v_fst_800_, 0);
                                        crate::leanh::lean_inc_ref(v_code_814_);
                                        crate::leanh::lean_dec_ref_known(v_fst_800_, 1);
                                        v___y_790_ = v_fst_813_;
                                        v___y_791_ = v_code_814_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_800_);
                                v_a_815_ = crate::leanh::lean_ctor_get(v___x_807_, 0);
                                v_isSharedCheck_822_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_807_)) as u8;
                                if v_isSharedCheck_822_ == 0 {
                                    v___x_817_ = v___x_807_;
                                    v_isShared_818_ = v_isSharedCheck_822_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_815_);
                                    crate::leanh::lean_dec(v___x_807_);
                                    v___x_817_ = crate::leanh::lean_box(0);
                                    v_isShared_818_ = v_isSharedCheck_822_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_801_);
                            crate::leanh::lean_dec(v_fst_800_);
                            crate::leanh::lean_dec_ref(v_alts_780_);
                            v_a_823_ = crate::leanh::lean_ctor_get(v___x_803_, 0);
                            v_isSharedCheck_830_ =
                                (!crate::leanh::lean_is_exclusive(v___x_803_)) as u8;
                            if v_isSharedCheck_830_ == 0 {
                                v___x_825_ = v___x_803_;
                                v_isShared_826_ = v_isSharedCheck_830_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_823_);
                                crate::leanh::lean_dec(v___x_803_);
                                v___x_825_ = crate::leanh::lean_box(0);
                                v_isShared_826_ = v_isSharedCheck_830_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_801_);
                        crate::leanh::lean_dec(v_fst_800_);
                        v___x_831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_831_, 0, v_alts_780_);
                        return v___x_831_;
                    }
                } else {
                    v___x_832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_832_, 0, v_alts_780_);
                    return v___x_832_;
                }
            }
            3 => {
                if v_isShared_818_ == 0 {
                    v___x_820_ = v___x_817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
                    v___x_820_ = v_reuseFailAlloc_821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_820_;
            }
            5 => {
                if v_isShared_826_ == 0 {
                    v___x_828_ = v___x_825_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
                    v___x_828_ = v_reuseFailAlloc_829_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(
    mut v_alts_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_a_846_: *mut crate::leanh::LeanObject,
    mut v_a_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(
        v_alts_839_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
    );
    crate::leanh::lean_dec(v_a_846_);
    crate::leanh::lean_dec_ref(v_a_845_);
    crate::leanh::lean_dec(v_a_844_);
    crate::leanh::lean_dec_ref(v_a_843_);
    crate::leanh::lean_dec_ref(v_a_842_);
    crate::leanh::lean_dec(v_a_841_);
    crate::leanh::lean_dec_ref(v_a_840_);
    return v_res_848_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
}
