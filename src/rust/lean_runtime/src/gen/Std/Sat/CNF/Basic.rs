// Lean compiler output
// Module: Std.Sat.CNF.Basic
// Imports: Std.Sat.CNF.Literal Init.Data.Prod Init.Data.Array.Lemmas
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any, l_Array_append___redArg,
    l_Array_contains___redArg,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, l_Array_instDecidableExistsAndMemOfDecidablePred___redArg,
    runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_beq___boxed, l_List_elem___redArg, l_List_isEmpty___redArg,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Prelude::{
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
};
use crate::r#gen::Std::Sat::CNF::Literal::{
    initialize_Std_Sat_CNF_Literal, runtime_initialize_Std_Sat_CNF_Literal,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Std_Sat_CNF_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_Sat_CNF_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_empty___closed__0_value) as *mut LeanObject;
pub static l_Std_Sat_CNF_instAppend___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Sat_CNF_append___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Sat_CNF_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_instAppend___closed__0_value) as *mut LeanObject;
static mut l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value
) as *mut LeanObject;
pub static l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value
) as *mut LeanObject;
pub unsafe fn l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(
    mut v_a_340_: *mut LeanObject,
    mut v_x_341_: *mut LeanObject,
) -> u8 {
    let mut v___x_342_: u8 = 0;
    let mut v_head_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: u8 = 0;
    let mut v___x_349_: u8 = 0;
    let mut v___x_350_: u8 = 0;
    let mut v___x_352_: u8 = 0;
    let mut v___x_354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_341_) == 0 {
                    lean_dec_ref(v_a_340_);
                    v___x_342_ = 0;
                    return v___x_342_;
                } else {
                    v_head_343_ = lean_ctor_get(v_x_341_, 0);
                    lean_inc(v_head_343_);
                    v_tail_344_ = lean_ctor_get(v_x_341_, 1);
                    lean_inc(v_tail_344_);
                    lean_dec_ref_known(v_x_341_, 2);
                    v_fst_345_ = lean_ctor_get(v_head_343_, 0);
                    lean_inc(v_fst_345_);
                    v_snd_346_ = lean_ctor_get(v_head_343_, 1);
                    lean_inc(v_snd_346_);
                    lean_dec(v_head_343_);
                    lean_inc_ref(v_a_340_);
                    v___x_347_ = lean_apply_1(v_a_340_, v_fst_345_);
                    v___x_348_ = (lean_unbox(v___x_347_) as u8);
                    if v___x_348_ == 0 {
                        v___x_349_ = (lean_unbox(v_snd_346_) as u8);
                        lean_dec(v_snd_346_);
                        if v___x_349_ == 0 {
                            lean_dec(v_tail_344_);
                            lean_dec_ref(v_a_340_);
                            v___x_350_ = 1;
                            return v___x_350_;
                        } else {
                            v_x_341_ = v_tail_344_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_352_ = (lean_unbox(v_snd_346_) as u8);
                        if v___x_352_ == 0 {
                            lean_dec(v_snd_346_);
                            v_x_341_ = v_tail_344_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_tail_344_);
                            lean_dec_ref(v_a_340_);
                            v___x_354_ = (lean_unbox(v_snd_346_) as u8);
                            lean_dec(v_snd_346_);
                            return v___x_354_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(
    mut v_a_355_: *mut LeanObject,
    mut v_x_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_357_: u8 = 0;
    let mut v_r_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_357_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_355_, v_x_356_);
    v_r_358_ = lean_box((v_res_357_) as usize);
    return v_r_358_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_eval___redArg(
    mut v_a_359_: *mut LeanObject,
    mut v_c_360_: *mut LeanObject,
) -> u8 {
    let mut v___x_361_: u8 = 0;
    v___x_361_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_359_, v_c_360_);
    return v___x_361_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_eval___redArg___boxed(
    mut v_a_362_: *mut LeanObject,
    mut v_c_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_364_: u8 = 0;
    let mut v_r_365_: *mut LeanObject = core::ptr::null_mut();
    v_res_364_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_362_, v_c_363_);
    v_r_365_ = lean_box((v_res_364_) as usize);
    return v_r_365_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_eval(
    mut v_00_u03b1_366_: *mut LeanObject,
    mut v_a_367_: *mut LeanObject,
    mut v_c_368_: *mut LeanObject,
) -> u8 {
    let mut v___x_369_: u8 = 0;
    v___x_369_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_367_, v_c_368_);
    return v___x_369_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_eval___boxed(
    mut v_00_u03b1_370_: *mut LeanObject,
    mut v_a_371_: *mut LeanObject,
    mut v_c_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_373_: u8 = 0;
    let mut v_r_374_: *mut LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Std_Sat_CNF_Clause_eval(v_00_u03b1_370_, v_a_371_, v_c_372_);
    v_r_374_ = lean_box((v_res_373_) as usize);
    return v_r_374_;
}
pub unsafe fn l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(
    mut v_00_u03b1_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
    mut v_x_377_: *mut LeanObject,
) -> u8 {
    let mut v___x_378_: u8 = 0;
    v___x_378_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_376_, v_x_377_);
    return v___x_378_;
}
pub unsafe fn l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(
    mut v_00_u03b1_379_: *mut LeanObject,
    mut v_a_380_: *mut LeanObject,
    mut v_x_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_382_: u8 = 0;
    let mut v_r_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_382_ =
        l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(v_00_u03b1_379_, v_a_380_, v_x_381_);
    v_r_383_ = lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(
    mut v_a_384_: *mut LeanObject,
    mut v_as_385_: *mut LeanObject,
    mut v_i_386_: usize,
    mut v_stop_387_: usize,
) -> u8 {
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: u8 = 0;
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: usize = 0;
    let mut v___x_393_: usize = 0;
    let mut v___x_395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_388_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
                if v___x_388_ == 0 {
                    v___x_389_ = 1;
                    v___x_390_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
                    lean_inc(v___x_390_);
                    lean_inc_ref(v_a_384_);
                    v___x_391_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(
                        v_a_384_, v___x_390_,
                    );
                    if v___x_391_ == 0 {
                        lean_dec_ref(v_a_384_);
                        return v___x_389_;
                    } else {
                        if v___x_388_ == 0 {
                            v___x_392_ = 1usize;
                            v___x_393_ = lean_usize_add(v_i_386_, v___x_392_);
                            v_i_386_ = v___x_393_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_a_384_);
                            return v___x_389_;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_384_);
                    v___x_395_ = 0;
                    return v___x_395_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(
    mut v_a_396_: *mut LeanObject,
    mut v_as_397_: *mut LeanObject,
    mut v_i_398_: *mut LeanObject,
    mut v_stop_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_400_: usize = 0;
    let mut v_stop_boxed_401_: usize = 0;
    let mut v_res_402_: u8 = 0;
    let mut v_r_403_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_400_ = lean_unbox_usize(v_i_398_);
    lean_dec(v_i_398_);
    v_stop_boxed_401_ = lean_unbox_usize(v_stop_399_);
    lean_dec(v_stop_399_);
    v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_396_, v_as_397_, v_i_boxed_400_, v_stop_boxed_401_);
    lean_dec_ref(v_as_397_);
    v_r_403_ = lean_box((v_res_402_) as usize);
    return v_r_403_;
}
pub unsafe fn l_Std_Sat_CNF_eval___redArg(
    mut v_a_404_: *mut LeanObject,
    mut v_f_405_: *mut LeanObject,
) -> u8 {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: u8 = 0;
    v___x_406_ = lean_unsigned_to_nat(0);
    v___x_407_ = lean_array_get_size(v_f_405_);
    v___x_408_ = lean_nat_dec_lt(v___x_406_, v___x_407_);
    if v___x_408_ == 0 {
        let mut v___x_409_: u8 = 0;
        lean_dec_ref(v_a_404_);
        v___x_409_ = 1;
        return v___x_409_;
    } else {
        if v___x_408_ == 0 {
            lean_dec_ref(v_a_404_);
            return v___x_408_;
        } else {
            let mut v___x_410_: usize = 0;
            let mut v___x_411_: usize = 0;
            let mut v___x_412_: u8 = 0;
            v___x_410_ = 0usize;
            v___x_411_ = lean_usize_of_nat(v___x_407_);
            v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_404_, v_f_405_, v___x_410_, v___x_411_);
            if v___x_412_ == 0 {
                return v___x_408_;
            } else {
                let mut v___x_413_: u8 = 0;
                v___x_413_ = 0;
                return v___x_413_;
            }
        }
    }
}
pub unsafe fn l_Std_Sat_CNF_eval___redArg___boxed(
    mut v_a_414_: *mut LeanObject,
    mut v_f_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: u8 = 0;
    let mut v_r_417_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Sat_CNF_eval___redArg(v_a_414_, v_f_415_);
    lean_dec_ref(v_f_415_);
    v_r_417_ = lean_box((v_res_416_) as usize);
    return v_r_417_;
}
pub unsafe fn l_Std_Sat_CNF_eval(
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v_a_419_: *mut LeanObject,
    mut v_f_420_: *mut LeanObject,
) -> u8 {
    let mut v___x_421_: u8 = 0;
    v___x_421_ = l_Std_Sat_CNF_eval___redArg(v_a_419_, v_f_420_);
    return v___x_421_;
}
pub unsafe fn l_Std_Sat_CNF_eval___boxed(
    mut v_00_u03b1_422_: *mut LeanObject,
    mut v_a_423_: *mut LeanObject,
    mut v_f_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_425_: u8 = 0;
    let mut v_r_426_: *mut LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Std_Sat_CNF_eval(v_00_u03b1_422_, v_a_423_, v_f_424_);
    lean_dec_ref(v_f_424_);
    v_r_426_ = lean_box((v_res_425_) as usize);
    return v_r_426_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(
    mut v_00_u03b1_427_: *mut LeanObject,
    mut v_a_428_: *mut LeanObject,
    mut v_as_429_: *mut LeanObject,
    mut v_i_430_: usize,
    mut v_stop_431_: usize,
) -> u8 {
    let mut v___x_432_: u8 = 0;
    v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_428_, v_as_429_, v_i_430_, v_stop_431_);
    return v___x_432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(
    mut v_00_u03b1_433_: *mut LeanObject,
    mut v_a_434_: *mut LeanObject,
    mut v_as_435_: *mut LeanObject,
    mut v_i_436_: *mut LeanObject,
    mut v_stop_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_438_: usize = 0;
    let mut v_stop_boxed_439_: usize = 0;
    let mut v_res_440_: u8 = 0;
    let mut v_r_441_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_438_ = lean_unbox_usize(v_i_436_);
    lean_dec(v_i_436_);
    v_stop_boxed_439_ = lean_unbox_usize(v_stop_437_);
    lean_dec(v_stop_437_);
    v_res_440_ =
        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(
            v_00_u03b1_433_,
            v_a_434_,
            v_as_435_,
            v_i_boxed_438_,
            v_stop_boxed_439_,
        );
    lean_dec_ref(v_as_435_);
    v_r_441_ = lean_box((v_res_440_) as usize);
    return v_r_441_;
}
pub unsafe fn l_Std_Sat_CNF_empty(mut v_00_u03b1_444_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Std_Sat_CNF_empty___closed__0;
    return v___x_445_;
}
pub unsafe fn l_Std_Sat_CNF_emptyWithCapacity___redArg(
    mut v_n_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    v___x_447_ = lean_mk_empty_array_with_capacity(v_n_446_);
    return v___x_447_;
}
pub unsafe fn l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(
    mut v_n_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_448_);
    lean_dec(v_n_448_);
    return v_res_449_;
}
pub unsafe fn l_Std_Sat_CNF_emptyWithCapacity(
    mut v_00_u03b1_450_: *mut LeanObject,
    mut v_n_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_mk_empty_array_with_capacity(v_n_451_);
    return v___x_452_;
}
pub unsafe fn l_Std_Sat_CNF_emptyWithCapacity___boxed(
    mut v_00_u03b1_453_: *mut LeanObject,
    mut v_n_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_455_: *mut LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_453_, v_n_454_);
    lean_dec(v_n_454_);
    return v_res_455_;
}
pub unsafe fn l_Std_Sat_CNF_add___redArg(
    mut v_c_456_: *mut LeanObject,
    mut v_f_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    v___x_458_ = lean_array_push(v_f_457_, v_c_456_);
    return v___x_458_;
}
pub unsafe fn l_Std_Sat_CNF_add(
    mut v_00_u03b1_459_: *mut LeanObject,
    mut v_c_460_: *mut LeanObject,
    mut v_f_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    v___x_462_ = lean_array_push(v_f_461_, v_c_460_);
    return v___x_462_;
}
pub unsafe fn l_Std_Sat_CNF_append___redArg(
    mut v_f1_463_: *mut LeanObject,
    mut v_f2_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Array_append___redArg(v_f1_463_, v_f2_464_);
    return v___x_465_;
}
pub unsafe fn l_Std_Sat_CNF_append___redArg___boxed(
    mut v_f1_466_: *mut LeanObject,
    mut v_f2_467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_468_: *mut LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Std_Sat_CNF_append___redArg(v_f1_466_, v_f2_467_);
    lean_dec_ref(v_f2_467_);
    return v_res_468_;
}
pub unsafe fn l_Std_Sat_CNF_append(
    mut v_00_u03b1_469_: *mut LeanObject,
    mut v_f1_470_: *mut LeanObject,
    mut v_f2_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = l_Array_append___redArg(v_f1_470_, v_f2_471_);
    return v___x_472_;
}
pub unsafe fn l_Std_Sat_CNF_append___boxed(
    mut v_00_u03b1_473_: *mut LeanObject,
    mut v_f1_474_: *mut LeanObject,
    mut v_f2_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_476_: *mut LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Std_Sat_CNF_append(v_00_u03b1_473_, v_f1_474_, v_f2_475_);
    lean_dec_ref(v_f2_475_);
    return v_res_476_;
}
pub unsafe fn l_Std_Sat_CNF_instAppend(mut v_00_u03b1_478_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Std_Sat_CNF_instAppend___closed__0;
    return v___x_479_;
}
pub unsafe fn _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_481_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_481_, 0, v___x_480_);
    return v___f_481_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
    mut v_v_482_: *mut LeanObject,
    mut v_c_483_: *mut LeanObject,
    mut v_inst_484_: *mut LeanObject,
) -> u8 {
    let mut v___f_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    v___f_485_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_485_, 0, v_inst_484_);
    v___f_486_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once
        ),
        _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0,
    );
    v___f_487_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_487_, 0, v___f_485_);
    lean_closure_set(v___f_487_, 1, v___f_486_);
    v___x_488_ = 0;
    v___x_489_ = lean_box((v___x_488_) as usize);
    lean_inc(v_v_482_);
    v___x_490_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_490_, 0, v_v_482_);
    lean_ctor_set(v___x_490_, 1, v___x_489_);
    lean_inc(v_c_483_);
    lean_inc_ref(v___f_487_);
    v___x_491_ = l_List_elem___redArg(v___f_487_, v___x_490_, v_c_483_);
    if v___x_491_ == 0 {
        let mut v___x_492_: u8 = 0;
        let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_495_: u8 = 0;
        v___x_492_ = 1;
        v___x_493_ = lean_box((v___x_492_) as usize);
        v___x_494_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_494_, 0, v_v_482_);
        lean_ctor_set(v___x_494_, 1, v___x_493_);
        v___x_495_ = l_List_elem___redArg(v___f_487_, v___x_494_, v_c_483_);
        return v___x_495_;
    } else {
        lean_dec_ref(v___f_487_);
        lean_dec(v_c_483_);
        lean_dec(v_v_482_);
        return v___x_491_;
    }
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___boxed(
    mut v_v_496_: *mut LeanObject,
    mut v_c_497_: *mut LeanObject,
    mut v_inst_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: u8 = 0;
    let mut v_r_500_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
        v_v_496_,
        v_c_497_,
        v_inst_498_,
    );
    v_r_500_ = lean_box((v_res_499_) as usize);
    return v_r_500_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(
    mut v_00_u03b1_501_: *mut LeanObject,
    mut v_v_502_: *mut LeanObject,
    mut v_c_503_: *mut LeanObject,
    mut v_inst_504_: *mut LeanObject,
) -> u8 {
    let mut v___x_505_: u8 = 0;
    v___x_505_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
        v_v_502_,
        v_c_503_,
        v_inst_504_,
    );
    return v___x_505_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___boxed(
    mut v_00_u03b1_506_: *mut LeanObject,
    mut v_v_507_: *mut LeanObject,
    mut v_c_508_: *mut LeanObject,
    mut v_inst_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_510_: u8 = 0;
    let mut v_r_511_: *mut LeanObject = core::ptr::null_mut();
    v_res_510_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1(
        v_00_u03b1_506_,
        v_v_507_,
        v_c_508_,
        v_inst_509_,
    );
    v_r_511_ = lean_box((v_res_510_) as usize);
    return v_r_511_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(
    mut v_v_512_: *mut LeanObject,
    mut v_c_513_: *mut LeanObject,
    mut v_inst_514_: *mut LeanObject,
) -> u8 {
    let mut v___x_515_: u8 = 0;
    v___x_515_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
        v_v_512_,
        v_c_513_,
        v_inst_514_,
    );
    return v___x_515_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(
    mut v_v_516_: *mut LeanObject,
    mut v_c_517_: *mut LeanObject,
    mut v_inst_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_519_: u8 = 0;
    let mut v_r_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(
        v_v_516_,
        v_c_517_,
        v_inst_518_,
    );
    v_r_520_ = lean_box((v_res_519_) as usize);
    return v_r_520_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(
    mut v_00_u03b1_521_: *mut LeanObject,
    mut v_v_522_: *mut LeanObject,
    mut v_c_523_: *mut LeanObject,
    mut v_inst_524_: *mut LeanObject,
) -> u8 {
    let mut v___x_525_: u8 = 0;
    v___x_525_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
        v_v_522_,
        v_c_523_,
        v_inst_524_,
    );
    return v___x_525_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(
    mut v_00_u03b1_526_: *mut LeanObject,
    mut v_v_527_: *mut LeanObject,
    mut v_c_528_: *mut LeanObject,
    mut v_inst_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_530_: u8 = 0;
    let mut v_r_531_: *mut LeanObject = core::ptr::null_mut();
    v_res_530_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(
        v_00_u03b1_526_,
        v_v_527_,
        v_c_528_,
        v_inst_529_,
    );
    v_r_531_ = lean_box((v_res_530_) as usize);
    return v_r_531_;
}
pub unsafe fn l_Std_Sat_CNF_instMembershipClause(
    mut v_00_u03b1_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = lean_box(0);
    return v___x_533_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(
    mut v_c_534_: *mut LeanObject,
    mut v_f_535_: *mut LeanObject,
    mut v_inst_536_: *mut LeanObject,
) -> u8 {
    let mut v___f_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: u8 = 0;
    v___f_537_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_537_, 0, v_inst_536_);
    v___f_538_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0_once
        ),
        _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg___closed__0,
    );
    v___f_539_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_539_, 0, v___f_537_);
    lean_closure_set(v___f_539_, 1, v___f_538_);
    v___x_540_ = lean_alloc_closure(l_List_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_540_, 0, lean_box(0));
    lean_closure_set(v___x_540_, 1, v___f_539_);
    v___x_541_ = l_Array_contains___redArg(v___x_540_, v_f_535_, v_c_534_);
    return v___x_541_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg___boxed(
    mut v_c_542_: *mut LeanObject,
    mut v_f_543_: *mut LeanObject,
    mut v_inst_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_545_: u8 = 0;
    let mut v_r_546_: *mut LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(
        v_c_542_,
        v_f_543_,
        v_inst_544_,
    );
    v_r_546_ = lean_box((v_res_545_) as usize);
    return v_r_546_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(
    mut v_00_u03b1_547_: *mut LeanObject,
    mut v_c_548_: *mut LeanObject,
    mut v_f_549_: *mut LeanObject,
    mut v_inst_550_: *mut LeanObject,
) -> u8 {
    let mut v___x_551_: u8 = 0;
    v___x_551_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(
        v_c_548_,
        v_f_549_,
        v_inst_550_,
    );
    return v___x_551_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___boxed(
    mut v_00_u03b1_552_: *mut LeanObject,
    mut v_c_553_: *mut LeanObject,
    mut v_f_554_: *mut LeanObject,
    mut v_inst_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_556_: u8 = 0;
    let mut v_r_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1(
        v_00_u03b1_552_,
        v_c_553_,
        v_f_554_,
        v_inst_555_,
    );
    v_r_557_ = lean_box((v_res_556_) as usize);
    return v_r_557_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(
    mut v_c_558_: *mut LeanObject,
    mut v_f_559_: *mut LeanObject,
    mut v_inst_560_: *mut LeanObject,
) -> u8 {
    let mut v___x_561_: u8 = 0;
    v___x_561_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(
        v_c_558_,
        v_f_559_,
        v_inst_560_,
    );
    return v___x_561_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(
    mut v_c_562_: *mut LeanObject,
    mut v_f_563_: *mut LeanObject,
    mut v_inst_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_565_: u8 = 0;
    let mut v_r_566_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ =
        l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_562_, v_f_563_, v_inst_564_);
    v_r_566_ = lean_box((v_res_565_) as usize);
    return v_r_566_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_c_568_: *mut LeanObject,
    mut v_f_569_: *mut LeanObject,
    mut v_inst_570_: *mut LeanObject,
) -> u8 {
    let mut v___x_571_: u8 = 0;
    v___x_571_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___aux__1___redArg(
        v_c_568_,
        v_f_569_,
        v_inst_570_,
    );
    return v___x_571_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(
    mut v_00_u03b1_572_: *mut LeanObject,
    mut v_c_573_: *mut LeanObject,
    mut v_f_574_: *mut LeanObject,
    mut v_inst_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_576_: u8 = 0;
    let mut v_r_577_: *mut LeanObject = core::ptr::null_mut();
    v_res_576_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(
        v_00_u03b1_572_,
        v_c_573_,
        v_f_574_,
        v_inst_575_,
    );
    v_r_577_ = lean_box((v_res_576_) as usize);
    return v_r_577_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(
    mut v_v_578_: *mut LeanObject,
    mut v_inst_579_: *mut LeanObject,
    mut v_a_580_: *mut LeanObject,
) -> u8 {
    let mut v___x_581_: u8 = 0;
    v___x_581_ = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___aux__1___redArg(
        v_v_578_,
        v_a_580_,
        v_inst_579_,
    );
    return v___x_581_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed(
    mut v_v_582_: *mut LeanObject,
    mut v_inst_583_: *mut LeanObject,
    mut v_a_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_585_: u8 = 0;
    let mut v_r_586_: *mut LeanObject = core::ptr::null_mut();
    v_res_585_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0(
        v_v_582_,
        v_inst_583_,
        v_a_584_,
    );
    v_r_586_ = lean_box((v_res_585_) as usize);
    return v_r_586_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(
    mut v_v_587_: *mut LeanObject,
    mut v_f_588_: *mut LeanObject,
    mut v_inst_589_: *mut LeanObject,
) -> u8 {
    let mut v___f_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    v___f_590_ = lean_alloc_closure(
        l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_590_, 0, v_v_587_);
    lean_closure_set(v___f_590_, 1, v_inst_589_);
    v___x_591_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_f_588_, v___f_590_);
    return v___x_591_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg___boxed(
    mut v_v_592_: *mut LeanObject,
    mut v_f_593_: *mut LeanObject,
    mut v_inst_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_595_: u8 = 0;
    let mut v_r_596_: *mut LeanObject = core::ptr::null_mut();
    v_res_595_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(
        v_v_592_,
        v_f_593_,
        v_inst_594_,
    );
    v_r_596_ = lean_box((v_res_595_) as usize);
    return v_r_596_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(
    mut v_00_u03b1_597_: *mut LeanObject,
    mut v_v_598_: *mut LeanObject,
    mut v_f_599_: *mut LeanObject,
    mut v_inst_600_: *mut LeanObject,
) -> u8 {
    let mut v___x_601_: u8 = 0;
    v___x_601_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(
        v_v_598_,
        v_f_599_,
        v_inst_600_,
    );
    return v___x_601_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___boxed(
    mut v_00_u03b1_602_: *mut LeanObject,
    mut v_v_603_: *mut LeanObject,
    mut v_f_604_: *mut LeanObject,
    mut v_inst_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_606_: u8 = 0;
    let mut v_r_607_: *mut LeanObject = core::ptr::null_mut();
    v_res_606_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1(
        v_00_u03b1_602_,
        v_v_603_,
        v_f_604_,
        v_inst_605_,
    );
    v_r_607_ = lean_box((v_res_606_) as usize);
    return v_r_607_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(
    mut v_v_608_: *mut LeanObject,
    mut v_f_609_: *mut LeanObject,
    mut v_inst_610_: *mut LeanObject,
) -> u8 {
    let mut v___x_611_: u8 = 0;
    v___x_611_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(
        v_v_608_,
        v_f_609_,
        v_inst_610_,
    );
    return v___x_611_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(
    mut v_v_612_: *mut LeanObject,
    mut v_f_613_: *mut LeanObject,
    mut v_inst_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_615_: u8 = 0;
    let mut v_r_616_: *mut LeanObject = core::ptr::null_mut();
    v_res_615_ =
        l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_612_, v_f_613_, v_inst_614_);
    v_r_616_ = lean_box((v_res_615_) as usize);
    return v_r_616_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(
    mut v_00_u03b1_617_: *mut LeanObject,
    mut v_v_618_: *mut LeanObject,
    mut v_f_619_: *mut LeanObject,
    mut v_inst_620_: *mut LeanObject,
) -> u8 {
    let mut v___x_621_: u8 = 0;
    v___x_621_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___aux__1___redArg(
        v_v_618_,
        v_f_619_,
        v_inst_620_,
    );
    return v___x_621_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(
    mut v_00_u03b1_622_: *mut LeanObject,
    mut v_v_623_: *mut LeanObject,
    mut v_f_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_626_: u8 = 0;
    let mut v_r_627_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(
        v_00_u03b1_622_,
        v_v_623_,
        v_f_624_,
        v_inst_625_,
    );
    v_r_627_ = lean_box((v_res_626_) as usize);
    return v_r_627_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(
    mut v___x_628_: u8,
    mut v_x_629_: *mut LeanObject,
) -> u8 {
    let mut v___x_630_: u8 = 0;
    v___x_630_ = l_List_isEmpty___redArg(v_x_629_);
    if v___x_630_ == 0 {
        return v___x_628_;
    } else {
        let mut v___x_631_: u8 = 0;
        v___x_631_ = 0;
        return v___x_631_;
    }
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(
    mut v___x_632_: *mut LeanObject,
    mut v_x_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_86__boxed_634_: u8 = 0;
    let mut v_res_635_: u8 = 0;
    let mut v_r_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_86__boxed_634_ = (lean_unbox(v___x_632_) as u8);
    v_res_635_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(
        v___x_86__boxed_634_,
        v_x_633_,
    );
    lean_dec(v_x_633_);
    v_r_636_ = lean_box((v_res_635_) as usize);
    return v_r_636_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(
    mut v_f_656_: *mut LeanObject,
) -> u8 {
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: u8 = 0;
    v___x_657_ = lean_unsigned_to_nat(0);
    v___x_658_ = lean_array_get_size(v_f_656_);
    v___x_659_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9;
    v___x_660_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
    if v___x_660_ == 0 {
        lean_dec_ref(v_f_656_);
        return v___x_660_;
    } else {
        if v___x_660_ == 0 {
            lean_dec_ref(v_f_656_);
            return v___x_660_;
        } else {
            let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_662_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_663_: usize = 0;
            let mut v___x_664_: usize = 0;
            let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_666_: u8 = 0;
            v___x_661_ = lean_box((v___x_660_) as usize);
            v___f_662_ = lean_alloc_closure(
                l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_662_, 0, v___x_661_);
            v___x_663_ = 0usize;
            v___x_664_ = lean_usize_of_nat(v___x_658_);
            v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_659_,
                v___f_662_,
                v_f_656_,
                v___x_663_,
                v___x_664_,
            );
            v___x_666_ = (lean_unbox(v___x_665_) as u8);
            lean_dec(v___x_665_);
            return v___x_666_;
        }
    }
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(
    mut v_f_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_668_: u8 = 0;
    let mut v_r_669_: *mut LeanObject = core::ptr::null_mut();
    v_res_668_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_667_);
    v_r_669_ = lean_box((v_res_668_) as usize);
    return v_r_669_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(
    mut v_00_u03b1_670_: *mut LeanObject,
    mut v_f_671_: *mut LeanObject,
    mut v_inst_672_: *mut LeanObject,
) -> u8 {
    let mut v___x_673_: u8 = 0;
    v___x_673_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_671_);
    return v___x_673_;
}
pub unsafe fn l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(
    mut v_00_u03b1_674_: *mut LeanObject,
    mut v_f_675_: *mut LeanObject,
    mut v_inst_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_677_: u8 = 0;
    let mut v_r_678_: *mut LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(
        v_00_u03b1_674_,
        v_f_675_,
        v_inst_676_,
    );
    lean_dec_ref(v_inst_676_);
    v_r_678_ = lean_box((v_res_677_) as usize);
    return v_r_678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_CNF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF_Literal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_CNF_Basic(builtin);
}
