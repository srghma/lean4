// Lean compiler output
// Module: Lean.Meta.CollectFVars
// Imports: Lean.Util.CollectFVars Lean.Meta.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasMVar};
use crate::r#gen::Lean::LocalContext::{lean_local_ctx_erase, lean_local_ctx_find};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_LocalInstances_erase, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_removeUnused___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_removeUnused___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_removeUnused___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(
    mut v_e_376_: *mut crate::leanh::LeanObject,
    mut v___y_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_379_: u8 = 0;
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_393_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut v_unused_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_379_ = l_Lean_Expr_hasMVar(v_e_376_);
                if v___x_379_ == 0 {
                    v___x_380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_380_, 0, v_e_376_);
                    return v___x_380_;
                } else {
                    v___x_381_ = lean_st_ref_get(v___y_377_);
                    v_mctx_382_ = crate::leanh::lean_ctor_get(v___x_381_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_382_);
                    crate::leanh::lean_dec(v___x_381_);
                    v___x_383_ = l_Lean_instantiateMVarsCore(v_mctx_382_, v_e_376_);
                    v_fst_384_ = crate::leanh::lean_ctor_get(v___x_383_, 0);
                    crate::leanh::lean_inc(v_fst_384_);
                    v_snd_385_ = crate::leanh::lean_ctor_get(v___x_383_, 1);
                    crate::leanh::lean_inc(v_snd_385_);
                    crate::leanh::lean_dec_ref(v___x_383_);
                    v___x_386_ = lean_st_ref_take(v___y_377_);
                    v_cache_387_ = crate::leanh::lean_ctor_get(v___x_386_, 1);
                    v_zetaDeltaFVarIds_388_ = crate::leanh::lean_ctor_get(v___x_386_, 2);
                    v_postponed_389_ = crate::leanh::lean_ctor_get(v___x_386_, 3);
                    v_diag_390_ = crate::leanh::lean_ctor_get(v___x_386_, 4);
                    v_isSharedCheck_399_ = (!crate::leanh::lean_is_exclusive(v___x_386_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v_unused_400_ = crate::leanh::lean_ctor_get(v___x_386_, 0);
                        crate::leanh::lean_dec(v_unused_400_);
                        v___x_392_ = v___x_386_;
                        v_isShared_393_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_390_);
                        crate::leanh::lean_inc(v_postponed_389_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_388_);
                        crate::leanh::lean_inc(v_cache_387_);
                        crate::leanh::lean_dec(v___x_386_);
                        v___x_392_ = crate::leanh::lean_box(0);
                        v_isShared_393_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_392_, 0, v_snd_385_);
                    v___x_395_ = v___x_392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_398_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 0, v_snd_385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 1, v_cache_387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 2, v_zetaDeltaFVarIds_388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 3, v_postponed_389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 4, v_diag_390_);
                    v___x_395_ = v_reuseFailAlloc_398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_396_ = lean_st_ref_set(v___y_377_, v___x_395_);
                v___x_397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_397_, 0, v_fst_384_);
                return v___x_397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg___boxed(
    mut v_e_401_: *mut crate::leanh::LeanObject,
    mut v___y_402_: *mut crate::leanh::LeanObject,
    mut v___y_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(
        v_e_401_, v___y_402_,
    );
    crate::leanh::lean_dec(v___y_402_);
    return v_res_404_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(
    mut v_e_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(
        v_e_405_, v___y_408_,
    );
    return v___x_412_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___boxed(
    mut v_e_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ = l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0(
        v_e_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_,
    );
    crate::leanh::lean_dec(v___y_418_);
    crate::leanh::lean_dec_ref(v___y_417_);
    crate::leanh::lean_dec(v___y_416_);
    crate::leanh::lean_dec_ref(v___y_415_);
    crate::leanh::lean_dec(v___y_414_);
    return v_res_420_;
}
pub unsafe fn l_Lean_Expr_collectFVars(
    mut v_e_421_: *mut crate::leanh::LeanObject,
    mut v_a_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
    mut v_a_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_432_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_428_ =
                    l_Lean_instantiateMVars___at___00Lean_Expr_collectFVars_spec__0___redArg(
                        v_e_421_, v_a_424_,
                    );
                v_a_429_ = crate::leanh::lean_ctor_get(v___x_428_, 0);
                v_isSharedCheck_440_ = (!crate::leanh::lean_is_exclusive(v___x_428_)) as u8;
                if v_isSharedCheck_440_ == 0 {
                    v___x_431_ = v___x_428_;
                    v_isShared_432_ = v_isSharedCheck_440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_429_);
                    crate::leanh::lean_dec(v___x_428_);
                    v___x_431_ = crate::leanh::lean_box(0);
                    v_isShared_432_ = v_isSharedCheck_440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_433_ = lean_st_ref_take(v_a_422_);
                v___x_434_ = l_Lean_collectFVars(v___x_433_, v_a_429_);
                v___x_435_ = lean_st_ref_set(v_a_422_, v___x_434_);
                v___x_436_ = crate::leanh::lean_box(0);
                if v_isShared_432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_431_, 0, v___x_436_);
                    v___x_438_ = v___x_431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_439_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
                    v___x_438_ = v_reuseFailAlloc_439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_collectFVars___boxed(
    mut v_e_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
    mut v_a_443_: *mut crate::leanh::LeanObject,
    mut v_a_444_: *mut crate::leanh::LeanObject,
    mut v_a_445_: *mut crate::leanh::LeanObject,
    mut v_a_446_: *mut crate::leanh::LeanObject,
    mut v_a_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ =
        l_Lean_Expr_collectFVars(v_e_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
    crate::leanh::lean_dec(v_a_446_);
    crate::leanh::lean_dec_ref(v_a_445_);
    crate::leanh::lean_dec(v_a_444_);
    crate::leanh::lean_dec_ref(v_a_443_);
    crate::leanh::lean_dec(v_a_442_);
    return v_res_448_;
}
pub unsafe fn l_Lean_LocalDecl_collectFVars(
    mut v_localDecl_449_: *mut crate::leanh::LeanObject,
    mut v_a_450_: *mut crate::leanh::LeanObject,
    mut v_a_451_: *mut crate::leanh::LeanObject,
    mut v_a_452_: *mut crate::leanh::LeanObject,
    mut v_a_453_: *mut crate::leanh::LeanObject,
    mut v_a_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_localDecl_449_) == 0 {
        let mut v_type_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_type_456_ = crate::leanh::lean_ctor_get(v_localDecl_449_, 3);
        crate::leanh::lean_inc_ref(v_type_456_);
        crate::leanh::lean_dec_ref_known(v_localDecl_449_, 4);
        v___x_457_ = l_Lean_Expr_collectFVars(
            v_type_456_,
            v_a_450_,
            v_a_451_,
            v_a_452_,
            v_a_453_,
            v_a_454_,
        );
        return v___x_457_;
    } else {
        let mut v_type_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_type_458_ = crate::leanh::lean_ctor_get(v_localDecl_449_, 3);
        crate::leanh::lean_inc_ref(v_type_458_);
        v_value_459_ = crate::leanh::lean_ctor_get(v_localDecl_449_, 4);
        crate::leanh::lean_inc_ref(v_value_459_);
        crate::leanh::lean_dec_ref_known(v_localDecl_449_, 5);
        v___x_460_ = l_Lean_Expr_collectFVars(
            v_type_458_,
            v_a_450_,
            v_a_451_,
            v_a_452_,
            v_a_453_,
            v_a_454_,
        );
        if crate::leanh::lean_obj_tag(v___x_460_) == 0 {
            let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_460_, 1);
            v___x_461_ = l_Lean_Expr_collectFVars(
                v_value_459_,
                v_a_450_,
                v_a_451_,
                v_a_452_,
                v_a_453_,
                v_a_454_,
            );
            return v___x_461_;
        } else {
            crate::leanh::lean_dec_ref(v_value_459_);
            return v___x_460_;
        }
    }
}
pub unsafe fn l_Lean_LocalDecl_collectFVars___boxed(
    mut v_localDecl_462_: *mut crate::leanh::LeanObject,
    mut v_a_463_: *mut crate::leanh::LeanObject,
    mut v_a_464_: *mut crate::leanh::LeanObject,
    mut v_a_465_: *mut crate::leanh::LeanObject,
    mut v_a_466_: *mut crate::leanh::LeanObject,
    mut v_a_467_: *mut crate::leanh::LeanObject,
    mut v_a_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_469_ = l_Lean_LocalDecl_collectFVars(
        v_localDecl_462_,
        v_a_463_,
        v_a_464_,
        v_a_465_,
        v_a_466_,
        v_a_467_,
    );
    crate::leanh::lean_dec(v_a_467_);
    crate::leanh::lean_dec_ref(v_a_466_);
    crate::leanh::lean_dec(v_a_465_);
    crate::leanh::lean_dec_ref(v_a_464_);
    crate::leanh::lean_dec(v_a_463_);
    return v_res_469_;
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(
    mut v_a_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    v___x_473_ = lean_st_ref_get(v_a_471_);
    v___x_474_ = lean_st_ref_get(v_a_470_);
    v_fvarIds_475_ = crate::leanh::lean_ctor_get(v___x_473_, 2);
    crate::leanh::lean_inc_ref(v_fvarIds_475_);
    crate::leanh::lean_dec(v___x_473_);
    v___x_476_ = lean_array_get_size(v_fvarIds_475_);
    v___x_477_ = lean_nat_dec_lt(v___x_474_, v___x_476_);
    if v___x_477_ == 0 {
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_fvarIds_475_);
        crate::leanh::lean_dec(v___x_474_);
        v___x_478_ = crate::leanh::lean_box(0);
        v___x_479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_479_, 0, v___x_478_);
        return v___x_479_;
    } else {
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_480_ = lean_st_ref_take(v_a_470_);
        v___x_481_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_482_ = lean_nat_add(v___x_480_, v___x_481_);
        crate::leanh::lean_dec(v___x_480_);
        v___x_483_ = lean_st_ref_set(v_a_470_, v___x_482_);
        v___x_484_ = lean_array_fget(v_fvarIds_475_, v___x_474_);
        crate::leanh::lean_dec(v___x_474_);
        crate::leanh::lean_dec_ref(v_fvarIds_475_);
        v___x_485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_485_, 0, v___x_484_);
        v___x_486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_486_, 0, v___x_485_);
        return v___x_486_;
    }
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
    mut v_a_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_487_, v_a_488_);
    crate::leanh::lean_dec(v_a_488_);
    crate::leanh::lean_dec(v_a_487_);
    return v_res_490_;
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(
    mut v_a_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_491_, v_a_492_);
    return v___x_498_;
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(
    mut v_a_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_a_501_: *mut crate::leanh::LeanObject,
    mut v_a_502_: *mut crate::leanh::LeanObject,
    mut v_a_503_: *mut crate::leanh::LeanObject,
    mut v_a_504_: *mut crate::leanh::LeanObject,
    mut v_a_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ =
        l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(
            v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_,
        );
    crate::leanh::lean_dec(v_a_504_);
    crate::leanh::lean_dec_ref(v_a_503_);
    crate::leanh::lean_dec(v_a_502_);
    crate::leanh::lean_dec_ref(v_a_501_);
    crate::leanh::lean_dec(v_a_500_);
    crate::leanh::lean_dec(v_a_499_);
    return v_res_506_;
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(
    mut v_a_507_: *mut crate::leanh::LeanObject,
    mut v_a_508_: *mut crate::leanh::LeanObject,
    mut v_a_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
    mut v_a_511_: *mut crate::leanh::LeanObject,
    mut v_a_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v_val_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut v_a_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_514_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(v_a_507_, v_a_508_);
                if crate::leanh::lean_obj_tag(v___x_514_) == 0 {
                    v_a_515_ = crate::leanh::lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_533_ = (!crate::leanh::lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_533_ == 0 {
                        v___x_517_ = v___x_514_;
                        v_isShared_518_ = v_isSharedCheck_533_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_515_);
                        crate::leanh::lean_dec(v___x_514_);
                        v___x_517_ = crate::leanh::lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_533_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_534_ = crate::leanh::lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_541_ = (!crate::leanh::lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_541_ == 0 {
                        v___x_536_ = v___x_514_;
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_534_);
                        crate::leanh::lean_dec(v___x_514_);
                        v___x_536_ = crate::leanh::lean_box(0);
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_515_) == 1 {
                    v_val_519_ = crate::leanh::lean_ctor_get(v_a_515_, 0);
                    crate::leanh::lean_inc(v_val_519_);
                    crate::leanh::lean_dec_ref_known(v_a_515_, 1);
                    v_lctx_520_ = crate::leanh::lean_ctor_get(v_a_509_, 2);
                    crate::leanh::lean_inc_ref(v_lctx_520_);
                    v___x_521_ = lean_local_ctx_find(v_lctx_520_, v_val_519_);
                    if crate::leanh::lean_obj_tag(v___x_521_) == 1 {
                        crate::leanh::lean_del_object(v___x_517_);
                        v_val_522_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                        crate::leanh::lean_inc(v_val_522_);
                        crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                        v___x_523_ = l_Lean_LocalDecl_collectFVars(
                            v_val_522_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_523_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_523_, 1);
                            state = 0;
                            continue;
                        } else {
                            return v___x_523_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_521_);
                        v___x_525_ = crate::leanh::lean_box(0);
                        if v_isShared_518_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_517_, 0, v___x_525_);
                            v___x_527_ = v___x_517_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
                            v___x_527_ = v_reuseFailAlloc_528_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_515_);
                    v___x_529_ = crate::leanh::lean_box(0);
                    if v_isShared_518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_517_, 0, v___x_529_);
                        v___x_531_ = v___x_517_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
                        v___x_531_ = v_reuseFailAlloc_532_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_527_;
            }
            3 => {
                return v___x_531_;
            }
            4 => {
                if v_isShared_537_ == 0 {
                    v___x_539_ = v___x_536_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
                    v___x_539_ = v_reuseFailAlloc_540_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(
    mut v_a_542_: *mut crate::leanh::LeanObject,
    mut v_a_543_: *mut crate::leanh::LeanObject,
    mut v_a_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_a_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(
        v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_,
    );
    crate::leanh::lean_dec(v_a_547_);
    crate::leanh::lean_dec_ref(v_a_546_);
    crate::leanh::lean_dec(v_a_545_);
    crate::leanh::lean_dec_ref(v_a_544_);
    crate::leanh::lean_dec(v_a_543_);
    crate::leanh::lean_dec(v_a_542_);
    return v_res_549_;
}
pub unsafe fn l_Lean_CollectFVars_State_addDependencies(
    mut v_s_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
    mut v_a_553_: *mut crate::leanh::LeanObject,
    mut v_a_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_562_: u8 = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_568_: u8 = 0;
    let mut v_unused_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_556_ = lean_st_mk_ref(v_s_550_);
                v___x_557_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_558_ = lean_st_mk_ref(v___x_557_);
                v___x_559_ = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(v___x_558_, v___x_556_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
                if crate::leanh::lean_obj_tag(v___x_559_) == 0 {
                    v_isSharedCheck_568_ = (!crate::leanh::lean_is_exclusive(v___x_559_)) as u8;
                    if v_isSharedCheck_568_ == 0 {
                        v_unused_569_ = crate::leanh::lean_ctor_get(v___x_559_, 0);
                        crate::leanh::lean_dec(v_unused_569_);
                        v___x_561_ = v___x_559_;
                        v_isShared_562_ = v_isSharedCheck_568_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_559_);
                        v___x_561_ = crate::leanh::lean_box(0);
                        v_isShared_562_ = v_isSharedCheck_568_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_558_);
                    crate::leanh::lean_dec(v___x_556_);
                    v_a_570_ = crate::leanh::lean_ctor_get(v___x_559_, 0);
                    v_isSharedCheck_577_ = (!crate::leanh::lean_is_exclusive(v___x_559_)) as u8;
                    if v_isSharedCheck_577_ == 0 {
                        v___x_572_ = v___x_559_;
                        v_isShared_573_ = v_isSharedCheck_577_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_570_);
                        crate::leanh::lean_dec(v___x_559_);
                        v___x_572_ = crate::leanh::lean_box(0);
                        v_isShared_573_ = v_isSharedCheck_577_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_563_ = lean_st_ref_get(v___x_558_);
                crate::leanh::lean_dec(v___x_558_);
                crate::leanh::lean_dec(v___x_563_);
                v___x_564_ = lean_st_ref_get(v___x_556_);
                crate::leanh::lean_dec(v___x_556_);
                if v_isShared_562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_561_, 0, v___x_564_);
                    v___x_566_ = v___x_561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
                    v___x_566_ = v_reuseFailAlloc_567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_566_;
            }
            3 => {
                if v_isShared_573_ == 0 {
                    v___x_575_ = v___x_572_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
                    v___x_575_ = v_reuseFailAlloc_576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectFVars_State_addDependencies___boxed(
    mut v_s_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
    mut v_a_580_: *mut crate::leanh::LeanObject,
    mut v_a_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
    mut v_a_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ =
        l_Lean_CollectFVars_State_addDependencies(v_s_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
    crate::leanh::lean_dec(v_a_582_);
    crate::leanh::lean_dec_ref(v_a_581_);
    crate::leanh::lean_dec(v_a_580_);
    crate::leanh::lean_dec_ref(v_a_579_);
    return v_res_584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(
    mut v_k_585_: *mut crate::leanh::LeanObject,
    mut v_t_586_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_592_: u8 = 0;
    let mut v___x_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_586_) == 0 {
                    v_k_587_ = crate::leanh::lean_ctor_get(v_t_586_, 1);
                    v_l_588_ = crate::leanh::lean_ctor_get(v_t_586_, 3);
                    v_r_589_ = crate::leanh::lean_ctor_get(v_t_586_, 4);
                    v___x_590_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_585_, v_k_587_);
                    match v___x_590_ {
                        0 => {
                            v_t_586_ = v_l_588_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_592_ = 1;
                            return v___x_592_;
                        }
                        _ => {
                            v_t_586_ = v_r_589_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_594_ = 0;
                    return v___x_594_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg___boxed(
    mut v_k_595_: *mut crate::leanh::LeanObject,
    mut v_t_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_597_: u8 = 0;
    let mut v_r_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_597_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(
            v_k_595_, v_t_596_,
        );
    crate::leanh::lean_dec(v_t_596_);
    crate::leanh::lean_dec(v_k_595_);
    v_r_598_ = crate::leanh::lean_box((v_res_597_) as usize);
    return v_r_598_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(
    mut v_as_599_: *mut crate::leanh::LeanObject,
    mut v_i_600_: usize,
    mut v_stop_601_: usize,
    mut v_b_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_608_: u8 = 0;
    let mut v_snd_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v_fst_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_619_: u8 = 0;
    let mut v_fst_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: usize = 0;
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_a_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut v_unused_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v_unused_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut v_unused_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_608_ = lean_usize_dec_eq(v_i_600_, v_stop_601_);
                if v___x_608_ == 0 {
                    v_snd_609_ = crate::leanh::lean_ctor_get(v_b_602_, 1);
                    crate::leanh::lean_inc(v_snd_609_);
                    v_snd_610_ = crate::leanh::lean_ctor_get(v_snd_609_, 1);
                    crate::leanh::lean_inc(v_snd_610_);
                    v_snd_611_ = crate::leanh::lean_ctor_get(v_snd_610_, 1);
                    v_fst_612_ = crate::leanh::lean_ctor_get(v_b_602_, 0);
                    v_isSharedCheck_676_ = (!crate::leanh::lean_is_exclusive(v_b_602_)) as u8;
                    if v_isSharedCheck_676_ == 0 {
                        v_unused_677_ = crate::leanh::lean_ctor_get(v_b_602_, 1);
                        crate::leanh::lean_dec(v_unused_677_);
                        v___x_614_ = v_b_602_;
                        v_isShared_615_ = v_isSharedCheck_676_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_612_);
                        crate::leanh::lean_dec(v_b_602_);
                        v___x_614_ = crate::leanh::lean_box(0);
                        v_isShared_615_ = v_isSharedCheck_676_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_678_, 0, v_b_602_);
                    return v___x_678_;
                }
            }
            1 => {
                v_fst_616_ = crate::leanh::lean_ctor_get(v_snd_609_, 0);
                v_isSharedCheck_674_ = (!crate::leanh::lean_is_exclusive(v_snd_609_)) as u8;
                if v_isSharedCheck_674_ == 0 {
                    v_unused_675_ = crate::leanh::lean_ctor_get(v_snd_609_, 1);
                    crate::leanh::lean_dec(v_unused_675_);
                    v___x_618_ = v_snd_609_;
                    v_isShared_619_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_616_);
                    crate::leanh::lean_dec(v_snd_609_);
                    v___x_618_ = crate::leanh::lean_box(0);
                    v_isShared_619_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_620_ = crate::leanh::lean_ctor_get(v_snd_610_, 0);
                v_fvarSet_621_ = crate::leanh::lean_ctor_get(v_snd_611_, 1);
                v___x_622_ = 1usize;
                v___x_623_ = lean_usize_sub(v_i_600_, v___x_622_);
                v___x_624_ = lean_array_uget_borrowed(v_as_599_, v___x_623_);
                v___x_625_ = l_Lean_Expr_fvarId_x21(v___x_624_);
                v___x_626_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(v___x_625_, v_fvarSet_621_);
                if v___x_626_ == 0 {
                    crate::leanh::lean_inc(v___x_625_);
                    v___x_627_ = lean_local_ctx_erase(v_fst_612_, v___x_625_);
                    v___x_628_ = l_Lean_LocalInstances_erase(v_fst_616_, v___x_625_);
                    if v_isShared_619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_618_, 0, v___x_628_);
                        v___x_630_ = v___x_618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_628_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 1, v_snd_610_);
                        v___x_630_ = v_reuseFailAlloc_635_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_fst_620_);
                    crate::leanh::lean_inc(v_snd_611_);
                    crate::leanh::lean_dec(v___x_625_);
                    v_isSharedCheck_671_ = (!crate::leanh::lean_is_exclusive(v_snd_610_)) as u8;
                    if v_isSharedCheck_671_ == 0 {
                        v_unused_672_ = crate::leanh::lean_ctor_get(v_snd_610_, 1);
                        crate::leanh::lean_dec(v_unused_672_);
                        v_unused_673_ = crate::leanh::lean_ctor_get(v_snd_610_, 0);
                        crate::leanh::lean_dec(v_unused_673_);
                        v___x_637_ = v_snd_610_;
                        v_isShared_638_ = v_isSharedCheck_671_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_610_);
                        v___x_637_ = crate::leanh::lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_671_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_630_);
                    crate::leanh::lean_ctor_set(v___x_614_, 0, v___x_627_);
                    v___x_632_ = v___x_614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_630_);
                    v___x_632_ = v_reuseFailAlloc_634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_i_600_ = v___x_623_;
                v_b_602_ = v___x_632_;
                state = 0;
                continue;
            }
            5 => {
                crate::leanh::lean_inc(v___y_606_);
                crate::leanh::lean_inc_ref(v___y_605_);
                crate::leanh::lean_inc(v___y_604_);
                crate::leanh::lean_inc_ref(v___y_603_);
                crate::leanh::lean_inc(v___x_624_);
                v___x_639_ =
                    lean_infer_type(v___x_624_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
                if crate::leanh::lean_obj_tag(v___x_639_) == 0 {
                    v_a_640_ = crate::leanh::lean_ctor_get(v___x_639_, 0);
                    crate::leanh::lean_inc(v_a_640_);
                    crate::leanh::lean_dec_ref_known(v___x_639_, 1);
                    v___x_641_ = lean_st_mk_ref(v_snd_611_);
                    v___x_642_ = l_Lean_Expr_collectFVars(
                        v_a_640_, v___x_641_, v___y_603_, v___y_604_, v___y_605_, v___y_606_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_642_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_642_, 1);
                        v___x_643_ = lean_st_ref_get(v___x_641_);
                        crate::leanh::lean_dec(v___x_641_);
                        crate::leanh::lean_inc(v___x_624_);
                        v___x_644_ = lean_array_push(v_fst_620_, v___x_624_);
                        if v_isShared_638_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_637_, 1, v___x_643_);
                            crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_644_);
                            v___x_646_ = v___x_637_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_644_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_643_);
                            v___x_646_ = v_reuseFailAlloc_654_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_641_);
                        crate::leanh::lean_del_object(v___x_637_);
                        crate::leanh::lean_dec(v_fst_620_);
                        crate::leanh::lean_del_object(v___x_618_);
                        crate::leanh::lean_dec(v_fst_616_);
                        crate::leanh::lean_del_object(v___x_614_);
                        crate::leanh::lean_dec(v_fst_612_);
                        v_a_655_ = crate::leanh::lean_ctor_get(v___x_642_, 0);
                        v_isSharedCheck_662_ = (!crate::leanh::lean_is_exclusive(v___x_642_)) as u8;
                        if v_isSharedCheck_662_ == 0 {
                            v___x_657_ = v___x_642_;
                            v_isShared_658_ = v_isSharedCheck_662_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_655_);
                            crate::leanh::lean_dec(v___x_642_);
                            v___x_657_ = crate::leanh::lean_box(0);
                            v_isShared_658_ = v_isSharedCheck_662_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_637_);
                    crate::leanh::lean_dec(v_fst_620_);
                    crate::leanh::lean_del_object(v___x_618_);
                    crate::leanh::lean_dec(v_fst_616_);
                    crate::leanh::lean_del_object(v___x_614_);
                    crate::leanh::lean_dec(v_fst_612_);
                    crate::leanh::lean_dec(v_snd_611_);
                    v_a_663_ = crate::leanh::lean_ctor_get(v___x_639_, 0);
                    v_isSharedCheck_670_ = (!crate::leanh::lean_is_exclusive(v___x_639_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_665_ = v___x_639_;
                        v_isShared_666_ = v_isSharedCheck_670_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_663_);
                        crate::leanh::lean_dec(v___x_639_);
                        v___x_665_ = crate::leanh::lean_box(0);
                        v_isShared_666_ = v_isSharedCheck_670_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_619_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_618_, 1, v___x_646_);
                    v___x_648_ = v___x_618_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_646_);
                    v___x_648_ = v_reuseFailAlloc_653_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_648_);
                    v___x_650_ = v___x_614_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_652_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_i_600_ = v___x_623_;
                v_b_602_ = v___x_650_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_658_ == 0 {
                    v___x_660_ = v___x_657_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
                    v___x_660_ = v_reuseFailAlloc_661_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_660_;
            }
            11 => {
                if v_isShared_666_ == 0 {
                    v___x_668_ = v___x_665_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
                    v___x_668_ = v_reuseFailAlloc_669_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1___boxed(
    mut v_as_679_: *mut crate::leanh::LeanObject,
    mut v_i_680_: *mut crate::leanh::LeanObject,
    mut v_stop_681_: *mut crate::leanh::LeanObject,
    mut v_b_682_: *mut crate::leanh::LeanObject,
    mut v___y_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_688_: usize = 0;
    let mut v_stop_boxed_689_: usize = 0;
    let mut v_res_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_688_ = crate::leanh::lean_unbox_usize(v_i_680_);
    crate::leanh::lean_dec(v_i_680_);
    v_stop_boxed_689_ = crate::leanh::lean_unbox_usize(v_stop_681_);
    crate::leanh::lean_dec(v_stop_681_);
    v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_as_679_, v_i_boxed_688_, v_stop_boxed_689_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
    crate::leanh::lean_dec(v___y_686_);
    crate::leanh::lean_dec_ref(v___y_685_);
    crate::leanh::lean_dec(v___y_684_);
    crate::leanh::lean_dec_ref(v___y_683_);
    crate::leanh::lean_dec_ref(v_as_679_);
    return v_res_690_;
}
pub unsafe fn l_Lean_Meta_removeUnused(
    mut v_vars_693_: *mut crate::leanh::LeanObject,
    mut v_used_694_: *mut crate::leanh::LeanObject,
    mut v_a_695_: *mut crate::leanh::LeanObject,
    mut v_a_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: u8 = 0;
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: usize = 0;
    let mut v___x_718_: usize = 0;
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_708_ = crate::leanh::lean_ctor_get(v_a_695_, 2);
                v_localInstances_709_ = crate::leanh::lean_ctor_get(v_a_695_, 3);
                v___x_710_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_711_ = l_Lean_Meta_removeUnused___closed__0;
                v___x_712_ = lean_array_get_size(v_vars_693_);
                v___x_713_ = lean_nat_dec_lt(v___x_710_, v___x_712_);
                if v___x_713_ == 0 {
                    crate::leanh::lean_dec_ref(v_used_694_);
                    crate::leanh::lean_inc_ref(v_localInstances_709_);
                    crate::leanh::lean_inc_ref(v_lctx_708_);
                    v_fst_701_ = v_lctx_708_;
                    v_fst_702_ = v_localInstances_709_;
                    v_fst_703_ = v___x_711_;
                    state = 1;
                    continue;
                } else {
                    v___x_714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_714_, 0, v___x_711_);
                    crate::leanh::lean_ctor_set(v___x_714_, 1, v_used_694_);
                    crate::leanh::lean_inc_ref(v_localInstances_709_);
                    v___x_715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_715_, 0, v_localInstances_709_);
                    crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
                    crate::leanh::lean_inc_ref(v_lctx_708_);
                    v___x_716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_716_, 0, v_lctx_708_);
                    crate::leanh::lean_ctor_set(v___x_716_, 1, v___x_715_);
                    v___x_717_ = lean_usize_of_nat(v___x_712_);
                    v___x_718_ = 0usize;
                    v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_removeUnused_spec__1(v_vars_693_, v___x_717_, v___x_718_, v___x_716_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
                    if crate::leanh::lean_obj_tag(v___x_719_) == 0 {
                        v_a_720_ = crate::leanh::lean_ctor_get(v___x_719_, 0);
                        crate::leanh::lean_inc(v_a_720_);
                        crate::leanh::lean_dec_ref_known(v___x_719_, 1);
                        v_snd_721_ = crate::leanh::lean_ctor_get(v_a_720_, 1);
                        crate::leanh::lean_inc(v_snd_721_);
                        v_snd_722_ = crate::leanh::lean_ctor_get(v_snd_721_, 1);
                        crate::leanh::lean_inc(v_snd_722_);
                        v_fst_723_ = crate::leanh::lean_ctor_get(v_a_720_, 0);
                        crate::leanh::lean_inc(v_fst_723_);
                        crate::leanh::lean_dec(v_a_720_);
                        v_fst_724_ = crate::leanh::lean_ctor_get(v_snd_721_, 0);
                        crate::leanh::lean_inc(v_fst_724_);
                        crate::leanh::lean_dec(v_snd_721_);
                        v_fst_725_ = crate::leanh::lean_ctor_get(v_snd_722_, 0);
                        crate::leanh::lean_inc(v_fst_725_);
                        crate::leanh::lean_dec(v_snd_722_);
                        v_fst_701_ = v_fst_723_;
                        v_fst_702_ = v_fst_724_;
                        v_fst_703_ = v_fst_725_;
                        state = 1;
                        continue;
                    } else {
                        v_a_726_ = crate::leanh::lean_ctor_get(v___x_719_, 0);
                        v_isSharedCheck_733_ = (!crate::leanh::lean_is_exclusive(v___x_719_)) as u8;
                        if v_isSharedCheck_733_ == 0 {
                            v___x_728_ = v___x_719_;
                            v_isShared_729_ = v_isSharedCheck_733_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_726_);
                            crate::leanh::lean_dec(v___x_719_);
                            v___x_728_ = crate::leanh::lean_box(0);
                            v_isShared_729_ = v_isSharedCheck_733_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_704_ = l_Array_reverse___redArg(v_fst_703_);
                v___x_705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_705_, 0, v_fst_702_);
                crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_704_);
                v___x_706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_706_, 0, v_fst_701_);
                crate::leanh::lean_ctor_set(v___x_706_, 1, v___x_705_);
                v___x_707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_707_, 0, v___x_706_);
                return v___x_707_;
            }
            2 => {
                if v_isShared_729_ == 0 {
                    v___x_731_ = v___x_728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
                    v___x_731_ = v_reuseFailAlloc_732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_removeUnused___boxed(
    mut v_vars_734_: *mut crate::leanh::LeanObject,
    mut v_used_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
    mut v_a_737_: *mut crate::leanh::LeanObject,
    mut v_a_738_: *mut crate::leanh::LeanObject,
    mut v_a_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Lean_Meta_removeUnused(
        v_vars_734_,
        v_used_735_,
        v_a_736_,
        v_a_737_,
        v_a_738_,
        v_a_739_,
    );
    crate::leanh::lean_dec(v_a_739_);
    crate::leanh::lean_dec_ref(v_a_738_);
    crate::leanh::lean_dec(v_a_737_);
    crate::leanh::lean_dec_ref(v_a_736_);
    crate::leanh::lean_dec_ref(v_vars_734_);
    return v_res_741_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(
    mut v_00_u03b2_742_: *mut crate::leanh::LeanObject,
    mut v_k_743_: *mut crate::leanh::LeanObject,
    mut v_t_744_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_745_: u8 = 0;
    v___x_745_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___redArg(
            v_k_743_, v_t_744_,
        );
    return v___x_745_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0___boxed(
    mut v_00_u03b2_746_: *mut crate::leanh::LeanObject,
    mut v_k_747_: *mut crate::leanh::LeanObject,
    mut v_t_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_749_: u8 = 0;
    let mut v_r_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_removeUnused_spec__0(
        v_00_u03b2_746_,
        v_k_747_,
        v_t_748_,
    );
    crate::leanh::lean_dec(v_t_748_);
    crate::leanh::lean_dec(v_k_747_);
    v_r_750_ = crate::leanh::lean_box((v_res_749_) as usize);
    return v_r_750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CollectFVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CollectFVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CollectFVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CollectFVars(builtin);
}
