// Lean compiler output
// Module: Lean.Meta.Sym.Simp.DiscrTree
// Imports: Lean.Meta.Sym.Pattern Lean.Meta.DiscrTree.Basic Lean.Meta.Sym.Offset Lean.Meta.Sym.Eta Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFn_x21, l_Lean_Expr_bvar___override, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    initialize_Lean_Meta_DiscrTree_Basic, l_Lean_Meta_DiscrTree_Key_lt,
    l_Lean_Meta_DiscrTree_hasNoindexAnnotation, l_Lean_Meta_DiscrTree_insertKeyValue___redArg,
    runtime_initialize_Lean_Meta_DiscrTree_Basic,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::Sym::Eta::{
    initialize_Lean_Meta_Sym_Eta, l_Lean_Meta_Sym_etaReduce, runtime_initialize_Lean_Meta_Sym_Eta,
};
use crate::r#gen::Lean::Meta::Sym::Offset::{
    initialize_Lean_Meta_Sym_Offset, l_Lean_Meta_Sym_isOffset_x27,
    runtime_initialize_Lean_Meta_Sym_Offset,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern, runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Sym_getMatch___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Sym_getMatch___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getMatch___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(
    mut v_infos_622_: *mut LeanObject,
    mut v_i_623_: *mut LeanObject,
) -> u8 {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v___x_624_ = lean_array_get_size(v_infos_622_);
    v___x_625_ = lean_nat_dec_lt(v_i_623_, v___x_624_);
    if v___x_625_ == 0 {
        return v___x_625_;
    } else {
        let mut v_info_626_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isInstance_627_: u8 = 0;
        v_info_626_ = lean_array_fget_borrowed(v_infos_622_, v_i_623_);
        v_isInstance_627_ = lean_ctor_get_uint8(v_info_626_, 1 as u32);
        if v_isInstance_627_ == 0 {
            let mut v_isProof_628_: u8 = 0;
            v_isProof_628_ = lean_ctor_get_uint8(v_info_626_, 0 as u32);
            return v_isProof_628_;
        } else {
            return v_isInstance_627_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg___boxed(
    mut v_infos_629_: *mut LeanObject,
    mut v_i_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_631_: u8 = 0;
    let mut v_r_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_631_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_629_, v_i_630_);
    lean_dec(v_i_630_);
    lean_dec_ref(v_infos_629_);
    v_r_632_ = lean_box((v_res_631_) as usize);
    return v_r_632_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(
    mut v_e_633_: *mut LeanObject,
    mut v_todo_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_633_) == 5 {
                    v_fn_635_ = lean_ctor_get(v_e_633_, 0);
                    lean_inc_ref(v_fn_635_);
                    v_arg_636_ = lean_ctor_get(v_e_633_, 1);
                    lean_inc_ref(v_arg_636_);
                    lean_dec_ref_known(v_e_633_, 2);
                    v___x_637_ = lean_array_push(v_todo_634_, v_arg_636_);
                    v_e_633_ = v_fn_635_;
                    v_todo_634_ = v___x_637_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_e_633_);
                    return v_todo_634_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0()
-> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummyBVar_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = lean_unsigned_to_nat(1000000);
    v_dummyBVar_640_ = l_Lean_Expr_bvar___override(v___x_639_);
    return v_dummyBVar_640_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
    mut v_infos_641_: *mut LeanObject,
    mut v_i_642_: *mut LeanObject,
    mut v_e_643_: *mut LeanObject,
    mut v_todo_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummyBVar_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_643_) == 5 {
                    v_fn_645_ = lean_ctor_get(v_e_643_, 0);
                    lean_inc_ref(v_fn_645_);
                    v_arg_646_ = lean_ctor_get(v_e_643_, 1);
                    lean_inc_ref(v_arg_646_);
                    lean_dec_ref_known(v_e_643_, 2);
                    v___x_647_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(
                            v_infos_641_,
                            v_i_642_,
                        );
                    if v___x_647_ == 0 {
                        v___x_648_ = lean_unsigned_to_nat(1);
                        v___x_649_ = lean_nat_sub(v_i_642_, v___x_648_);
                        lean_dec(v_i_642_);
                        v___x_650_ = lean_array_push(v_todo_644_, v_arg_646_);
                        v_i_642_ = v___x_649_;
                        v_e_643_ = v_fn_645_;
                        v_todo_644_ = v___x_650_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_arg_646_);
                        v_dummyBVar_652_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0);
                        v___x_653_ = lean_unsigned_to_nat(1);
                        v___x_654_ = lean_nat_sub(v_i_642_, v___x_653_);
                        lean_dec(v_i_642_);
                        v___x_655_ = lean_array_push(v_todo_644_, v_dummyBVar_652_);
                        v_i_642_ = v___x_654_;
                        v_e_643_ = v_fn_645_;
                        v_todo_644_ = v___x_655_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_643_);
                    lean_dec(v_i_642_);
                    return v_todo_644_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___boxed(
    mut v_infos_657_: *mut LeanObject,
    mut v_i_658_: *mut LeanObject,
    mut v_e_659_: *mut LeanObject,
    mut v_todo_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_661_: *mut LeanObject = core::ptr::null_mut();
    v_res_661_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
        v_infos_657_,
        v_i_658_,
        v_e_659_,
        v_todo_660_,
    );
    lean_dec_ref(v_infos_657_);
    return v_res_661_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(
    mut v_a_662_: *mut LeanObject,
    mut v_x_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_663_) == 0 {
                    v___x_664_ = lean_box(0);
                    return v___x_664_;
                } else {
                    v_key_665_ = lean_ctor_get(v_x_663_, 0);
                    v_value_666_ = lean_ctor_get(v_x_663_, 1);
                    v_tail_667_ = lean_ctor_get(v_x_663_, 2);
                    v___x_668_ = lean_name_eq(v_key_665_, v_a_662_);
                    if v___x_668_ == 0 {
                        v_x_663_ = v_tail_667_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_666_);
                        v___x_670_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_670_, 0, v_value_666_);
                        return v___x_670_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg___boxed(
    mut v_a_671_: *mut LeanObject,
    mut v_x_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_673_: *mut LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_671_, v_x_672_);
    lean_dec(v_x_672_);
    lean_dec(v_a_671_);
    return v_res_673_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
    mut v_root_674_: u8,
    mut v_fnInfos_675_: *mut LeanObject,
    mut v_todo_676_: *mut LeanObject,
    mut v_e_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_678_: u8 = 0;
    let mut v_fn_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_todo_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_678_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_677_);
                if v___x_678_ == 0 {
                    v_fn_679_ = l_Lean_Expr_getAppFn(v_e_677_);
                    match lean_obj_tag(v_fn_679_) {
                        9 => {
                            lean_dec_ref(v_e_677_);
                            v_a_680_ = lean_ctor_get(v_fn_679_, 0);
                            lean_inc_ref(v_a_680_);
                            lean_dec_ref_known(v_fn_679_, 1);
                            v___x_681_ = lean_alloc_ctor(2, 1, (0) as u32);
                            lean_ctor_set(v___x_681_, 0, v_a_680_);
                            v___x_682_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_682_, 0, v___x_681_);
                            lean_ctor_set(v___x_682_, 1, v_todo_676_);
                            return v___x_682_;
                        }
                        0 => {
                            lean_dec_ref_known(v_fn_679_, 1);
                            lean_dec_ref(v_e_677_);
                            v___x_683_ = lean_box(0);
                            v___x_684_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_684_, 0, v___x_683_);
                            lean_ctor_set(v___x_684_, 1, v_todo_676_);
                            return v___x_684_;
                        }
                        7 => {
                            lean_dec_ref(v_e_677_);
                            v_binderType_685_ = lean_ctor_get(v_fn_679_, 1);
                            lean_inc_ref(v_binderType_685_);
                            v_body_686_ = lean_ctor_get(v_fn_679_, 2);
                            lean_inc_ref(v_body_686_);
                            lean_dec_ref_known(v_fn_679_, 3);
                            v___x_687_ = lean_box(5);
                            v___x_688_ = lean_array_push(v_todo_676_, v_body_686_);
                            v___x_689_ = lean_array_push(v___x_688_, v_binderType_685_);
                            v___x_690_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_690_, 0, v___x_687_);
                            lean_ctor_set(v___x_690_, 1, v___x_689_);
                            return v___x_690_;
                        }
                        4 => {
                            v_declName_691_ = lean_ctor_get(v_fn_679_, 0);
                            lean_inc(v_declName_691_);
                            lean_dec_ref_known(v_fn_679_, 2);
                            if v_root_674_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_678_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_fvarId_709_ = lean_ctor_get(v_fn_679_, 0);
                            lean_inc(v_fvarId_709_);
                            lean_dec_ref_known(v_fn_679_, 1);
                            v_numArgs_710_ = l_Lean_Expr_getAppNumArgs(v_e_677_);
                            v_todo_711_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_677_, v_todo_676_);
                            v___x_712_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v___x_712_, 0, v_fvarId_709_);
                            lean_ctor_set(v___x_712_, 1, v_numArgs_710_);
                            v___x_713_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_713_, 0, v___x_712_);
                            lean_ctor_set(v___x_713_, 1, v_todo_711_);
                            return v___x_713_;
                        }
                        _ => {
                            lean_dec_ref(v_fn_679_);
                            lean_dec_ref(v_e_677_);
                            v___x_714_ = lean_box(1);
                            v___x_715_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_715_, 0, v___x_714_);
                            lean_ctor_set(v___x_715_, 1, v_todo_676_);
                            return v___x_715_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_677_);
                    v___x_716_ = lean_box(0);
                    v___x_717_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_717_, 0, v___x_716_);
                    lean_ctor_set(v___x_717_, 1, v_todo_676_);
                    return v___x_717_;
                }
            }
            1 => {
                v___x_695_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_695_, 0, v_declName_691_);
                lean_ctor_set(v___x_695_, 1, v___y_693_);
                v___x_696_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_696_, 0, v___x_695_);
                lean_ctor_set(v___x_696_, 1, v___y_694_);
                return v___x_696_;
            }
            2 => {
                v_numArgs_698_ = l_Lean_Expr_getAppNumArgs(v_e_677_);
                v___x_699_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_691_, v_fnInfos_675_);
                if lean_obj_tag(v___x_699_) == 1 {
                    v_val_700_ = lean_ctor_get(v___x_699_, 0);
                    lean_inc(v_val_700_);
                    lean_dec_ref_known(v___x_699_, 1);
                    v___x_701_ = lean_unsigned_to_nat(1);
                    v___x_702_ = lean_nat_sub(v_numArgs_698_, v___x_701_);
                    v___x_703_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
                            v_val_700_,
                            v___x_702_,
                            v_e_677_,
                            v_todo_676_,
                        );
                    lean_dec(v_val_700_);
                    v___y_693_ = v_numArgs_698_;
                    v___y_694_ = v___x_703_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_699_);
                    v___x_704_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(
                            v_e_677_,
                            v_todo_676_,
                        );
                    v___y_693_ = v_numArgs_698_;
                    v___y_694_ = v___x_704_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_e_677_);
                v___x_706_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_691_, v_e_677_);
                if v___x_706_ == 0 {
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_declName_691_);
                    lean_dec_ref(v_e_677_);
                    v___x_707_ = lean_box(0);
                    v___x_708_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_708_, 0, v___x_707_);
                    lean_ctor_set(v___x_708_, 1, v_todo_676_);
                    return v___x_708_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(
    mut v_root_718_: *mut LeanObject,
    mut v_fnInfos_719_: *mut LeanObject,
    mut v_todo_720_: *mut LeanObject,
    mut v_e_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_boxed_722_: u8 = 0;
    let mut v_res_723_: *mut LeanObject = core::ptr::null_mut();
    v_root_boxed_722_ = (lean_unbox(v_root_718_) as u8);
    v_res_723_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
        v_root_boxed_722_,
        v_fnInfos_719_,
        v_todo_720_,
        v_e_721_,
    );
    lean_dec(v_fnInfos_719_);
    return v_res_723_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(
    mut v_00_u03b2_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_x_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_725_, v_x_726_);
    return v___x_727_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(
    mut v_00_u03b2_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_x_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_728_, v_a_729_, v_x_730_);
    lean_dec(v_x_730_);
    lean_dec(v_a_729_);
    return v_res_731_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
    mut v_root_732_: u8,
    mut v_fnInfos_733_: *mut LeanObject,
    mut v_todo_734_: *mut LeanObject,
    mut v_keys_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_todo_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_736_ = lean_array_get_size(v_todo_734_);
                v___x_737_ = lean_unsigned_to_nat(0);
                v___x_738_ = lean_nat_dec_eq(v___x_736_, v___x_737_);
                if v___x_738_ == 0 {
                    v___x_739_ = l_Lean_instInhabitedExpr;
                    v___x_740_ = lean_unsigned_to_nat(1);
                    v___x_741_ = lean_nat_sub(v___x_736_, v___x_740_);
                    v_e_742_ = lean_array_get(v___x_739_, v_todo_734_, v___x_741_);
                    lean_dec(v___x_741_);
                    v_todo_743_ = lean_array_pop(v_todo_734_);
                    v___x_744_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
                        v_root_732_,
                        v_fnInfos_733_,
                        v_todo_743_,
                        v_e_742_,
                    );
                    v_fst_745_ = lean_ctor_get(v___x_744_, 0);
                    lean_inc(v_fst_745_);
                    v_snd_746_ = lean_ctor_get(v___x_744_, 1);
                    lean_inc(v_snd_746_);
                    lean_dec_ref(v___x_744_);
                    v___x_747_ = lean_array_push(v_keys_735_, v_fst_745_);
                    v_root_732_ = v___x_738_;
                    v_todo_734_ = v_snd_746_;
                    v_keys_735_ = v___x_747_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_todo_734_);
                    return v_keys_735_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(
    mut v_root_749_: *mut LeanObject,
    mut v_fnInfos_750_: *mut LeanObject,
    mut v_todo_751_: *mut LeanObject,
    mut v_keys_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_boxed_753_: u8 = 0;
    let mut v_res_754_: *mut LeanObject = core::ptr::null_mut();
    v_root_boxed_753_ = (lean_unbox(v_root_749_) as u8);
    v_res_754_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
        v_root_boxed_753_,
        v_fnInfos_750_,
        v_todo_751_,
        v_keys_752_,
    );
    lean_dec(v_fnInfos_750_);
    return v_res_754_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity()
-> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = lean_unsigned_to_nat(8);
    return v___x_755_;
}
pub unsafe fn l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(
    mut v_p_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pattern_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnInfos_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_todo_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v_pattern_757_ = lean_ctor_get(v_p_756_, 3);
    lean_inc_ref(v_pattern_757_);
    v_fnInfos_758_ = lean_ctor_get(v_p_756_, 4);
    lean_inc(v_fnInfos_758_);
    lean_dec_ref(v_p_756_);
    v___x_759_ = lean_unsigned_to_nat(8);
    v_todo_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
    v___x_761_ = 1;
    lean_inc_ref(v_todo_760_);
    v___x_762_ = lean_array_push(v_todo_760_, v_pattern_757_);
    v___x_763_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
        v___x_761_,
        v_fnInfos_758_,
        v___x_762_,
        v_todo_760_,
    );
    lean_dec(v_fnInfos_758_);
    return v___x_763_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___redArg(
    mut v_inst_764_: *mut LeanObject,
    mut v_d_765_: *mut LeanObject,
    mut v_p_766_: *mut LeanObject,
    mut v_v_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keys_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v_keys_768_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_766_);
    v___x_769_ =
        l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_764_, v_d_765_, v_keys_768_, v_v_767_);
    return v___x_769_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern(
    mut v_00_u03b1_770_: *mut LeanObject,
    mut v_inst_771_: *mut LeanObject,
    mut v_d_772_: *mut LeanObject,
    mut v_p_773_: *mut LeanObject,
    mut v_v_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_775_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_771_, v_d_772_, v_p_773_, v_v_774_);
    return v___x_775_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(
    mut v_a_776_: *mut LeanObject,
    mut v_b_777_: *mut LeanObject,
) -> u8 {
    let mut v_fst_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    v_fst_778_ = lean_ctor_get(v_a_776_, 0);
    v_fst_779_ = lean_ctor_get(v_b_777_, 0);
    v___x_780_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_778_, v_fst_779_);
    return v___x_780_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(
    mut v_a_781_: *mut LeanObject,
    mut v_b_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: u8 = 0;
    let mut v_r_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(
            v_a_781_, v_b_782_,
        );
    lean_dec_ref(v_b_782_);
    lean_dec_ref(v_a_781_);
    v_r_784_ = lean_box((v_res_783_) as usize);
    return v_r_784_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(
    mut v_cs_791_: *mut LeanObject,
    mut v_k_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    v___x_793_ = lean_unsigned_to_nat(0);
    v___x_794_ = lean_array_get_size(v_cs_791_);
    v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
    if v___x_795_ == 0 {
        let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_792_);
        v___x_796_ = lean_box(0);
        return v___x_796_;
    } else {
        let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: u8 = 0;
        v___x_797_ = lean_unsigned_to_nat(1);
        v___x_798_ = lean_nat_sub(v___x_794_, v___x_797_);
        v___x_799_ = lean_nat_dec_le(v___x_793_, v___x_798_);
        if v___x_799_ == 0 {
            let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_798_);
            lean_dec(v_k_792_);
            v___x_800_ = lean_box(0);
            return v___x_800_;
        } else {
            let mut v___f_801_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
            v___f_801_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0;
            v___x_802_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
            v___x_803_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_803_, 0, v_k_792_);
            lean_ctor_set(v___x_803_, 1, v___x_802_);
            v___x_804_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3;
            v___x_805_ = l_Array_binSearchAux___redArg(
                v___f_801_, v___x_804_, v_cs_791_, v___x_803_, v___x_793_, v___x_798_,
            );
            return v___x_805_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(
    mut v_cs_806_: *mut LeanObject,
    mut v_k_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(
        v_cs_806_, v_k_807_,
    );
    lean_dec_ref(v_cs_806_);
    return v_res_808_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(
    mut v_00_u03b1_809_: *mut LeanObject,
    mut v_cs_810_: *mut LeanObject,
    mut v_k_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    v___x_812_ = lean_unsigned_to_nat(0);
    v___x_813_ = lean_array_get_size(v_cs_810_);
    v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
    if v___x_814_ == 0 {
        let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_811_);
        v___x_815_ = lean_box(0);
        return v___x_815_;
    } else {
        let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_818_: u8 = 0;
        v___x_816_ = lean_unsigned_to_nat(1);
        v___x_817_ = lean_nat_sub(v___x_813_, v___x_816_);
        v___x_818_ = lean_nat_dec_le(v___x_812_, v___x_817_);
        if v___x_818_ == 0 {
            let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_817_);
            lean_dec(v_k_811_);
            v___x_819_ = lean_box(0);
            return v___x_819_;
        } else {
            let mut v___f_820_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
            v___f_820_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0;
            v___x_821_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
            v___x_822_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_822_, 0, v_k_811_);
            lean_ctor_set(v___x_822_, 1, v___x_821_);
            v___x_823_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3;
            v___x_824_ = l_Array_binSearchAux___redArg(
                v___f_820_, v___x_823_, v_cs_810_, v___x_822_, v___x_812_, v___x_817_,
            );
            return v___x_824_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(
    mut v_00_u03b1_825_: *mut LeanObject,
    mut v_cs_826_: *mut LeanObject,
    mut v_k_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(
        v_00_u03b1_825_,
        v_cs_826_,
        v_k_827_,
    );
    lean_dec_ref(v_cs_826_);
    return v_res_828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(
    mut v_e_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Lean_Expr_getAppFn(v_e_829_);
    match lean_obj_tag(v___x_830_) {
        9 => {
            let mut v_a_831_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
            v_a_831_ = lean_ctor_get(v___x_830_, 0);
            lean_inc_ref(v_a_831_);
            lean_dec_ref_known(v___x_830_, 1);
            v___x_832_ = lean_alloc_ctor(2, 1, (0) as u32);
            lean_ctor_set(v___x_832_, 0, v_a_831_);
            return v___x_832_;
        }
        4 => {
            let mut v_declName_833_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
            v_declName_833_ = lean_ctor_get(v___x_830_, 0);
            lean_inc(v_declName_833_);
            lean_dec_ref_known(v___x_830_, 2);
            v___x_834_ = l_Lean_Expr_getAppNumArgs(v_e_829_);
            v___x_835_ = lean_alloc_ctor(4, 2, (0) as u32);
            lean_ctor_set(v___x_835_, 0, v_declName_833_);
            lean_ctor_set(v___x_835_, 1, v___x_834_);
            return v___x_835_;
        }
        1 => {
            let mut v_fvarId_836_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
            v_fvarId_836_ = lean_ctor_get(v___x_830_, 0);
            lean_inc(v_fvarId_836_);
            lean_dec_ref_known(v___x_830_, 1);
            v___x_837_ = l_Lean_Expr_getAppNumArgs(v_e_829_);
            v___x_838_ = lean_alloc_ctor(3, 2, (0) as u32);
            lean_ctor_set(v___x_838_, 0, v_fvarId_836_);
            lean_ctor_set(v___x_838_, 1, v___x_837_);
            return v___x_838_;
        }
        7 => {
            let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_830_, 3);
            v___x_839_ = lean_box(5);
            return v___x_839_;
        }
        _ => {
            let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_830_);
            v___x_840_ = lean_box(1);
            return v___x_840_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(
    mut v_e_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_841_);
    lean_dec_ref(v_e_841_);
    return v_res_842_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(
    mut v_todo_843_: *mut LeanObject,
    mut v_e_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_844_) {
                5 => {
                    v_fn_845_ = lean_ctor_get(v_e_844_, 0);
                    lean_inc_ref(v_fn_845_);
                    v_arg_846_ = lean_ctor_get(v_e_844_, 1);
                    lean_inc_ref(v_arg_846_);
                    lean_dec_ref_known(v_e_844_, 2);
                    v___x_847_ = lean_array_push(v_todo_843_, v_arg_846_);
                    v_todo_843_ = v___x_847_;
                    v_e_844_ = v_fn_845_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_binderType_849_ = lean_ctor_get(v_e_844_, 1);
                    lean_inc_ref(v_binderType_849_);
                    v_body_850_ = lean_ctor_get(v_e_844_, 2);
                    lean_inc_ref(v_body_850_);
                    lean_dec_ref_known(v_e_844_, 3);
                    v___x_851_ = lean_array_push(v_todo_843_, v_body_850_);
                    v___x_852_ = lean_array_push(v___x_851_, v_binderType_849_);
                    return v___x_852_;
                }
                _ => {
                    lean_dec_ref(v_e_844_);
                    return v_todo_843_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(
    mut v_as_853_: *mut LeanObject,
    mut v_k_854_: *mut LeanObject,
    mut v_x_855_: *mut LeanObject,
    mut v_x_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_857_ = lean_nat_add(v_x_855_, v_x_856_);
                v___x_858_ = lean_unsigned_to_nat(1);
                v_m_859_ = lean_nat_shiftr(v___x_857_, v___x_858_);
                lean_dec(v___x_857_);
                v_a_860_ = lean_array_fget_borrowed(v_as_853_, v_m_859_);
                v___x_861_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_860_, v_k_854_);
                if v___x_861_ == 0 {
                    lean_dec(v_x_856_);
                    v___x_862_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_854_, v_a_860_);
                    if v___x_862_ == 0 {
                        lean_dec(v_m_859_);
                        lean_dec(v_x_855_);
                        lean_inc(v_a_860_);
                        v___x_863_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_863_, 0, v_a_860_);
                        return v___x_863_;
                    } else {
                        v___x_864_ = lean_unsigned_to_nat(0);
                        v___x_865_ = lean_nat_dec_eq(v_m_859_, v___x_864_);
                        if v___x_865_ == 0 {
                            v___x_866_ = lean_nat_sub(v_m_859_, v___x_858_);
                            lean_dec(v_m_859_);
                            v___x_867_ = lean_nat_dec_lt(v___x_866_, v_x_855_);
                            if v___x_867_ == 0 {
                                v_x_856_ = v___x_866_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_866_);
                                lean_dec(v_x_855_);
                                v___x_869_ = lean_box(0);
                                return v___x_869_;
                            }
                        } else {
                            lean_dec(v_m_859_);
                            lean_dec(v_x_855_);
                            v___x_870_ = lean_box(0);
                            return v___x_870_;
                        }
                    }
                } else {
                    lean_dec(v_x_855_);
                    v___x_871_ = lean_nat_add(v_m_859_, v___x_858_);
                    lean_dec(v_m_859_);
                    v___x_872_ = lean_nat_dec_le(v___x_871_, v_x_856_);
                    if v___x_872_ == 0 {
                        lean_dec(v___x_871_);
                        lean_dec(v_x_856_);
                        v___x_873_ = lean_box(0);
                        return v___x_873_;
                    } else {
                        v_x_855_ = v___x_871_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(
    mut v_as_875_: *mut LeanObject,
    mut v_k_876_: *mut LeanObject,
    mut v_x_877_: *mut LeanObject,
    mut v_x_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_879_: *mut LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_875_, v_k_876_, v_x_877_, v_x_878_);
    lean_dec_ref(v_k_876_);
    lean_dec_ref(v_as_875_);
    return v_res_879_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(
    mut v_todo_880_: *mut LeanObject,
    mut v_c_881_: *mut LeanObject,
    mut v_result_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v_csize_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_todo_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_first_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v_fst_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: u8 = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_883_ = lean_ctor_get(v_c_881_, 0);
                v_children_884_ = lean_ctor_get(v_c_881_, 1);
                v_isSharedCheck_931_ = (!lean_is_exclusive(v_c_881_)) as u8;
                if v_isSharedCheck_931_ == 0 {
                    v___x_886_ = v_c_881_;
                    v_isShared_887_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_884_);
                    lean_inc(v_vs_883_);
                    lean_dec(v_c_881_);
                    v___x_886_ = lean_box(0);
                    v_isShared_887_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_888_ = lean_array_get_size(v_todo_880_);
                v___x_889_ = lean_unsigned_to_nat(0);
                v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
                if v___x_890_ == 0 {
                    lean_dec_ref(v_vs_883_);
                    v_csize_891_ = lean_array_get_size(v_children_884_);
                    v___x_892_ = lean_nat_dec_eq(v_csize_891_, v___x_889_);
                    if v___x_892_ == 0 {
                        v___x_893_ = l_Lean_instInhabitedExpr;
                        v___x_894_ = lean_unsigned_to_nat(1);
                        v___x_895_ = lean_nat_sub(v___x_888_, v___x_894_);
                        v___x_896_ = lean_array_get_borrowed(v___x_893_, v_todo_880_, v___x_895_);
                        lean_dec(v___x_895_);
                        v_e_897_ = l_Lean_Meta_Sym_etaReduce(v___x_896_);
                        v_todo_898_ = lean_array_pop(v_todo_880_);
                        v_first_914_ = lean_array_fget_borrowed(v_children_884_, v___x_889_);
                        v___x_915_ = lean_nat_dec_eq(v_csize_891_, v___x_894_);
                        if v___x_915_ == 0 {
                            v_fst_916_ = lean_ctor_get(v_first_914_, 0);
                            v_snd_917_ = lean_ctor_get(v_first_914_, 1);
                            v___x_918_ = lean_box(0);
                            v___x_919_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_916_, v___x_918_);
                            if v___x_919_ == 0 {
                                v___y_900_ = v_result_882_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_snd_917_);
                                lean_inc_ref(v_todo_898_);
                                v___x_920_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_898_, v_snd_917_, v_result_882_);
                                v___y_900_ = v___x_920_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc(v_first_914_);
                            lean_del_object(v___x_886_);
                            lean_dec_ref(v_children_884_);
                            v_fst_921_ = lean_ctor_get(v_first_914_, 0);
                            lean_inc(v_fst_921_);
                            v_snd_922_ = lean_ctor_get(v_first_914_, 1);
                            lean_inc(v_snd_922_);
                            lean_dec(v_first_914_);
                            v___x_923_ = lean_box(0);
                            v___x_924_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_921_, v___x_923_);
                            if v___x_924_ == 0 {
                                v___x_925_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_897_);
                                v___x_926_ =
                                    l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_921_, v___x_925_);
                                lean_dec(v___x_925_);
                                lean_dec(v_fst_921_);
                                if v___x_926_ == 0 {
                                    lean_dec(v_snd_922_);
                                    lean_dec_ref(v_todo_898_);
                                    lean_dec_ref(v_e_897_);
                                    return v_result_882_;
                                } else {
                                    v___x_927_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_898_, v_e_897_);
                                    v_todo_880_ = v___x_927_;
                                    v_c_881_ = v_snd_922_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fst_921_);
                                lean_dec_ref(v_e_897_);
                                v_todo_880_ = v_todo_898_;
                                v_c_881_ = v_snd_922_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_886_);
                        lean_dec_ref(v_children_884_);
                        lean_dec_ref(v_todo_880_);
                        return v_result_882_;
                    }
                } else {
                    lean_del_object(v___x_886_);
                    lean_dec_ref(v_children_884_);
                    lean_dec_ref(v_todo_880_);
                    v___x_930_ = l_Array_append___redArg(v_result_882_, v_vs_883_);
                    lean_dec_ref(v_vs_883_);
                    return v___x_930_;
                }
            }
            2 => {
                v___x_901_ = lean_nat_dec_lt(v___x_889_, v_csize_891_);
                if v___x_901_ == 0 {
                    lean_dec_ref(v_todo_898_);
                    lean_dec_ref(v_e_897_);
                    lean_del_object(v___x_886_);
                    lean_dec_ref(v_children_884_);
                    return v___y_900_;
                } else {
                    v___x_902_ = lean_nat_sub(v_csize_891_, v___x_894_);
                    v___x_903_ = lean_nat_dec_le(v___x_889_, v___x_902_);
                    if v___x_903_ == 0 {
                        lean_dec(v___x_902_);
                        lean_dec_ref(v_todo_898_);
                        lean_dec_ref(v_e_897_);
                        lean_del_object(v___x_886_);
                        lean_dec_ref(v_children_884_);
                        return v___y_900_;
                    } else {
                        v___x_904_ =
                            l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(
                                v_e_897_,
                            );
                        v___x_905_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
                        if v_isShared_887_ == 0 {
                            lean_ctor_set(v___x_886_, 1, v___x_905_);
                            lean_ctor_set(v___x_886_, 0, v___x_904_);
                            v___x_907_ = v___x_886_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_904_);
                            lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_905_);
                            v___x_907_ = v_reuseFailAlloc_913_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_908_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_884_, v___x_907_, v___x_889_, v___x_902_);
                lean_dec_ref(v___x_907_);
                lean_dec_ref(v_children_884_);
                if lean_obj_tag(v___x_908_) == 0 {
                    lean_dec_ref(v_todo_898_);
                    lean_dec_ref(v_e_897_);
                    return v___y_900_;
                } else {
                    v_val_909_ = lean_ctor_get(v___x_908_, 0);
                    lean_inc(v_val_909_);
                    lean_dec_ref_known(v___x_908_, 1);
                    v_snd_910_ = lean_ctor_get(v_val_909_, 1);
                    lean_inc(v_snd_910_);
                    lean_dec(v_val_909_);
                    v___x_911_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(
                            v_todo_898_,
                            v_e_897_,
                        );
                    v_todo_880_ = v___x_911_;
                    v_c_881_ = v_snd_910_;
                    v_result_882_ = v___y_900_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(
    mut v_00_u03b1_932_: *mut LeanObject,
    mut v_todo_933_: *mut LeanObject,
    mut v_c_934_: *mut LeanObject,
    mut v_result_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    v___x_936_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(
        v_todo_933_,
        v_c_934_,
        v_result_935_,
    );
    return v___x_936_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(
    mut v_00_u03b1_937_: *mut LeanObject,
    mut v_as_938_: *mut LeanObject,
    mut v_k_939_: *mut LeanObject,
    mut v_x_940_: *mut LeanObject,
    mut v_x_941_: *mut LeanObject,
    mut v_x_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_938_, v_k_939_, v_x_940_, v_x_941_);
    return v___x_943_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(
    mut v_00_u03b1_944_: *mut LeanObject,
    mut v_as_945_: *mut LeanObject,
    mut v_k_946_: *mut LeanObject,
    mut v_x_947_: *mut LeanObject,
    mut v_x_948_: *mut LeanObject,
    mut v_x_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_944_, v_as_945_, v_k_946_, v_x_947_, v_x_948_, v_x_949_);
    lean_dec_ref(v_k_946_);
    lean_dec_ref(v_as_945_);
    return v_res_950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(
    mut v_keys_951_: *mut LeanObject,
    mut v_vals_952_: *mut LeanObject,
    mut v_i_953_: *mut LeanObject,
    mut v_k_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_955_ = lean_array_get_size(v_keys_951_);
                v___x_956_ = lean_nat_dec_lt(v_i_953_, v___x_955_);
                if v___x_956_ == 0 {
                    lean_dec(v_i_953_);
                    v___x_957_ = lean_box(0);
                    return v___x_957_;
                } else {
                    v_k_x27_958_ = lean_array_fget_borrowed(v_keys_951_, v_i_953_);
                    v___x_959_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_954_, v_k_x27_958_);
                    if v___x_959_ == 0 {
                        v___x_960_ = lean_unsigned_to_nat(1);
                        v___x_961_ = lean_nat_add(v_i_953_, v___x_960_);
                        lean_dec(v_i_953_);
                        v_i_953_ = v___x_961_;
                        state = 0;
                        continue;
                    } else {
                        v___x_963_ = lean_array_fget_borrowed(v_vals_952_, v_i_953_);
                        lean_dec(v_i_953_);
                        lean_inc(v___x_963_);
                        v___x_964_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_964_, 0, v___x_963_);
                        return v___x_964_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_965_: *mut LeanObject,
    mut v_vals_966_: *mut LeanObject,
    mut v_i_967_: *mut LeanObject,
    mut v_k_968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_969_: *mut LeanObject = core::ptr::null_mut();
    v_res_969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_965_, v_vals_966_, v_i_967_, v_k_968_);
    lean_dec(v_k_968_);
    lean_dec_ref(v_vals_966_);
    lean_dec_ref(v_keys_965_);
    return v_res_969_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_970_: usize = 0;
    let mut v___x_971_: usize = 0;
    let mut v___x_972_: usize = 0;
    v___x_970_ = 5usize;
    v___x_971_ = 1usize;
    v___x_972_ = lean_usize_shift_left(v___x_971_, v___x_970_);
    return v___x_972_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_973_: usize = 0;
    let mut v___x_974_: usize = 0;
    let mut v___x_975_: usize = 0;
    v___x_973_ = 1usize;
    v___x_974_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0);
    v___x_975_ = lean_usize_sub(v___x_974_, v___x_973_);
    return v___x_975_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(
    mut v_x_976_: *mut LeanObject,
    mut v_x_977_: usize,
    mut v_x_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: usize = 0;
    let mut v___x_982_: usize = 0;
    let mut v___x_983_: usize = 0;
    let mut v_j_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: usize = 0;
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_976_) == 0 {
                    v_es_979_ = lean_ctor_get(v_x_976_, 0);
                    v___x_980_ = lean_box(2);
                    v___x_981_ = 5usize;
                    v___x_982_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1);
                    v___x_983_ = lean_usize_land(v_x_977_, v___x_982_);
                    v_j_984_ = lean_usize_to_nat(v___x_983_);
                    v___x_985_ = lean_array_get_borrowed(v___x_980_, v_es_979_, v_j_984_);
                    lean_dec(v_j_984_);
                    match lean_obj_tag(v___x_985_) {
                        0 => {
                            v_key_986_ = lean_ctor_get(v___x_985_, 0);
                            v_val_987_ = lean_ctor_get(v___x_985_, 1);
                            v___x_988_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_978_, v_key_986_);
                            if v___x_988_ == 0 {
                                v___x_989_ = lean_box(0);
                                return v___x_989_;
                            } else {
                                lean_inc(v_val_987_);
                                v___x_990_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_990_, 0, v_val_987_);
                                return v___x_990_;
                            }
                        }
                        1 => {
                            v_node_991_ = lean_ctor_get(v___x_985_, 0);
                            v___x_992_ = lean_usize_shift_right(v_x_977_, v___x_981_);
                            v_x_976_ = v_node_991_;
                            v_x_977_ = v___x_992_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_994_ = lean_box(0);
                            return v___x_994_;
                        }
                    }
                } else {
                    v_ks_995_ = lean_ctor_get(v_x_976_, 0);
                    v_vs_996_ = lean_ctor_get(v_x_976_, 1);
                    v___x_997_ = lean_unsigned_to_nat(0);
                    v___x_998_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_995_, v_vs_996_, v___x_997_, v_x_978_);
                    return v___x_998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(
    mut v_x_999_: *mut LeanObject,
    mut v_x_1000_: *mut LeanObject,
    mut v_x_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_205__boxed_1002_: usize = 0;
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_x_205__boxed_1002_ = lean_unbox_usize(v_x_1000_);
    lean_dec(v_x_1000_);
    v_res_1003_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_999_, v_x_205__boxed_1002_, v_x_1001_);
    lean_dec(v_x_1001_);
    lean_dec_ref(v_x_999_);
    return v_res_1003_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
    mut v_x_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1006_: u64 = 0;
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1005_);
    v___x_1007_ = lean_uint64_to_usize(v___x_1006_);
    v___x_1008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_1004_, v___x_1007_, v_x_1005_);
    return v___x_1008_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(
    mut v_x_1009_: *mut LeanObject,
    mut v_x_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1011_: *mut LeanObject = core::ptr::null_mut();
    v_res_1011_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
            v_x_1009_, v_x_1010_,
        );
    lean_dec(v_x_1010_);
    lean_dec_ref(v_x_1009_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch___redArg(
    mut v_d_1014_: *mut LeanObject,
    mut v_e_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1025_ = lean_box(0);
                v___x_1026_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_1014_, v___x_1025_);
                if lean_obj_tag(v___x_1026_) == 0 {
                    v___x_1027_ = lean_unsigned_to_nat(8);
                    v___x_1028_ = lean_mk_empty_array_with_capacity(v___x_1027_);
                    v___y_1017_ = v___x_1028_;
                    state = 1;
                    continue;
                } else {
                    v_val_1029_ = lean_ctor_get(v___x_1026_, 0);
                    lean_inc(v_val_1029_);
                    lean_dec_ref_known(v___x_1026_, 1);
                    v_vs_1030_ = lean_ctor_get(v_val_1029_, 0);
                    lean_inc_ref(v_vs_1030_);
                    lean_dec(v_val_1029_);
                    v___y_1017_ = v_vs_1030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_e_1018_ = l_Lean_Meta_Sym_etaReduce(v_e_1015_);
                v___x_1019_ =
                    l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_1018_);
                v___x_1020_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_1014_, v___x_1019_);
                lean_dec(v___x_1019_);
                if lean_obj_tag(v___x_1020_) == 0 {
                    lean_dec_ref(v_e_1018_);
                    return v___y_1017_;
                } else {
                    v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
                    lean_inc(v_val_1021_);
                    lean_dec_ref_known(v___x_1020_, 1);
                    v___x_1022_ = l_Lean_Meta_Sym_getMatch___redArg___closed__0;
                    v___x_1023_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(
                            v___x_1022_,
                            v_e_1018_,
                        );
                    v___x_1024_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v___x_1023_, v_val_1021_, v___y_1017_);
                    return v___x_1024_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getMatch___redArg___boxed(
    mut v_d_1031_: *mut LeanObject,
    mut v_e_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1033_: *mut LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1031_, v_e_1032_);
    lean_dec_ref(v_e_1032_);
    lean_dec_ref(v_d_1031_);
    return v_res_1033_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch(
    mut v_00_u03b1_1034_: *mut LeanObject,
    mut v_d_1035_: *mut LeanObject,
    mut v_e_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1035_, v_e_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch___boxed(
    mut v_00_u03b1_1038_: *mut LeanObject,
    mut v_d_1039_: *mut LeanObject,
    mut v_e_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1041_: *mut LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_1038_, v_d_1039_, v_e_1040_);
    lean_dec_ref(v_e_1040_);
    lean_dec_ref(v_d_1039_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(
    mut v_00_u03b2_1042_: *mut LeanObject,
    mut v_x_1043_: *mut LeanObject,
    mut v_x_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
            v_x_1043_, v_x_1044_,
        );
    return v___x_1045_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(
    mut v_00_u03b2_1046_: *mut LeanObject,
    mut v_x_1047_: *mut LeanObject,
    mut v_x_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1049_: *mut LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(
        v_00_u03b2_1046_,
        v_x_1047_,
        v_x_1048_,
    );
    lean_dec(v_x_1048_);
    lean_dec_ref(v_x_1047_);
    return v_res_1049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(
    mut v_00_u03b2_1050_: *mut LeanObject,
    mut v_x_1051_: *mut LeanObject,
    mut v_x_1052_: usize,
    mut v_x_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(
    mut v_00_u03b2_1055_: *mut LeanObject,
    mut v_x_1056_: *mut LeanObject,
    mut v_x_1057_: *mut LeanObject,
    mut v_x_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_315__boxed_1059_: usize = 0;
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_x_315__boxed_1059_ = lean_unbox_usize(v_x_1057_);
    lean_dec(v_x_1057_);
    v_res_1060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_1055_, v_x_1056_, v_x_315__boxed_1059_, v_x_1058_);
    lean_dec(v_x_1058_);
    lean_dec_ref(v_x_1056_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1061_: *mut LeanObject,
    mut v_keys_1062_: *mut LeanObject,
    mut v_vals_1063_: *mut LeanObject,
    mut v_heq_1064_: *mut LeanObject,
    mut v_i_1065_: *mut LeanObject,
    mut v_k_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1065_, v_k_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1068_: *mut LeanObject,
    mut v_keys_1069_: *mut LeanObject,
    mut v_vals_1070_: *mut LeanObject,
    mut v_heq_1071_: *mut LeanObject,
    mut v_i_1072_: *mut LeanObject,
    mut v_k_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_1068_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_k_1073_);
    lean_dec(v_k_1073_);
    lean_dec_ref(v_vals_1070_);
    lean_dec_ref(v_keys_1069_);
    return v_res_1074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(
    mut v_d_1075_: *mut LeanObject,
    mut v_k_1076_: *mut LeanObject,
) -> u8 {
    let mut v_k_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v_a_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v_zero_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1088_: u8 = 0;
    let mut v_one_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v_zero_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1102_: u8 = 0;
    let mut v_one_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v___x_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_k_1076_) {
                4 => {
                    v_a_1082_ = lean_ctor_get(v_k_1076_, 0);
                    v_a_1083_ = lean_ctor_get(v_k_1076_, 1);
                    v_isSharedCheck_1095_ = (!lean_is_exclusive(v_k_1076_)) as u8;
                    if v_isSharedCheck_1095_ == 0 {
                        v___x_1085_ = v_k_1076_;
                        v_isShared_1086_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1083_);
                        lean_inc(v_a_1082_);
                        lean_dec(v_k_1076_);
                        v___x_1085_ = lean_box(0);
                        v_isShared_1086_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    v_a_1096_ = lean_ctor_get(v_k_1076_, 0);
                    v_a_1097_ = lean_ctor_get(v_k_1076_, 1);
                    v_isSharedCheck_1109_ = (!lean_is_exclusive(v_k_1076_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1099_ = v_k_1076_;
                        v_isShared_1100_ = v_isSharedCheck_1109_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1097_);
                        lean_inc(v_a_1096_);
                        lean_dec(v_k_1076_);
                        v___x_1099_ = lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1109_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_k_1076_);
                    v___x_1110_ = 0;
                    return v___x_1110_;
                }
            },
            1 => {
                v___x_1079_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_1075_, v_k_1078_);
                if lean_obj_tag(v___x_1079_) == 0 {
                    v_k_1076_ = v_k_1078_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_1079_, 1);
                    lean_dec(v_k_1078_);
                    v___x_1081_ = 1;
                    return v___x_1081_;
                }
            }
            2 => {
                v_zero_1087_ = lean_unsigned_to_nat(0);
                v_isZero_1088_ = lean_nat_dec_eq(v_a_1083_, v_zero_1087_);
                if v_isZero_1088_ == 0 {
                    v_one_1089_ = lean_unsigned_to_nat(1);
                    v_n_1090_ = lean_nat_sub(v_a_1083_, v_one_1089_);
                    lean_dec(v_a_1083_);
                    if v_isShared_1086_ == 0 {
                        lean_ctor_set(v___x_1085_, 1, v_n_1090_);
                        v___x_1092_ = v___x_1085_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1093_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1082_);
                        lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_n_1090_);
                        v___x_1092_ = v_reuseFailAlloc_1093_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1085_);
                    lean_dec(v_a_1083_);
                    lean_dec(v_a_1082_);
                    v___x_1094_ = 0;
                    return v___x_1094_;
                }
            }
            3 => {
                v_k_1078_ = v___x_1092_;
                state = 1;
                continue;
            }
            4 => {
                v_zero_1101_ = lean_unsigned_to_nat(0);
                v_isZero_1102_ = lean_nat_dec_eq(v_a_1097_, v_zero_1101_);
                if v_isZero_1102_ == 0 {
                    v_one_1103_ = lean_unsigned_to_nat(1);
                    v_n_1104_ = lean_nat_sub(v_a_1097_, v_one_1103_);
                    lean_dec(v_a_1097_);
                    if v_isShared_1100_ == 0 {
                        lean_ctor_set(v___x_1099_, 1, v_n_1104_);
                        v___x_1106_ = v___x_1099_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1107_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1096_);
                        lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_n_1104_);
                        v___x_1106_ = v_reuseFailAlloc_1107_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1099_);
                    lean_dec(v_a_1097_);
                    lean_dec(v_a_1096_);
                    v___x_1108_ = 0;
                    return v___x_1108_;
                }
            }
            5 => {
                v_k_1078_ = v___x_1106_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(
    mut v_d_1111_: *mut LeanObject,
    mut v_k_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: u8 = 0;
    let mut v_r_1114_: *mut LeanObject = core::ptr::null_mut();
    v_res_1113_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1111_, v_k_1112_);
    lean_dec_ref(v_d_1111_);
    v_r_1114_ = lean_box((v_res_1113_) as usize);
    return v_r_1114_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(
    mut v_00_u03b1_1115_: *mut LeanObject,
    mut v_d_1116_: *mut LeanObject,
    mut v_k_1117_: *mut LeanObject,
) -> u8 {
    let mut v___x_1118_: u8 = 0;
    v___x_1118_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1116_, v_k_1117_);
    return v___x_1118_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(
    mut v_00_u03b1_1119_: *mut LeanObject,
    mut v_d_1120_: *mut LeanObject,
    mut v_k_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: u8 = 0;
    let mut v_r_1123_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(
            v_00_u03b1_1119_,
            v_d_1120_,
            v_k_1121_,
        );
    lean_dec_ref(v_d_1120_);
    v_r_1123_ = lean_box((v_res_1122_) as usize);
    return v_r_1123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(
    mut v_numExtra_1124_: *mut LeanObject,
    mut v_sz_1125_: usize,
    mut v_i_1126_: usize,
    mut v_bs_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1128_: u8 = 0;
    let mut v_v_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: usize = 0;
    let mut v___x_1134_: usize = 0;
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = lean_usize_dec_lt(v_i_1126_, v_sz_1125_);
                if v___x_1128_ == 0 {
                    lean_dec(v_numExtra_1124_);
                    return v_bs_1127_;
                } else {
                    v_v_1129_ = lean_array_uget(v_bs_1127_, v_i_1126_);
                    v___x_1130_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1131_ = lean_array_uset(v_bs_1127_, v_i_1126_, v___x_1130_);
                    lean_inc(v_numExtra_1124_);
                    v___x_1132_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1132_, 0, v_v_1129_);
                    lean_ctor_set(v___x_1132_, 1, v_numExtra_1124_);
                    v___x_1133_ = 1usize;
                    v___x_1134_ = lean_usize_add(v_i_1126_, v___x_1133_);
                    v___x_1135_ = lean_array_uset(v_bs_x27_1131_, v_i_1126_, v___x_1132_);
                    v_i_1126_ = v___x_1134_;
                    v_bs_1127_ = v___x_1135_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(
    mut v_numExtra_1137_: *mut LeanObject,
    mut v_sz_1138_: *mut LeanObject,
    mut v_i_1139_: *mut LeanObject,
    mut v_bs_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1141_: usize = 0;
    let mut v_i_boxed_1142_: usize = 0;
    let mut v_res_1143_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1138_);
    lean_dec(v_sz_1138_);
    v_i_boxed_1142_ = lean_unbox_usize(v_i_1139_);
    lean_dec(v_i_1139_);
    v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1137_, v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1140_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(
    mut v_d_1144_: *mut LeanObject,
    mut v_e_1145_: *mut LeanObject,
    mut v_numExtra_1146_: *mut LeanObject,
    mut v_result_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1149_: usize = 0;
    let mut v___x_1150_: usize = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1144_, v_e_1145_);
                v_sz_1149_ = lean_array_size(v___x_1148_);
                v___x_1150_ = 0usize;
                lean_inc(v_numExtra_1146_);
                v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1146_, v_sz_1149_, v___x_1150_, v___x_1148_);
                v_result_1152_ = l_Array_append___redArg(v_result_1147_, v___x_1151_);
                lean_dec_ref(v___x_1151_);
                v___x_1153_ = l_Lean_Expr_isApp(v_e_1145_);
                if v___x_1153_ == 0 {
                    lean_dec(v_numExtra_1146_);
                    lean_dec_ref(v_e_1145_);
                    return v_result_1152_;
                } else {
                    v___x_1154_ = l_Lean_Expr_appFn_x21(v_e_1145_);
                    lean_dec_ref(v_e_1145_);
                    v___x_1155_ = lean_unsigned_to_nat(1);
                    v___x_1156_ = lean_nat_add(v_numExtra_1146_, v___x_1155_);
                    lean_dec(v_numExtra_1146_);
                    v_e_1145_ = v___x_1154_;
                    v_numExtra_1146_ = v___x_1156_;
                    v_result_1147_ = v_result_1152_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(
    mut v_d_1158_: *mut LeanObject,
    mut v_e_1159_: *mut LeanObject,
    mut v_numExtra_1160_: *mut LeanObject,
    mut v_result_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1162_: *mut LeanObject = core::ptr::null_mut();
    v_res_1162_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(
            v_d_1158_,
            v_e_1159_,
            v_numExtra_1160_,
            v_result_1161_,
        );
    lean_dec_ref(v_d_1158_);
    return v_res_1162_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(
    mut v_00_u03b1_1163_: *mut LeanObject,
    mut v_d_1164_: *mut LeanObject,
    mut v_e_1165_: *mut LeanObject,
    mut v_numExtra_1166_: *mut LeanObject,
    mut v_result_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    v___x_1168_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(
            v_d_1164_,
            v_e_1165_,
            v_numExtra_1166_,
            v_result_1167_,
        );
    return v___x_1168_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(
    mut v_00_u03b1_1169_: *mut LeanObject,
    mut v_d_1170_: *mut LeanObject,
    mut v_e_1171_: *mut LeanObject,
    mut v_numExtra_1172_: *mut LeanObject,
    mut v_result_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1174_: *mut LeanObject = core::ptr::null_mut();
    v_res_1174_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(
        v_00_u03b1_1169_,
        v_d_1170_,
        v_e_1171_,
        v_numExtra_1172_,
        v_result_1173_,
    );
    lean_dec_ref(v_d_1170_);
    return v_res_1174_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(
    mut v_00_u03b1_1175_: *mut LeanObject,
    mut v_numExtra_1176_: *mut LeanObject,
    mut v_sz_1177_: usize,
    mut v_i_1178_: usize,
    mut v_bs_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1176_, v_sz_1177_, v_i_1178_, v_bs_1179_);
    return v___x_1180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(
    mut v_00_u03b1_1181_: *mut LeanObject,
    mut v_numExtra_1182_: *mut LeanObject,
    mut v_sz_1183_: *mut LeanObject,
    mut v_i_1184_: *mut LeanObject,
    mut v_bs_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1186_: usize = 0;
    let mut v_i_boxed_1187_: usize = 0;
    let mut v_res_1188_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1186_ = lean_unbox_usize(v_sz_1183_);
    lean_dec(v_sz_1183_);
    v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
    lean_dec(v_i_1184_);
    v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_1181_, v_numExtra_1182_, v_sz_boxed_1186_, v_i_boxed_1187_, v_bs_1185_);
    return v_res_1188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(
    mut v_sz_1189_: usize,
    mut v_i_1190_: usize,
    mut v_bs_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v_v_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = lean_usize_dec_lt(v_i_1190_, v_sz_1189_);
                if v___x_1192_ == 0 {
                    return v_bs_1191_;
                } else {
                    v_v_1193_ = lean_array_uget(v_bs_1191_, v_i_1190_);
                    v___x_1194_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1195_ = lean_array_uset(v_bs_1191_, v_i_1190_, v___x_1194_);
                    v___x_1196_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1196_, 0, v_v_1193_);
                    lean_ctor_set(v___x_1196_, 1, v___x_1194_);
                    v___x_1197_ = 1usize;
                    v___x_1198_ = lean_usize_add(v_i_1190_, v___x_1197_);
                    v___x_1199_ = lean_array_uset(v_bs_x27_1195_, v_i_1190_, v___x_1196_);
                    v_i_1190_ = v___x_1198_;
                    v_bs_1191_ = v___x_1199_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(
    mut v_sz_1201_: *mut LeanObject,
    mut v_i_1202_: *mut LeanObject,
    mut v_bs_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1204_: usize = 0;
    let mut v_i_boxed_1205_: usize = 0;
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1204_ = lean_unbox_usize(v_sz_1201_);
    lean_dec(v_sz_1201_);
    v_i_boxed_1205_ = lean_unbox_usize(v_i_1202_);
    lean_dec(v_i_1202_);
    v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_1204_, v_i_boxed_1205_, v_bs_1203_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___redArg(
    mut v_d_1207_: *mut LeanObject,
    mut v_e_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1211_: usize = 0;
    let mut v___x_1212_: usize = 0;
    let mut v_result_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: u8 = 0;
    v_e_1209_ = l_Lean_Meta_Sym_etaReduce(v_e_1208_);
    v_result_1210_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1207_, v_e_1209_);
    v_sz_1211_ = lean_array_size(v_result_1210_);
    v___x_1212_ = 0usize;
    v_result_1213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_1211_, v___x_1212_, v_result_1210_);
    v___x_1214_ = l_Lean_Expr_isApp(v_e_1209_);
    if v___x_1214_ == 0 {
        lean_dec_ref(v_e_1209_);
        return v_result_1213_;
    } else {
        let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: u8 = 0;
        v___x_1215_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_1209_);
        v___x_1216_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1207_, v___x_1215_);
        if v___x_1216_ == 0 {
            lean_dec_ref(v_e_1209_);
            return v_result_1213_;
        } else {
            let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
            v___x_1217_ = l_Lean_Expr_appFn_x21(v_e_1209_);
            lean_dec_ref(v_e_1209_);
            v___x_1218_ = lean_unsigned_to_nat(1);
            v___x_1219_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_1207_, v___x_1217_, v___x_1218_, v_result_1213_);
            return v___x_1219_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(
    mut v_d_1220_: *mut LeanObject,
    mut v_e_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1222_: *mut LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_1220_, v_e_1221_);
    lean_dec_ref(v_e_1221_);
    lean_dec_ref(v_d_1220_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra(
    mut v_00_u03b1_1223_: *mut LeanObject,
    mut v_d_1224_: *mut LeanObject,
    mut v_e_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    v___x_1226_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_1224_, v_e_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___boxed(
    mut v_00_u03b1_1227_: *mut LeanObject,
    mut v_d_1228_: *mut LeanObject,
    mut v_e_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1230_: *mut LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_1227_, v_d_1228_, v_e_1229_);
    lean_dec_ref(v_e_1229_);
    lean_dec_ref(v_d_1228_);
    return v_res_1230_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(
    mut v_00_u03b1_1231_: *mut LeanObject,
    mut v_sz_1232_: usize,
    mut v_i_1233_: usize,
    mut v_bs_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_1232_, v_i_1233_, v_bs_1234_);
    return v___x_1235_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(
    mut v_00_u03b1_1236_: *mut LeanObject,
    mut v_sz_1237_: *mut LeanObject,
    mut v_i_1238_: *mut LeanObject,
    mut v_bs_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1240_: usize = 0;
    let mut v_i_boxed_1241_: usize = 0;
    let mut v_res_1242_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1240_ = lean_unbox_usize(v_sz_1237_);
    lean_dec(v_sz_1237_);
    v_i_boxed_1241_ = lean_unbox_usize(v_i_1238_);
    lean_dec(v_i_1238_);
    v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_1236_, v_sz_boxed_1240_, v_i_boxed_1241_, v_bs_1239_);
    return v_res_1242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity =
        _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity();
    lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
}
