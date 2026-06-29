// Lean compiler output
// Module: Lean.Meta.Sym.Simp.DiscrTree
// Imports: Lean.Meta.Sym.Pattern Lean.Meta.DiscrTree.Basic Lean.Meta.Sym.Offset Lean.Meta.Sym.Eta Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_pop, lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Sym_getMatch___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_getMatch___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getMatch___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(
    mut v_infos_622_: *mut crate::leanh::LeanObject,
    mut v_i_623_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v___x_624_ = lean_array_get_size(v_infos_622_);
    v___x_625_ = lean_nat_dec_lt(v_i_623_, v___x_624_);
    if v___x_625_ == 0 {
        return v___x_625_;
    } else {
        let mut v_info_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isInstance_627_: u8 = 0;
        v_info_626_ = lean_array_fget_borrowed(v_infos_622_, v_i_623_);
        v_isInstance_627_ = crate::leanh::lean_ctor_get_uint8(v_info_626_, 1 as u32);
        if v_isInstance_627_ == 0 {
            let mut v_isProof_628_: u8 = 0;
            v_isProof_628_ = crate::leanh::lean_ctor_get_uint8(v_info_626_, 0 as u32);
            return v_isProof_628_;
        } else {
            return v_isInstance_627_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg___boxed(
    mut v_infos_629_: *mut crate::leanh::LeanObject,
    mut v_i_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_631_: u8 = 0;
    let mut v_r_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_631_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_629_, v_i_630_);
    crate::leanh::lean_dec(v_i_630_);
    crate::leanh::lean_dec_ref(v_infos_629_);
    v_r_632_ = crate::leanh::lean_box((v_res_631_) as usize);
    return v_r_632_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(
    mut v_e_633_: *mut crate::leanh::LeanObject,
    mut v_todo_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_633_) == 5 {
                    v_fn_635_ = crate::leanh::lean_ctor_get(v_e_633_, 0);
                    crate::leanh::lean_inc_ref(v_fn_635_);
                    v_arg_636_ = crate::leanh::lean_ctor_get(v_e_633_, 1);
                    crate::leanh::lean_inc_ref(v_arg_636_);
                    crate::leanh::lean_dec_ref_known(v_e_633_, 2);
                    v___x_637_ = lean_array_push(v_todo_634_, v_arg_636_);
                    v_e_633_ = v_fn_635_;
                    v_todo_634_ = v___x_637_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_633_);
                    return v_todo_634_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummyBVar_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v_dummyBVar_640_ = l_Lean_Expr_bvar___override(v___x_639_);
    return v_dummyBVar_640_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
    mut v_infos_641_: *mut crate::leanh::LeanObject,
    mut v_i_642_: *mut crate::leanh::LeanObject,
    mut v_e_643_: *mut crate::leanh::LeanObject,
    mut v_todo_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummyBVar_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_643_) == 5 {
                    v_fn_645_ = crate::leanh::lean_ctor_get(v_e_643_, 0);
                    crate::leanh::lean_inc_ref(v_fn_645_);
                    v_arg_646_ = crate::leanh::lean_ctor_get(v_e_643_, 1);
                    crate::leanh::lean_inc_ref(v_arg_646_);
                    crate::leanh::lean_dec_ref_known(v_e_643_, 2);
                    v___x_647_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(
                            v_infos_641_,
                            v_i_642_,
                        );
                    if v___x_647_ == 0 {
                        v___x_648_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_649_ = lean_nat_sub(v_i_642_, v___x_648_);
                        crate::leanh::lean_dec(v_i_642_);
                        v___x_650_ = lean_array_push(v_todo_644_, v_arg_646_);
                        v_i_642_ = v___x_649_;
                        v_e_643_ = v_fn_645_;
                        v_todo_644_ = v___x_650_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_646_);
                        v_dummyBVar_652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0);
                        v___x_653_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_654_ = lean_nat_sub(v_i_642_, v___x_653_);
                        crate::leanh::lean_dec(v_i_642_);
                        v___x_655_ = lean_array_push(v_todo_644_, v_dummyBVar_652_);
                        v_i_642_ = v___x_654_;
                        v_e_643_ = v_fn_645_;
                        v_todo_644_ = v___x_655_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_643_);
                    crate::leanh::lean_dec(v_i_642_);
                    return v_todo_644_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___boxed(
    mut v_infos_657_: *mut crate::leanh::LeanObject,
    mut v_i_658_: *mut crate::leanh::LeanObject,
    mut v_e_659_: *mut crate::leanh::LeanObject,
    mut v_todo_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_661_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
        v_infos_657_,
        v_i_658_,
        v_e_659_,
        v_todo_660_,
    );
    crate::leanh::lean_dec_ref(v_infos_657_);
    return v_res_661_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(
    mut v_a_662_: *mut crate::leanh::LeanObject,
    mut v_x_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_663_) == 0 {
                    v___x_664_ = crate::leanh::lean_box(0);
                    return v___x_664_;
                } else {
                    v_key_665_ = crate::leanh::lean_ctor_get(v_x_663_, 0);
                    v_value_666_ = crate::leanh::lean_ctor_get(v_x_663_, 1);
                    v_tail_667_ = crate::leanh::lean_ctor_get(v_x_663_, 2);
                    v___x_668_ = lean_name_eq(v_key_665_, v_a_662_);
                    if v___x_668_ == 0 {
                        v_x_663_ = v_tail_667_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_666_);
                        v___x_670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_670_, 0, v_value_666_);
                        return v___x_670_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg___boxed(
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_x_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_671_, v_x_672_);
    crate::leanh::lean_dec(v_x_672_);
    crate::leanh::lean_dec(v_a_671_);
    return v_res_673_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
    mut v_root_674_: u8,
    mut v_fnInfos_675_: *mut crate::leanh::LeanObject,
    mut v_todo_676_: *mut crate::leanh::LeanObject,
    mut v_e_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: u8 = 0;
    let mut v_fn_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_678_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_677_);
                if v___x_678_ == 0 {
                    v_fn_679_ = l_Lean_Expr_getAppFn(v_e_677_);
                    match crate::leanh::lean_obj_tag(v_fn_679_) {
                        9 => {
                            crate::leanh::lean_dec_ref(v_e_677_);
                            v_a_680_ = crate::leanh::lean_ctor_get(v_fn_679_, 0);
                            crate::leanh::lean_inc_ref(v_a_680_);
                            crate::leanh::lean_dec_ref_known(v_fn_679_, 1);
                            v___x_681_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_681_, 0, v_a_680_);
                            v___x_682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_682_, 0, v___x_681_);
                            crate::leanh::lean_ctor_set(v___x_682_, 1, v_todo_676_);
                            return v___x_682_;
                        }
                        0 => {
                            crate::leanh::lean_dec_ref_known(v_fn_679_, 1);
                            crate::leanh::lean_dec_ref(v_e_677_);
                            v___x_683_ = crate::leanh::lean_box(0);
                            v___x_684_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_683_);
                            crate::leanh::lean_ctor_set(v___x_684_, 1, v_todo_676_);
                            return v___x_684_;
                        }
                        7 => {
                            crate::leanh::lean_dec_ref(v_e_677_);
                            v_binderType_685_ = crate::leanh::lean_ctor_get(v_fn_679_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_685_);
                            v_body_686_ = crate::leanh::lean_ctor_get(v_fn_679_, 2);
                            crate::leanh::lean_inc_ref(v_body_686_);
                            crate::leanh::lean_dec_ref_known(v_fn_679_, 3);
                            v___x_687_ = crate::leanh::lean_box(5);
                            v___x_688_ = lean_array_push(v_todo_676_, v_body_686_);
                            v___x_689_ = lean_array_push(v___x_688_, v_binderType_685_);
                            v___x_690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_687_);
                            crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                            return v___x_690_;
                        }
                        4 => {
                            v_declName_691_ = crate::leanh::lean_ctor_get(v_fn_679_, 0);
                            crate::leanh::lean_inc(v_declName_691_);
                            crate::leanh::lean_dec_ref_known(v_fn_679_, 2);
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
                            v_fvarId_709_ = crate::leanh::lean_ctor_get(v_fn_679_, 0);
                            crate::leanh::lean_inc(v_fvarId_709_);
                            crate::leanh::lean_dec_ref_known(v_fn_679_, 1);
                            v_numArgs_710_ = l_Lean_Expr_getAppNumArgs(v_e_677_);
                            v_todo_711_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_677_, v_todo_676_);
                            v___x_712_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_712_, 0, v_fvarId_709_);
                            crate::leanh::lean_ctor_set(v___x_712_, 1, v_numArgs_710_);
                            v___x_713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_712_);
                            crate::leanh::lean_ctor_set(v___x_713_, 1, v_todo_711_);
                            return v___x_713_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_fn_679_);
                            crate::leanh::lean_dec_ref(v_e_677_);
                            v___x_714_ = crate::leanh::lean_box(1);
                            v___x_715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_714_);
                            crate::leanh::lean_ctor_set(v___x_715_, 1, v_todo_676_);
                            return v___x_715_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_677_);
                    v___x_716_ = crate::leanh::lean_box(0);
                    v___x_717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_717_, 0, v___x_716_);
                    crate::leanh::lean_ctor_set(v___x_717_, 1, v_todo_676_);
                    return v___x_717_;
                }
            }
            1 => {
                v___x_695_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_695_, 0, v_declName_691_);
                crate::leanh::lean_ctor_set(v___x_695_, 1, v___y_693_);
                v___x_696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_696_, 0, v___x_695_);
                crate::leanh::lean_ctor_set(v___x_696_, 1, v___y_694_);
                return v___x_696_;
            }
            2 => {
                v_numArgs_698_ = l_Lean_Expr_getAppNumArgs(v_e_677_);
                v___x_699_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_691_, v_fnInfos_675_);
                if crate::leanh::lean_obj_tag(v___x_699_) == 1 {
                    v_val_700_ = crate::leanh::lean_ctor_get(v___x_699_, 0);
                    crate::leanh::lean_inc(v_val_700_);
                    crate::leanh::lean_dec_ref_known(v___x_699_, 1);
                    v___x_701_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_702_ = lean_nat_sub(v_numArgs_698_, v___x_701_);
                    v___x_703_ =
                        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(
                            v_val_700_,
                            v___x_702_,
                            v_e_677_,
                            v_todo_676_,
                        );
                    crate::leanh::lean_dec(v_val_700_);
                    v___y_693_ = v_numArgs_698_;
                    v___y_694_ = v___x_703_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_699_);
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
                crate::leanh::lean_inc_ref(v_e_677_);
                v___x_706_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_691_, v_e_677_);
                if v___x_706_ == 0 {
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_691_);
                    crate::leanh::lean_dec_ref(v_e_677_);
                    v___x_707_ = crate::leanh::lean_box(0);
                    v___x_708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_708_, 0, v___x_707_);
                    crate::leanh::lean_ctor_set(v___x_708_, 1, v_todo_676_);
                    return v___x_708_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(
    mut v_root_718_: *mut crate::leanh::LeanObject,
    mut v_fnInfos_719_: *mut crate::leanh::LeanObject,
    mut v_todo_720_: *mut crate::leanh::LeanObject,
    mut v_e_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_boxed_722_: u8 = 0;
    let mut v_res_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_722_ = (crate::leanh::lean_unbox(v_root_718_) as u8);
    v_res_723_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
        v_root_boxed_722_,
        v_fnInfos_719_,
        v_todo_720_,
        v_e_721_,
    );
    crate::leanh::lean_dec(v_fnInfos_719_);
    return v_res_723_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(
    mut v_00_u03b2_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
    mut v_x_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_725_, v_x_726_);
    return v___x_727_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(
    mut v_00_u03b2_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
    mut v_x_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_728_, v_a_729_, v_x_730_);
    crate::leanh::lean_dec(v_x_730_);
    crate::leanh::lean_dec(v_a_729_);
    return v_res_731_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
    mut v_root_732_: u8,
    mut v_fnInfos_733_: *mut crate::leanh::LeanObject,
    mut v_todo_734_: *mut crate::leanh::LeanObject,
    mut v_keys_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_736_ = lean_array_get_size(v_todo_734_);
                v___x_737_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_738_ = lean_nat_dec_eq(v___x_736_, v___x_737_);
                if v___x_738_ == 0 {
                    v___x_739_ = l_Lean_instInhabitedExpr;
                    v___x_740_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_741_ = lean_nat_sub(v___x_736_, v___x_740_);
                    v_e_742_ = lean_array_get(v___x_739_, v_todo_734_, v___x_741_);
                    crate::leanh::lean_dec(v___x_741_);
                    v_todo_743_ = lean_array_pop(v_todo_734_);
                    v___x_744_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(
                        v_root_732_,
                        v_fnInfos_733_,
                        v_todo_743_,
                        v_e_742_,
                    );
                    v_fst_745_ = crate::leanh::lean_ctor_get(v___x_744_, 0);
                    crate::leanh::lean_inc(v_fst_745_);
                    v_snd_746_ = crate::leanh::lean_ctor_get(v___x_744_, 1);
                    crate::leanh::lean_inc(v_snd_746_);
                    crate::leanh::lean_dec_ref(v___x_744_);
                    v___x_747_ = lean_array_push(v_keys_735_, v_fst_745_);
                    v_root_732_ = v___x_738_;
                    v_todo_734_ = v_snd_746_;
                    v_keys_735_ = v___x_747_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_todo_734_);
                    return v_keys_735_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(
    mut v_root_749_: *mut crate::leanh::LeanObject,
    mut v_fnInfos_750_: *mut crate::leanh::LeanObject,
    mut v_todo_751_: *mut crate::leanh::LeanObject,
    mut v_keys_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_boxed_753_: u8 = 0;
    let mut v_res_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_753_ = (crate::leanh::lean_unbox(v_root_749_) as u8);
    v_res_754_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
        v_root_boxed_753_,
        v_fnInfos_750_,
        v_todo_751_,
        v_keys_752_,
    );
    crate::leanh::lean_dec(v_fnInfos_750_);
    return v_res_754_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity()
-> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = crate::leanh::lean_unsigned_to_nat(8);
    return v___x_755_;
}
pub unsafe fn l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(
    mut v_p_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pattern_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnInfos_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pattern_757_ = crate::leanh::lean_ctor_get(v_p_756_, 3);
    crate::leanh::lean_inc_ref(v_pattern_757_);
    v_fnInfos_758_ = crate::leanh::lean_ctor_get(v_p_756_, 4);
    crate::leanh::lean_inc(v_fnInfos_758_);
    crate::leanh::lean_dec_ref(v_p_756_);
    v___x_759_ = crate::leanh::lean_unsigned_to_nat(8);
    v_todo_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
    v___x_761_ = 1;
    crate::leanh::lean_inc_ref(v_todo_760_);
    v___x_762_ = lean_array_push(v_todo_760_, v_pattern_757_);
    v___x_763_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(
        v___x_761_,
        v_fnInfos_758_,
        v___x_762_,
        v_todo_760_,
    );
    crate::leanh::lean_dec(v_fnInfos_758_);
    return v___x_763_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___redArg(
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_d_765_: *mut crate::leanh::LeanObject,
    mut v_p_766_: *mut crate::leanh::LeanObject,
    mut v_v_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keys_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keys_768_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_766_);
    v___x_769_ =
        l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_764_, v_d_765_, v_keys_768_, v_v_767_);
    return v___x_769_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern(
    mut v_00_u03b1_770_: *mut crate::leanh::LeanObject,
    mut v_inst_771_: *mut crate::leanh::LeanObject,
    mut v_d_772_: *mut crate::leanh::LeanObject,
    mut v_p_773_: *mut crate::leanh::LeanObject,
    mut v_v_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_771_, v_d_772_, v_p_773_, v_v_774_);
    return v___x_775_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(
    mut v_a_776_: *mut crate::leanh::LeanObject,
    mut v_b_777_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    v_fst_778_ = crate::leanh::lean_ctor_get(v_a_776_, 0);
    v_fst_779_ = crate::leanh::lean_ctor_get(v_b_777_, 0);
    v___x_780_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_778_, v_fst_779_);
    return v___x_780_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(
    mut v_a_781_: *mut crate::leanh::LeanObject,
    mut v_b_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_783_: u8 = 0;
    let mut v_r_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(
            v_a_781_, v_b_782_,
        );
    crate::leanh::lean_dec_ref(v_b_782_);
    crate::leanh::lean_dec_ref(v_a_781_);
    v_r_784_ = crate::leanh::lean_box((v_res_783_) as usize);
    return v_r_784_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(
    mut v_cs_791_: *mut crate::leanh::LeanObject,
    mut v_k_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    v___x_793_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_794_ = lean_array_get_size(v_cs_791_);
    v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
    if v___x_795_ == 0 {
        let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_792_);
        v___x_796_ = crate::leanh::lean_box(0);
        return v___x_796_;
    } else {
        let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: u8 = 0;
        v___x_797_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_798_ = lean_nat_sub(v___x_794_, v___x_797_);
        v___x_799_ = lean_nat_dec_le(v___x_793_, v___x_798_);
        if v___x_799_ == 0 {
            let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_798_);
            crate::leanh::lean_dec(v_k_792_);
            v___x_800_ = crate::leanh::lean_box(0);
            return v___x_800_;
        } else {
            let mut v___f_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_801_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0;
            v___x_802_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
            v___x_803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_803_, 0, v_k_792_);
            crate::leanh::lean_ctor_set(v___x_803_, 1, v___x_802_);
            v___x_804_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3;
            v___x_805_ = l_Array_binSearchAux___redArg(
                v___f_801_, v___x_804_, v_cs_791_, v___x_803_, v___x_793_, v___x_798_,
            );
            return v___x_805_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(
    mut v_cs_806_: *mut crate::leanh::LeanObject,
    mut v_k_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(
        v_cs_806_, v_k_807_,
    );
    crate::leanh::lean_dec_ref(v_cs_806_);
    return v_res_808_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(
    mut v_00_u03b1_809_: *mut crate::leanh::LeanObject,
    mut v_cs_810_: *mut crate::leanh::LeanObject,
    mut v_k_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    v___x_812_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_813_ = lean_array_get_size(v_cs_810_);
    v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
    if v___x_814_ == 0 {
        let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_811_);
        v___x_815_ = crate::leanh::lean_box(0);
        return v___x_815_;
    } else {
        let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_818_: u8 = 0;
        v___x_816_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_817_ = lean_nat_sub(v___x_813_, v___x_816_);
        v___x_818_ = lean_nat_dec_le(v___x_812_, v___x_817_);
        if v___x_818_ == 0 {
            let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_817_);
            crate::leanh::lean_dec(v_k_811_);
            v___x_819_ = crate::leanh::lean_box(0);
            return v___x_819_;
        } else {
            let mut v___f_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_820_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0;
            v___x_821_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
            v___x_822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_822_, 0, v_k_811_);
            crate::leanh::lean_ctor_set(v___x_822_, 1, v___x_821_);
            v___x_823_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3;
            v___x_824_ = l_Array_binSearchAux___redArg(
                v___f_820_, v___x_823_, v_cs_810_, v___x_822_, v___x_812_, v___x_817_,
            );
            return v___x_824_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(
    mut v_00_u03b1_825_: *mut crate::leanh::LeanObject,
    mut v_cs_826_: *mut crate::leanh::LeanObject,
    mut v_k_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(
        v_00_u03b1_825_,
        v_cs_826_,
        v_k_827_,
    );
    crate::leanh::lean_dec_ref(v_cs_826_);
    return v_res_828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(
    mut v_e_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Lean_Expr_getAppFn(v_e_829_);
    match crate::leanh::lean_obj_tag(v___x_830_) {
        9 => {
            let mut v_a_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_831_ = crate::leanh::lean_ctor_get(v___x_830_, 0);
            crate::leanh::lean_inc_ref(v_a_831_);
            crate::leanh::lean_dec_ref_known(v___x_830_, 1);
            v___x_832_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_832_, 0, v_a_831_);
            return v___x_832_;
        }
        4 => {
            let mut v_declName_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_declName_833_ = crate::leanh::lean_ctor_get(v___x_830_, 0);
            crate::leanh::lean_inc(v_declName_833_);
            crate::leanh::lean_dec_ref_known(v___x_830_, 2);
            v___x_834_ = l_Lean_Expr_getAppNumArgs(v_e_829_);
            v___x_835_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_835_, 0, v_declName_833_);
            crate::leanh::lean_ctor_set(v___x_835_, 1, v___x_834_);
            return v___x_835_;
        }
        1 => {
            let mut v_fvarId_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_836_ = crate::leanh::lean_ctor_get(v___x_830_, 0);
            crate::leanh::lean_inc(v_fvarId_836_);
            crate::leanh::lean_dec_ref_known(v___x_830_, 1);
            v___x_837_ = l_Lean_Expr_getAppNumArgs(v_e_829_);
            v___x_838_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_838_, 0, v_fvarId_836_);
            crate::leanh::lean_ctor_set(v___x_838_, 1, v___x_837_);
            return v___x_838_;
        }
        7 => {
            let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_830_, 3);
            v___x_839_ = crate::leanh::lean_box(5);
            return v___x_839_;
        }
        _ => {
            let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_830_);
            v___x_840_ = crate::leanh::lean_box(1);
            return v___x_840_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(
    mut v_e_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_841_);
    crate::leanh::lean_dec_ref(v_e_841_);
    return v_res_842_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(
    mut v_todo_843_: *mut crate::leanh::LeanObject,
    mut v_e_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_844_) {
                5 => {
                    v_fn_845_ = crate::leanh::lean_ctor_get(v_e_844_, 0);
                    crate::leanh::lean_inc_ref(v_fn_845_);
                    v_arg_846_ = crate::leanh::lean_ctor_get(v_e_844_, 1);
                    crate::leanh::lean_inc_ref(v_arg_846_);
                    crate::leanh::lean_dec_ref_known(v_e_844_, 2);
                    v___x_847_ = lean_array_push(v_todo_843_, v_arg_846_);
                    v_todo_843_ = v___x_847_;
                    v_e_844_ = v_fn_845_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_binderType_849_ = crate::leanh::lean_ctor_get(v_e_844_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_849_);
                    v_body_850_ = crate::leanh::lean_ctor_get(v_e_844_, 2);
                    crate::leanh::lean_inc_ref(v_body_850_);
                    crate::leanh::lean_dec_ref_known(v_e_844_, 3);
                    v___x_851_ = lean_array_push(v_todo_843_, v_body_850_);
                    v___x_852_ = lean_array_push(v___x_851_, v_binderType_849_);
                    return v___x_852_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_844_);
                    return v_todo_843_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(
    mut v_as_853_: *mut crate::leanh::LeanObject,
    mut v_k_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_857_ = lean_nat_add(v_x_855_, v_x_856_);
                v___x_858_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_859_ = lean_nat_shiftr(v___x_857_, v___x_858_);
                crate::leanh::lean_dec(v___x_857_);
                v_a_860_ = lean_array_fget_borrowed(v_as_853_, v_m_859_);
                v___x_861_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_860_, v_k_854_);
                if v___x_861_ == 0 {
                    crate::leanh::lean_dec(v_x_856_);
                    v___x_862_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_854_, v_a_860_);
                    if v___x_862_ == 0 {
                        crate::leanh::lean_dec(v_m_859_);
                        crate::leanh::lean_dec(v_x_855_);
                        crate::leanh::lean_inc(v_a_860_);
                        v___x_863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_863_, 0, v_a_860_);
                        return v___x_863_;
                    } else {
                        v___x_864_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_865_ = lean_nat_dec_eq(v_m_859_, v___x_864_);
                        if v___x_865_ == 0 {
                            v___x_866_ = lean_nat_sub(v_m_859_, v___x_858_);
                            crate::leanh::lean_dec(v_m_859_);
                            v___x_867_ = lean_nat_dec_lt(v___x_866_, v_x_855_);
                            if v___x_867_ == 0 {
                                v_x_856_ = v___x_866_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_866_);
                                crate::leanh::lean_dec(v_x_855_);
                                v___x_869_ = crate::leanh::lean_box(0);
                                return v___x_869_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_859_);
                            crate::leanh::lean_dec(v_x_855_);
                            v___x_870_ = crate::leanh::lean_box(0);
                            return v___x_870_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_855_);
                    v___x_871_ = lean_nat_add(v_m_859_, v___x_858_);
                    crate::leanh::lean_dec(v_m_859_);
                    v___x_872_ = lean_nat_dec_le(v___x_871_, v_x_856_);
                    if v___x_872_ == 0 {
                        crate::leanh::lean_dec(v___x_871_);
                        crate::leanh::lean_dec(v_x_856_);
                        v___x_873_ = crate::leanh::lean_box(0);
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
    mut v_as_875_: *mut crate::leanh::LeanObject,
    mut v_k_876_: *mut crate::leanh::LeanObject,
    mut v_x_877_: *mut crate::leanh::LeanObject,
    mut v_x_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_875_, v_k_876_, v_x_877_, v_x_878_);
    crate::leanh::lean_dec_ref(v_k_876_);
    crate::leanh::lean_dec_ref(v_as_875_);
    return v_res_879_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(
    mut v_todo_880_: *mut crate::leanh::LeanObject,
    mut v_c_881_: *mut crate::leanh::LeanObject,
    mut v_result_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vs_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v_csize_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_first_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v_fst_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: u8 = 0;
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_883_ = crate::leanh::lean_ctor_get(v_c_881_, 0);
                v_children_884_ = crate::leanh::lean_ctor_get(v_c_881_, 1);
                v_isSharedCheck_931_ = (!crate::leanh::lean_is_exclusive(v_c_881_)) as u8;
                if v_isSharedCheck_931_ == 0 {
                    v___x_886_ = v_c_881_;
                    v_isShared_887_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_884_);
                    crate::leanh::lean_inc(v_vs_883_);
                    crate::leanh::lean_dec(v_c_881_);
                    v___x_886_ = crate::leanh::lean_box(0);
                    v_isShared_887_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_888_ = lean_array_get_size(v_todo_880_);
                v___x_889_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
                if v___x_890_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_883_);
                    v_csize_891_ = lean_array_get_size(v_children_884_);
                    v___x_892_ = lean_nat_dec_eq(v_csize_891_, v___x_889_);
                    if v___x_892_ == 0 {
                        v___x_893_ = l_Lean_instInhabitedExpr;
                        v___x_894_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_895_ = lean_nat_sub(v___x_888_, v___x_894_);
                        v___x_896_ = lean_array_get_borrowed(v___x_893_, v_todo_880_, v___x_895_);
                        crate::leanh::lean_dec(v___x_895_);
                        v_e_897_ = l_Lean_Meta_Sym_etaReduce(v___x_896_);
                        v_todo_898_ = lean_array_pop(v_todo_880_);
                        v_first_914_ = lean_array_fget_borrowed(v_children_884_, v___x_889_);
                        v___x_915_ = lean_nat_dec_eq(v_csize_891_, v___x_894_);
                        if v___x_915_ == 0 {
                            v_fst_916_ = crate::leanh::lean_ctor_get(v_first_914_, 0);
                            v_snd_917_ = crate::leanh::lean_ctor_get(v_first_914_, 1);
                            v___x_918_ = crate::leanh::lean_box(0);
                            v___x_919_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_916_, v___x_918_);
                            if v___x_919_ == 0 {
                                v___y_900_ = v_result_882_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_917_);
                                crate::leanh::lean_inc_ref(v_todo_898_);
                                v___x_920_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_898_, v_snd_917_, v_result_882_);
                                v___y_900_ = v___x_920_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_first_914_);
                            crate::leanh::lean_del_object(v___x_886_);
                            crate::leanh::lean_dec_ref(v_children_884_);
                            v_fst_921_ = crate::leanh::lean_ctor_get(v_first_914_, 0);
                            crate::leanh::lean_inc(v_fst_921_);
                            v_snd_922_ = crate::leanh::lean_ctor_get(v_first_914_, 1);
                            crate::leanh::lean_inc(v_snd_922_);
                            crate::leanh::lean_dec(v_first_914_);
                            v___x_923_ = crate::leanh::lean_box(0);
                            v___x_924_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_921_, v___x_923_);
                            if v___x_924_ == 0 {
                                v___x_925_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_897_);
                                v___x_926_ =
                                    l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_921_, v___x_925_);
                                crate::leanh::lean_dec(v___x_925_);
                                crate::leanh::lean_dec(v_fst_921_);
                                if v___x_926_ == 0 {
                                    crate::leanh::lean_dec(v_snd_922_);
                                    crate::leanh::lean_dec_ref(v_todo_898_);
                                    crate::leanh::lean_dec_ref(v_e_897_);
                                    return v_result_882_;
                                } else {
                                    v___x_927_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_898_, v_e_897_);
                                    v_todo_880_ = v___x_927_;
                                    v_c_881_ = v_snd_922_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_921_);
                                crate::leanh::lean_dec_ref(v_e_897_);
                                v_todo_880_ = v_todo_898_;
                                v_c_881_ = v_snd_922_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_886_);
                        crate::leanh::lean_dec_ref(v_children_884_);
                        crate::leanh::lean_dec_ref(v_todo_880_);
                        return v_result_882_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_886_);
                    crate::leanh::lean_dec_ref(v_children_884_);
                    crate::leanh::lean_dec_ref(v_todo_880_);
                    v___x_930_ = l_Array_append___redArg(v_result_882_, v_vs_883_);
                    crate::leanh::lean_dec_ref(v_vs_883_);
                    return v___x_930_;
                }
            }
            2 => {
                v___x_901_ = lean_nat_dec_lt(v___x_889_, v_csize_891_);
                if v___x_901_ == 0 {
                    crate::leanh::lean_dec_ref(v_todo_898_);
                    crate::leanh::lean_dec_ref(v_e_897_);
                    crate::leanh::lean_del_object(v___x_886_);
                    crate::leanh::lean_dec_ref(v_children_884_);
                    return v___y_900_;
                } else {
                    v___x_902_ = lean_nat_sub(v_csize_891_, v___x_894_);
                    v___x_903_ = lean_nat_dec_le(v___x_889_, v___x_902_);
                    if v___x_903_ == 0 {
                        crate::leanh::lean_dec(v___x_902_);
                        crate::leanh::lean_dec_ref(v_todo_898_);
                        crate::leanh::lean_dec_ref(v_e_897_);
                        crate::leanh::lean_del_object(v___x_886_);
                        crate::leanh::lean_dec_ref(v_children_884_);
                        return v___y_900_;
                    } else {
                        v___x_904_ =
                            l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(
                                v_e_897_,
                            );
                        v___x_905_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
                        if v_isShared_887_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_886_, 1, v___x_905_);
                            crate::leanh::lean_ctor_set(v___x_886_, 0, v___x_904_);
                            v___x_907_ = v___x_886_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_904_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_905_);
                            v___x_907_ = v_reuseFailAlloc_913_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_908_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_884_, v___x_907_, v___x_889_, v___x_902_);
                crate::leanh::lean_dec_ref(v___x_907_);
                crate::leanh::lean_dec_ref(v_children_884_);
                if crate::leanh::lean_obj_tag(v___x_908_) == 0 {
                    crate::leanh::lean_dec_ref(v_todo_898_);
                    crate::leanh::lean_dec_ref(v_e_897_);
                    return v___y_900_;
                } else {
                    v_val_909_ = crate::leanh::lean_ctor_get(v___x_908_, 0);
                    crate::leanh::lean_inc(v_val_909_);
                    crate::leanh::lean_dec_ref_known(v___x_908_, 1);
                    v_snd_910_ = crate::leanh::lean_ctor_get(v_val_909_, 1);
                    crate::leanh::lean_inc(v_snd_910_);
                    crate::leanh::lean_dec(v_val_909_);
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
    mut v_00_u03b1_932_: *mut crate::leanh::LeanObject,
    mut v_todo_933_: *mut crate::leanh::LeanObject,
    mut v_c_934_: *mut crate::leanh::LeanObject,
    mut v_result_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(
        v_todo_933_,
        v_c_934_,
        v_result_935_,
    );
    return v___x_936_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(
    mut v_00_u03b1_937_: *mut crate::leanh::LeanObject,
    mut v_as_938_: *mut crate::leanh::LeanObject,
    mut v_k_939_: *mut crate::leanh::LeanObject,
    mut v_x_940_: *mut crate::leanh::LeanObject,
    mut v_x_941_: *mut crate::leanh::LeanObject,
    mut v_x_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_938_, v_k_939_, v_x_940_, v_x_941_);
    return v___x_943_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(
    mut v_00_u03b1_944_: *mut crate::leanh::LeanObject,
    mut v_as_945_: *mut crate::leanh::LeanObject,
    mut v_k_946_: *mut crate::leanh::LeanObject,
    mut v_x_947_: *mut crate::leanh::LeanObject,
    mut v_x_948_: *mut crate::leanh::LeanObject,
    mut v_x_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_944_, v_as_945_, v_k_946_, v_x_947_, v_x_948_, v_x_949_);
    crate::leanh::lean_dec_ref(v_k_946_);
    crate::leanh::lean_dec_ref(v_as_945_);
    return v_res_950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(
    mut v_keys_951_: *mut crate::leanh::LeanObject,
    mut v_vals_952_: *mut crate::leanh::LeanObject,
    mut v_i_953_: *mut crate::leanh::LeanObject,
    mut v_k_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_955_ = lean_array_get_size(v_keys_951_);
                v___x_956_ = lean_nat_dec_lt(v_i_953_, v___x_955_);
                if v___x_956_ == 0 {
                    crate::leanh::lean_dec(v_i_953_);
                    v___x_957_ = crate::leanh::lean_box(0);
                    return v___x_957_;
                } else {
                    v_k_x27_958_ = lean_array_fget_borrowed(v_keys_951_, v_i_953_);
                    v___x_959_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_954_, v_k_x27_958_);
                    if v___x_959_ == 0 {
                        v___x_960_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_961_ = lean_nat_add(v_i_953_, v___x_960_);
                        crate::leanh::lean_dec(v_i_953_);
                        v_i_953_ = v___x_961_;
                        state = 0;
                        continue;
                    } else {
                        v___x_963_ = lean_array_fget_borrowed(v_vals_952_, v_i_953_);
                        crate::leanh::lean_dec(v_i_953_);
                        crate::leanh::lean_inc(v___x_963_);
                        v___x_964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
                        return v___x_964_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_965_: *mut crate::leanh::LeanObject,
    mut v_vals_966_: *mut crate::leanh::LeanObject,
    mut v_i_967_: *mut crate::leanh::LeanObject,
    mut v_k_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_965_, v_vals_966_, v_i_967_, v_k_968_);
    crate::leanh::lean_dec(v_k_968_);
    crate::leanh::lean_dec_ref(v_vals_966_);
    crate::leanh::lean_dec_ref(v_keys_965_);
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
    v___x_974_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0);
    v___x_975_ = lean_usize_sub(v___x_974_, v___x_973_);
    return v___x_975_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(
    mut v_x_976_: *mut crate::leanh::LeanObject,
    mut v_x_977_: usize,
    mut v_x_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: usize = 0;
    let mut v___x_982_: usize = 0;
    let mut v___x_983_: usize = 0;
    let mut v_j_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: usize = 0;
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_976_) == 0 {
                    v_es_979_ = crate::leanh::lean_ctor_get(v_x_976_, 0);
                    v___x_980_ = crate::leanh::lean_box(2);
                    v___x_981_ = 5usize;
                    v___x_982_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1);
                    v___x_983_ = lean_usize_land(v_x_977_, v___x_982_);
                    v_j_984_ = lean_usize_to_nat(v___x_983_);
                    v___x_985_ = lean_array_get_borrowed(v___x_980_, v_es_979_, v_j_984_);
                    crate::leanh::lean_dec(v_j_984_);
                    match crate::leanh::lean_obj_tag(v___x_985_) {
                        0 => {
                            v_key_986_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
                            v_val_987_ = crate::leanh::lean_ctor_get(v___x_985_, 1);
                            v___x_988_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_978_, v_key_986_);
                            if v___x_988_ == 0 {
                                v___x_989_ = crate::leanh::lean_box(0);
                                return v___x_989_;
                            } else {
                                crate::leanh::lean_inc(v_val_987_);
                                v___x_990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_990_, 0, v_val_987_);
                                return v___x_990_;
                            }
                        }
                        1 => {
                            v_node_991_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
                            v___x_992_ = lean_usize_shift_right(v_x_977_, v___x_981_);
                            v_x_976_ = v_node_991_;
                            v_x_977_ = v___x_992_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_994_ = crate::leanh::lean_box(0);
                            return v___x_994_;
                        }
                    }
                } else {
                    v_ks_995_ = crate::leanh::lean_ctor_get(v_x_976_, 0);
                    v_vs_996_ = crate::leanh::lean_ctor_get(v_x_976_, 1);
                    v___x_997_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_998_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_995_, v_vs_996_, v___x_997_, v_x_978_);
                    return v___x_998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(
    mut v_x_999_: *mut crate::leanh::LeanObject,
    mut v_x_1000_: *mut crate::leanh::LeanObject,
    mut v_x_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_205__boxed_1002_: usize = 0;
    let mut v_res_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_205__boxed_1002_ = crate::leanh::lean_unbox_usize(v_x_1000_);
    crate::leanh::lean_dec(v_x_1000_);
    v_res_1003_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_999_, v_x_205__boxed_1002_, v_x_1001_);
    crate::leanh::lean_dec(v_x_1001_);
    crate::leanh::lean_dec_ref(v_x_999_);
    return v_res_1003_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
    mut v_x_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1006_: u64 = 0;
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1005_);
    v___x_1007_ = lean_uint64_to_usize(v___x_1006_);
    v___x_1008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_1004_, v___x_1007_, v_x_1005_);
    return v___x_1008_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_x_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
            v_x_1009_, v_x_1010_,
        );
    crate::leanh::lean_dec(v_x_1010_);
    crate::leanh::lean_dec_ref(v_x_1009_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch___redArg(
    mut v_d_1014_: *mut crate::leanh::LeanObject,
    mut v_e_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1025_ = crate::leanh::lean_box(0);
                v___x_1026_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_1014_, v___x_1025_);
                if crate::leanh::lean_obj_tag(v___x_1026_) == 0 {
                    v___x_1027_ = crate::leanh::lean_unsigned_to_nat(8);
                    v___x_1028_ = lean_mk_empty_array_with_capacity(v___x_1027_);
                    v___y_1017_ = v___x_1028_;
                    state = 1;
                    continue;
                } else {
                    v_val_1029_ = crate::leanh::lean_ctor_get(v___x_1026_, 0);
                    crate::leanh::lean_inc(v_val_1029_);
                    crate::leanh::lean_dec_ref_known(v___x_1026_, 1);
                    v_vs_1030_ = crate::leanh::lean_ctor_get(v_val_1029_, 0);
                    crate::leanh::lean_inc_ref(v_vs_1030_);
                    crate::leanh::lean_dec(v_val_1029_);
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
                crate::leanh::lean_dec(v___x_1019_);
                if crate::leanh::lean_obj_tag(v___x_1020_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_1018_);
                    return v___y_1017_;
                } else {
                    v_val_1021_ = crate::leanh::lean_ctor_get(v___x_1020_, 0);
                    crate::leanh::lean_inc(v_val_1021_);
                    crate::leanh::lean_dec_ref_known(v___x_1020_, 1);
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
    mut v_d_1031_: *mut crate::leanh::LeanObject,
    mut v_e_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1031_, v_e_1032_);
    crate::leanh::lean_dec_ref(v_e_1032_);
    crate::leanh::lean_dec_ref(v_d_1031_);
    return v_res_1033_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch(
    mut v_00_u03b1_1034_: *mut crate::leanh::LeanObject,
    mut v_d_1035_: *mut crate::leanh::LeanObject,
    mut v_e_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1035_, v_e_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatch___boxed(
    mut v_00_u03b1_1038_: *mut crate::leanh::LeanObject,
    mut v_d_1039_: *mut crate::leanh::LeanObject,
    mut v_e_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_1038_, v_d_1039_, v_e_1040_);
    crate::leanh::lean_dec_ref(v_e_1040_);
    crate::leanh::lean_dec_ref(v_d_1039_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(
    mut v_00_u03b2_1042_: *mut crate::leanh::LeanObject,
    mut v_x_1043_: *mut crate::leanh::LeanObject,
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(
            v_x_1043_, v_x_1044_,
        );
    return v___x_1045_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(
    mut v_00_u03b2_1046_: *mut crate::leanh::LeanObject,
    mut v_x_1047_: *mut crate::leanh::LeanObject,
    mut v_x_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(
        v_00_u03b2_1046_,
        v_x_1047_,
        v_x_1048_,
    );
    crate::leanh::lean_dec(v_x_1048_);
    crate::leanh::lean_dec_ref(v_x_1047_);
    return v_res_1049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(
    mut v_00_u03b2_1050_: *mut crate::leanh::LeanObject,
    mut v_x_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: usize,
    mut v_x_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(
    mut v_00_u03b2_1055_: *mut crate::leanh::LeanObject,
    mut v_x_1056_: *mut crate::leanh::LeanObject,
    mut v_x_1057_: *mut crate::leanh::LeanObject,
    mut v_x_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_315__boxed_1059_: usize = 0;
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_315__boxed_1059_ = crate::leanh::lean_unbox_usize(v_x_1057_);
    crate::leanh::lean_dec(v_x_1057_);
    v_res_1060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_1055_, v_x_1056_, v_x_315__boxed_1059_, v_x_1058_);
    crate::leanh::lean_dec(v_x_1058_);
    crate::leanh::lean_dec_ref(v_x_1056_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1061_: *mut crate::leanh::LeanObject,
    mut v_keys_1062_: *mut crate::leanh::LeanObject,
    mut v_vals_1063_: *mut crate::leanh::LeanObject,
    mut v_heq_1064_: *mut crate::leanh::LeanObject,
    mut v_i_1065_: *mut crate::leanh::LeanObject,
    mut v_k_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1065_, v_k_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1068_: *mut crate::leanh::LeanObject,
    mut v_keys_1069_: *mut crate::leanh::LeanObject,
    mut v_vals_1070_: *mut crate::leanh::LeanObject,
    mut v_heq_1071_: *mut crate::leanh::LeanObject,
    mut v_i_1072_: *mut crate::leanh::LeanObject,
    mut v_k_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_1068_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_k_1073_);
    crate::leanh::lean_dec(v_k_1073_);
    crate::leanh::lean_dec_ref(v_vals_1070_);
    crate::leanh::lean_dec_ref(v_keys_1069_);
    return v_res_1074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(
    mut v_d_1075_: *mut crate::leanh::LeanObject,
    mut v_k_1076_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v_zero_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1088_: u8 = 0;
    let mut v_one_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut v_a_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v_zero_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1102_: u8 = 0;
    let mut v_one_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v___x_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_k_1076_) {
                4 => {
                    v_a_1082_ = crate::leanh::lean_ctor_get(v_k_1076_, 0);
                    v_a_1083_ = crate::leanh::lean_ctor_get(v_k_1076_, 1);
                    v_isSharedCheck_1095_ = (!crate::leanh::lean_is_exclusive(v_k_1076_)) as u8;
                    if v_isSharedCheck_1095_ == 0 {
                        v___x_1085_ = v_k_1076_;
                        v_isShared_1086_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1083_);
                        crate::leanh::lean_inc(v_a_1082_);
                        crate::leanh::lean_dec(v_k_1076_);
                        v___x_1085_ = crate::leanh::lean_box(0);
                        v_isShared_1086_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    v_a_1096_ = crate::leanh::lean_ctor_get(v_k_1076_, 0);
                    v_a_1097_ = crate::leanh::lean_ctor_get(v_k_1076_, 1);
                    v_isSharedCheck_1109_ = (!crate::leanh::lean_is_exclusive(v_k_1076_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1099_ = v_k_1076_;
                        v_isShared_1100_ = v_isSharedCheck_1109_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1097_);
                        crate::leanh::lean_inc(v_a_1096_);
                        crate::leanh::lean_dec(v_k_1076_);
                        v___x_1099_ = crate::leanh::lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1109_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_k_1076_);
                    v___x_1110_ = 0;
                    return v___x_1110_;
                }
            },
            1 => {
                v___x_1079_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_1075_, v_k_1078_);
                if crate::leanh::lean_obj_tag(v___x_1079_) == 0 {
                    v_k_1076_ = v_k_1078_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1079_, 1);
                    crate::leanh::lean_dec(v_k_1078_);
                    v___x_1081_ = 1;
                    return v___x_1081_;
                }
            }
            2 => {
                v_zero_1087_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1088_ = lean_nat_dec_eq(v_a_1083_, v_zero_1087_);
                if v_isZero_1088_ == 0 {
                    v_one_1089_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1090_ = lean_nat_sub(v_a_1083_, v_one_1089_);
                    crate::leanh::lean_dec(v_a_1083_);
                    if v_isShared_1086_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1085_, 1, v_n_1090_);
                        v___x_1092_ = v___x_1085_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1093_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1082_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_n_1090_);
                        v___x_1092_ = v_reuseFailAlloc_1093_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1085_);
                    crate::leanh::lean_dec(v_a_1083_);
                    crate::leanh::lean_dec(v_a_1082_);
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
                v_zero_1101_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1102_ = lean_nat_dec_eq(v_a_1097_, v_zero_1101_);
                if v_isZero_1102_ == 0 {
                    v_one_1103_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1104_ = lean_nat_sub(v_a_1097_, v_one_1103_);
                    crate::leanh::lean_dec(v_a_1097_);
                    if v_isShared_1100_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1099_, 1, v_n_1104_);
                        v___x_1106_ = v___x_1099_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1107_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1096_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_n_1104_);
                        v___x_1106_ = v_reuseFailAlloc_1107_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1099_);
                    crate::leanh::lean_dec(v_a_1097_);
                    crate::leanh::lean_dec(v_a_1096_);
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
    mut v_d_1111_: *mut crate::leanh::LeanObject,
    mut v_k_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: u8 = 0;
    let mut v_r_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1111_, v_k_1112_);
    crate::leanh::lean_dec_ref(v_d_1111_);
    v_r_1114_ = crate::leanh::lean_box((v_res_1113_) as usize);
    return v_r_1114_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(
    mut v_00_u03b1_1115_: *mut crate::leanh::LeanObject,
    mut v_d_1116_: *mut crate::leanh::LeanObject,
    mut v_k_1117_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1118_: u8 = 0;
    v___x_1118_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1116_, v_k_1117_);
    return v___x_1118_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(
    mut v_00_u03b1_1119_: *mut crate::leanh::LeanObject,
    mut v_d_1120_: *mut crate::leanh::LeanObject,
    mut v_k_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: u8 = 0;
    let mut v_r_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(
            v_00_u03b1_1119_,
            v_d_1120_,
            v_k_1121_,
        );
    crate::leanh::lean_dec_ref(v_d_1120_);
    v_r_1123_ = crate::leanh::lean_box((v_res_1122_) as usize);
    return v_r_1123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(
    mut v_numExtra_1124_: *mut crate::leanh::LeanObject,
    mut v_sz_1125_: usize,
    mut v_i_1126_: usize,
    mut v_bs_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: u8 = 0;
    let mut v_v_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: usize = 0;
    let mut v___x_1134_: usize = 0;
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = lean_usize_dec_lt(v_i_1126_, v_sz_1125_);
                if v___x_1128_ == 0 {
                    crate::leanh::lean_dec(v_numExtra_1124_);
                    return v_bs_1127_;
                } else {
                    v_v_1129_ = lean_array_uget(v_bs_1127_, v_i_1126_);
                    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1131_ = lean_array_uset(v_bs_1127_, v_i_1126_, v___x_1130_);
                    crate::leanh::lean_inc(v_numExtra_1124_);
                    v___x_1132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1132_, 0, v_v_1129_);
                    crate::leanh::lean_ctor_set(v___x_1132_, 1, v_numExtra_1124_);
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
    mut v_numExtra_1137_: *mut crate::leanh::LeanObject,
    mut v_sz_1138_: *mut crate::leanh::LeanObject,
    mut v_i_1139_: *mut crate::leanh::LeanObject,
    mut v_bs_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1141_: usize = 0;
    let mut v_i_boxed_1142_: usize = 0;
    let mut v_res_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1141_ = crate::leanh::lean_unbox_usize(v_sz_1138_);
    crate::leanh::lean_dec(v_sz_1138_);
    v_i_boxed_1142_ = crate::leanh::lean_unbox_usize(v_i_1139_);
    crate::leanh::lean_dec(v_i_1139_);
    v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1137_, v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1140_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(
    mut v_d_1144_: *mut crate::leanh::LeanObject,
    mut v_e_1145_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1146_: *mut crate::leanh::LeanObject,
    mut v_result_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1149_: usize = 0;
    let mut v___x_1150_: usize = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1144_, v_e_1145_);
                v_sz_1149_ = lean_array_size(v___x_1148_);
                v___x_1150_ = 0usize;
                crate::leanh::lean_inc(v_numExtra_1146_);
                v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1146_, v_sz_1149_, v___x_1150_, v___x_1148_);
                v_result_1152_ = l_Array_append___redArg(v_result_1147_, v___x_1151_);
                crate::leanh::lean_dec_ref(v___x_1151_);
                v___x_1153_ = l_Lean_Expr_isApp(v_e_1145_);
                if v___x_1153_ == 0 {
                    crate::leanh::lean_dec(v_numExtra_1146_);
                    crate::leanh::lean_dec_ref(v_e_1145_);
                    return v_result_1152_;
                } else {
                    v___x_1154_ = l_Lean_Expr_appFn_x21(v_e_1145_);
                    crate::leanh::lean_dec_ref(v_e_1145_);
                    v___x_1155_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1156_ = lean_nat_add(v_numExtra_1146_, v___x_1155_);
                    crate::leanh::lean_dec(v_numExtra_1146_);
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
    mut v_d_1158_: *mut crate::leanh::LeanObject,
    mut v_e_1159_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1160_: *mut crate::leanh::LeanObject,
    mut v_result_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ =
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(
            v_d_1158_,
            v_e_1159_,
            v_numExtra_1160_,
            v_result_1161_,
        );
    crate::leanh::lean_dec_ref(v_d_1158_);
    return v_res_1162_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(
    mut v_00_u03b1_1163_: *mut crate::leanh::LeanObject,
    mut v_d_1164_: *mut crate::leanh::LeanObject,
    mut v_e_1165_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1166_: *mut crate::leanh::LeanObject,
    mut v_result_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1169_: *mut crate::leanh::LeanObject,
    mut v_d_1170_: *mut crate::leanh::LeanObject,
    mut v_e_1171_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1172_: *mut crate::leanh::LeanObject,
    mut v_result_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1174_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(
        v_00_u03b1_1169_,
        v_d_1170_,
        v_e_1171_,
        v_numExtra_1172_,
        v_result_1173_,
    );
    crate::leanh::lean_dec_ref(v_d_1170_);
    return v_res_1174_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(
    mut v_00_u03b1_1175_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1176_: *mut crate::leanh::LeanObject,
    mut v_sz_1177_: usize,
    mut v_i_1178_: usize,
    mut v_bs_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1176_, v_sz_1177_, v_i_1178_, v_bs_1179_);
    return v___x_1180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(
    mut v_00_u03b1_1181_: *mut crate::leanh::LeanObject,
    mut v_numExtra_1182_: *mut crate::leanh::LeanObject,
    mut v_sz_1183_: *mut crate::leanh::LeanObject,
    mut v_i_1184_: *mut crate::leanh::LeanObject,
    mut v_bs_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1186_: usize = 0;
    let mut v_i_boxed_1187_: usize = 0;
    let mut v_res_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1186_ = crate::leanh::lean_unbox_usize(v_sz_1183_);
    crate::leanh::lean_dec(v_sz_1183_);
    v_i_boxed_1187_ = crate::leanh::lean_unbox_usize(v_i_1184_);
    crate::leanh::lean_dec(v_i_1184_);
    v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_1181_, v_numExtra_1182_, v_sz_boxed_1186_, v_i_boxed_1187_, v_bs_1185_);
    return v_res_1188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(
    mut v_sz_1189_: usize,
    mut v_i_1190_: usize,
    mut v_bs_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v_v_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = lean_usize_dec_lt(v_i_1190_, v_sz_1189_);
                if v___x_1192_ == 0 {
                    return v_bs_1191_;
                } else {
                    v_v_1193_ = lean_array_uget(v_bs_1191_, v_i_1190_);
                    v___x_1194_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1195_ = lean_array_uset(v_bs_1191_, v_i_1190_, v___x_1194_);
                    v___x_1196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1196_, 0, v_v_1193_);
                    crate::leanh::lean_ctor_set(v___x_1196_, 1, v___x_1194_);
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
    mut v_sz_1201_: *mut crate::leanh::LeanObject,
    mut v_i_1202_: *mut crate::leanh::LeanObject,
    mut v_bs_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1204_: usize = 0;
    let mut v_i_boxed_1205_: usize = 0;
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1204_ = crate::leanh::lean_unbox_usize(v_sz_1201_);
    crate::leanh::lean_dec(v_sz_1201_);
    v_i_boxed_1205_ = crate::leanh::lean_unbox_usize(v_i_1202_);
    crate::leanh::lean_dec(v_i_1202_);
    v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_1204_, v_i_boxed_1205_, v_bs_1203_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___redArg(
    mut v_d_1207_: *mut crate::leanh::LeanObject,
    mut v_e_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1211_: usize = 0;
    let mut v___x_1212_: usize = 0;
    let mut v_result_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: u8 = 0;
    v_e_1209_ = l_Lean_Meta_Sym_etaReduce(v_e_1208_);
    v_result_1210_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_1207_, v_e_1209_);
    v_sz_1211_ = lean_array_size(v_result_1210_);
    v___x_1212_ = 0usize;
    v_result_1213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_1211_, v___x_1212_, v_result_1210_);
    v___x_1214_ = l_Lean_Expr_isApp(v_e_1209_);
    if v___x_1214_ == 0 {
        crate::leanh::lean_dec_ref(v_e_1209_);
        return v_result_1213_;
    } else {
        let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: u8 = 0;
        v___x_1215_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_1209_);
        v___x_1216_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1207_, v___x_1215_);
        if v___x_1216_ == 0 {
            crate::leanh::lean_dec_ref(v_e_1209_);
            return v_result_1213_;
        } else {
            let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1217_ = l_Lean_Expr_appFn_x21(v_e_1209_);
            crate::leanh::lean_dec_ref(v_e_1209_);
            v___x_1218_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1219_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_1207_, v___x_1217_, v___x_1218_, v_result_1213_);
            return v___x_1219_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(
    mut v_d_1220_: *mut crate::leanh::LeanObject,
    mut v_e_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_1220_, v_e_1221_);
    crate::leanh::lean_dec_ref(v_e_1221_);
    crate::leanh::lean_dec_ref(v_d_1220_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra(
    mut v_00_u03b1_1223_: *mut crate::leanh::LeanObject,
    mut v_d_1224_: *mut crate::leanh::LeanObject,
    mut v_e_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_1224_, v_e_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lean_Meta_Sym_getMatchWithExtra___boxed(
    mut v_00_u03b1_1227_: *mut crate::leanh::LeanObject,
    mut v_d_1228_: *mut crate::leanh::LeanObject,
    mut v_e_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_1227_, v_d_1228_, v_e_1229_);
    crate::leanh::lean_dec_ref(v_e_1229_);
    crate::leanh::lean_dec_ref(v_d_1228_);
    return v_res_1230_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(
    mut v_00_u03b1_1231_: *mut crate::leanh::LeanObject,
    mut v_sz_1232_: usize,
    mut v_i_1233_: usize,
    mut v_bs_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_1232_, v_i_1233_, v_bs_1234_);
    return v___x_1235_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(
    mut v_00_u03b1_1236_: *mut crate::leanh::LeanObject,
    mut v_sz_1237_: *mut crate::leanh::LeanObject,
    mut v_i_1238_: *mut crate::leanh::LeanObject,
    mut v_bs_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1240_: usize = 0;
    let mut v_i_boxed_1241_: usize = 0;
    let mut v_res_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1240_ = crate::leanh::lean_unbox_usize(v_sz_1237_);
    crate::leanh::lean_dec(v_sz_1237_);
    v_i_boxed_1241_ = crate::leanh::lean_unbox_usize(v_i_1238_);
    crate::leanh::lean_dec(v_i_1238_);
    v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_1236_, v_sz_boxed_1240_, v_i_boxed_1241_, v_bs_1239_);
    return v_res_1242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity =
        _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_DiscrTree(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
}
