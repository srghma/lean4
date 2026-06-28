// Lean compiler output
// Module: Lean.Meta.Tactic.ExposeNames
// Imports: Lean.Meta.Tactic.Util Init.While
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, lean_erase_macro_scopes,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_set___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_get_x21, l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_index,
    l_Lean_LocalDecl_setUserName, l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
    lean_local_ctx_find,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_exposeNames___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 120, 112, 111, 115, 101, 95, 110, 97, 109, 101, 115, 0],
};
static mut l_Lean_MVarId_exposeNames___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_exposeNames___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__0_value) as *mut LeanObject,
        8944005891006136425 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_exposeNames___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(
    mut v_a_1886_: *mut LeanObject,
    mut v_b_1887_: *mut LeanObject,
    mut v_x_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1888_) == 0 {
                    lean_dec(v_b_1887_);
                    lean_dec(v_a_1886_);
                    return v_x_1888_;
                } else {
                    v_key_1889_ = lean_ctor_get(v_x_1888_, 0);
                    v_value_1890_ = lean_ctor_get(v_x_1888_, 1);
                    v_tail_1891_ = lean_ctor_get(v_x_1888_, 2);
                    v_isSharedCheck_1903_ = (!lean_is_exclusive(v_x_1888_)) as u8;
                    if v_isSharedCheck_1903_ == 0 {
                        v___x_1893_ = v_x_1888_;
                        v_isShared_1894_ = v_isSharedCheck_1903_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1891_);
                        lean_inc(v_value_1890_);
                        lean_inc(v_key_1889_);
                        lean_dec(v_x_1888_);
                        v___x_1893_ = lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1903_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1895_ = lean_name_eq(v_key_1889_, v_a_1886_);
                if v___x_1895_ == 0 {
                    v___x_1896_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(v_a_1886_, v_b_1887_, v_tail_1891_);
                    if v_isShared_1894_ == 0 {
                        lean_ctor_set(v___x_1893_, 2, v___x_1896_);
                        v___x_1898_ = v___x_1893_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_key_1889_);
                        lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_value_1890_);
                        lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___x_1896_);
                        v___x_1898_ = v_reuseFailAlloc_1899_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1890_);
                    lean_dec(v_key_1889_);
                    if v_isShared_1894_ == 0 {
                        lean_ctor_set(v___x_1893_, 1, v_b_1887_);
                        lean_ctor_set(v___x_1893_, 0, v_a_1886_);
                        v___x_1901_ = v___x_1893_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1886_);
                        lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_b_1887_);
                        lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_tail_1891_);
                        v___x_1901_ = v_reuseFailAlloc_1902_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1898_;
            }
            3 => {
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0()
-> u64 {
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u64 = 0;
    v___x_1904_ = lean_unsigned_to_nat(1723);
    v___x_1905_ = lean_uint64_of_nat(v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(
    mut v_x_1906_: *mut LeanObject,
    mut v_x_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1916_: u64 = 0;
    let mut v___x_1917_: u64 = 0;
    let mut v___x_1918_: u64 = 0;
    let mut v_fold_1919_: u64 = 0;
    let mut v___x_1920_: u64 = 0;
    let mut v___x_1921_: u64 = 0;
    let mut v___x_1922_: u64 = 0;
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: usize = 0;
    let mut v___x_1925_: usize = 0;
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u64 = 0;
    let mut v_hash_1935_: u64 = 0;
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1907_) == 0 {
                    return v_x_1906_;
                } else {
                    v_key_1908_ = lean_ctor_get(v_x_1907_, 0);
                    v_value_1909_ = lean_ctor_get(v_x_1907_, 1);
                    v_tail_1910_ = lean_ctor_get(v_x_1907_, 2);
                    v_isSharedCheck_1936_ = (!lean_is_exclusive(v_x_1907_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1912_ = v_x_1907_;
                        v_isShared_1913_ = v_isSharedCheck_1936_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1910_);
                        lean_inc(v_value_1909_);
                        lean_inc(v_key_1908_);
                        lean_dec(v_x_1907_);
                        v___x_1912_ = lean_box(0);
                        v_isShared_1913_ = v_isSharedCheck_1936_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1914_ = lean_array_get_size(v_x_1906_);
                if lean_obj_tag(v_key_1908_) == 0 {
                    v___x_1934_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_1916_ = v___x_1934_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1935_ = lean_ctor_get_uint64(
                        v_key_1908_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1916_ = v_hash_1935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1917_ = 32u64;
                v___x_1918_ = lean_uint64_shift_right(v___y_1916_, v___x_1917_);
                v_fold_1919_ = lean_uint64_xor(v___y_1916_, v___x_1918_);
                v___x_1920_ = 16u64;
                v___x_1921_ = lean_uint64_shift_right(v_fold_1919_, v___x_1920_);
                v___x_1922_ = lean_uint64_xor(v_fold_1919_, v___x_1921_);
                v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
                v___x_1924_ = lean_usize_of_nat(v___x_1914_);
                v___x_1925_ = 1usize;
                v___x_1926_ = lean_usize_sub(v___x_1924_, v___x_1925_);
                v___x_1927_ = lean_usize_land(v___x_1923_, v___x_1926_);
                v___x_1928_ = lean_array_uget_borrowed(v_x_1906_, v___x_1927_);
                lean_inc(v___x_1928_);
                if v_isShared_1913_ == 0 {
                    lean_ctor_set(v___x_1912_, 2, v___x_1928_);
                    v___x_1930_ = v___x_1912_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_key_1908_);
                    lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_value_1909_);
                    lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1928_);
                    v___x_1930_ = v_reuseFailAlloc_1933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1931_ = lean_array_uset(v_x_1906_, v___x_1927_, v___x_1930_);
                v_x_1906_ = v___x_1931_;
                v_x_1907_ = v_tail_1910_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2___redArg(
    mut v_i_1937_: *mut LeanObject,
    mut v_source_1938_: *mut LeanObject,
    mut v_target_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v_es_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_array_get_size(v_source_1938_);
                v___x_1941_ = lean_nat_dec_lt(v_i_1937_, v___x_1940_);
                if v___x_1941_ == 0 {
                    lean_dec_ref(v_source_1938_);
                    lean_dec(v_i_1937_);
                    return v_target_1939_;
                } else {
                    v_es_1942_ = lean_array_fget(v_source_1938_, v_i_1937_);
                    v___x_1943_ = lean_box(0);
                    v_source_1944_ = lean_array_fset(v_source_1938_, v_i_1937_, v___x_1943_);
                    v_target_1945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(v_target_1939_, v_es_1942_);
                    v___x_1946_ = lean_unsigned_to_nat(1);
                    v___x_1947_ = lean_nat_add(v_i_1937_, v___x_1946_);
                    lean_dec(v_i_1937_);
                    v_i_1937_ = v___x_1947_;
                    v_source_1938_ = v_source_1944_;
                    v_target_1939_ = v_target_1945_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1___redArg(
    mut v_data_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_array_get_size(v_data_1949_);
    v___x_1951_ = lean_unsigned_to_nat(2);
    v_nbuckets_1952_ = lean_nat_mul(v___x_1950_, v___x_1951_);
    v___x_1953_ = lean_unsigned_to_nat(0);
    v___x_1954_ = lean_box(0);
    v___x_1955_ = lean_mk_array(v_nbuckets_1952_, v___x_1954_);
    v___x_1956_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2___redArg(v___x_1953_, v_data_1949_, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(
    mut v_a_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
) -> u8 {
    let mut v___x_1959_: u8 = 0;
    let mut v_key_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1958_) == 0 {
                    v___x_1959_ = 0;
                    return v___x_1959_;
                } else {
                    v_key_1960_ = lean_ctor_get(v_x_1958_, 0);
                    v_tail_1961_ = lean_ctor_get(v_x_1958_, 2);
                    v___x_1962_ = lean_name_eq(v_key_1960_, v_a_1957_);
                    if v___x_1962_ == 0 {
                        v_x_1958_ = v_tail_1961_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1962_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg___boxed(
    mut v_a_1964_: *mut LeanObject,
    mut v_x_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1966_: u8 = 0;
    let mut v_r_1967_: *mut LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_1964_, v_x_1965_);
    lean_dec(v_x_1965_);
    lean_dec(v_a_1964_);
    v_r_1967_ = lean_box((v_res_1966_) as usize);
    return v_r_1967_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(
    mut v_m_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_b_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: u64 = 0;
    let mut v___x_1979_: u64 = 0;
    let mut v___x_1980_: u64 = 0;
    let mut v_fold_1981_: u64 = 0;
    let mut v___x_1982_: u64 = 0;
    let mut v___x_1983_: u64 = 0;
    let mut v___x_1984_: u64 = 0;
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: usize = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: usize = 0;
    let mut v_bkt_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v_val_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u64 = 0;
    let mut v_hash_2017_: u64 = 0;
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1971_ = lean_ctor_get(v_m_1968_, 0);
                v_buckets_1972_ = lean_ctor_get(v_m_1968_, 1);
                v_isSharedCheck_2018_ = (!lean_is_exclusive(v_m_1968_)) as u8;
                if v_isSharedCheck_2018_ == 0 {
                    v___x_1974_ = v_m_1968_;
                    v_isShared_1975_ = v_isSharedCheck_2018_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1972_);
                    lean_inc(v_size_1971_);
                    lean_dec(v_m_1968_);
                    v___x_1974_ = lean_box(0);
                    v_isShared_1975_ = v_isSharedCheck_2018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1976_ = lean_array_get_size(v_buckets_1972_);
                if lean_obj_tag(v_a_1969_) == 0 {
                    v___x_2016_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_1978_ = v___x_2016_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2017_ = lean_ctor_get_uint64(
                        v_a_1969_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1978_ = v_hash_2017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1979_ = 32u64;
                v___x_1980_ = lean_uint64_shift_right(v___y_1978_, v___x_1979_);
                v_fold_1981_ = lean_uint64_xor(v___y_1978_, v___x_1980_);
                v___x_1982_ = 16u64;
                v___x_1983_ = lean_uint64_shift_right(v_fold_1981_, v___x_1982_);
                v___x_1984_ = lean_uint64_xor(v_fold_1981_, v___x_1983_);
                v___x_1985_ = lean_uint64_to_usize(v___x_1984_);
                v___x_1986_ = lean_usize_of_nat(v___x_1976_);
                v___x_1987_ = 1usize;
                v___x_1988_ = lean_usize_sub(v___x_1986_, v___x_1987_);
                v___x_1989_ = lean_usize_land(v___x_1985_, v___x_1988_);
                v_bkt_1990_ = lean_array_uget_borrowed(v_buckets_1972_, v___x_1989_);
                v___x_1991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_1969_, v_bkt_1990_);
                if v___x_1991_ == 0 {
                    v___x_1992_ = lean_unsigned_to_nat(1);
                    v_size_x27_1993_ = lean_nat_add(v_size_1971_, v___x_1992_);
                    lean_dec(v_size_1971_);
                    lean_inc(v_bkt_1990_);
                    v___x_1994_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1994_, 0, v_a_1969_);
                    lean_ctor_set(v___x_1994_, 1, v_b_1970_);
                    lean_ctor_set(v___x_1994_, 2, v_bkt_1990_);
                    v_buckets_x27_1995_ =
                        lean_array_uset(v_buckets_1972_, v___x_1989_, v___x_1994_);
                    v___x_1996_ = lean_unsigned_to_nat(4);
                    v___x_1997_ = lean_nat_mul(v_size_x27_1993_, v___x_1996_);
                    v___x_1998_ = lean_unsigned_to_nat(3);
                    v___x_1999_ = lean_nat_div(v___x_1997_, v___x_1998_);
                    lean_dec(v___x_1997_);
                    v___x_2000_ = lean_array_get_size(v_buckets_x27_1995_);
                    v___x_2001_ = lean_nat_dec_le(v___x_1999_, v___x_2000_);
                    lean_dec(v___x_1999_);
                    if v___x_2001_ == 0 {
                        v_val_2002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1___redArg(v_buckets_x27_1995_);
                        if v_isShared_1975_ == 0 {
                            lean_ctor_set(v___x_1974_, 1, v_val_2002_);
                            lean_ctor_set(v___x_1974_, 0, v_size_x27_1993_);
                            v___x_2004_ = v___x_1974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_size_x27_1993_);
                            lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_val_2002_);
                            v___x_2004_ = v_reuseFailAlloc_2005_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1975_ == 0 {
                            lean_ctor_set(v___x_1974_, 1, v_buckets_x27_1995_);
                            lean_ctor_set(v___x_1974_, 0, v_size_x27_1993_);
                            v___x_2007_ = v___x_1974_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_size_x27_1993_);
                            lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_buckets_x27_1995_);
                            v___x_2007_ = v_reuseFailAlloc_2008_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1990_);
                    v___x_2009_ = lean_box(0);
                    v_buckets_x27_2010_ =
                        lean_array_uset(v_buckets_1972_, v___x_1989_, v___x_2009_);
                    v___x_2011_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(v_a_1969_, v_b_1970_, v_bkt_1990_);
                    v___x_2012_ = lean_array_uset(v_buckets_x27_2010_, v___x_1989_, v___x_2011_);
                    if v_isShared_1975_ == 0 {
                        lean_ctor_set(v___x_1974_, 1, v___x_2012_);
                        v___x_2014_ = v___x_1974_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_size_1971_);
                        lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2012_);
                        v___x_2014_ = v_reuseFailAlloc_2015_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2004_;
            }
            4 => {
                return v___x_2007_;
            }
            5 => {
                return v___x_2014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(
    mut v_a_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2020_) == 0 {
                    v___x_2021_ = lean_box(0);
                    return v___x_2021_;
                } else {
                    v_key_2022_ = lean_ctor_get(v_x_2020_, 0);
                    v_value_2023_ = lean_ctor_get(v_x_2020_, 1);
                    v_tail_2024_ = lean_ctor_get(v_x_2020_, 2);
                    v___x_2025_ = lean_name_eq(v_key_2022_, v_a_2019_);
                    if v___x_2025_ == 0 {
                        v_x_2020_ = v_tail_2024_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2023_);
                        v___x_2027_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2027_, 0, v_value_2023_);
                        return v___x_2027_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg___boxed(
    mut v_a_2028_: *mut LeanObject,
    mut v_x_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(v_a_2028_, v_x_2029_);
    lean_dec(v_x_2029_);
    lean_dec(v_a_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(
    mut v_m_2031_: *mut LeanObject,
    mut v_a_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2036_: u64 = 0;
    let mut v___x_2037_: u64 = 0;
    let mut v___x_2038_: u64 = 0;
    let mut v_fold_2039_: u64 = 0;
    let mut v___x_2040_: u64 = 0;
    let mut v___x_2041_: u64 = 0;
    let mut v___x_2042_: u64 = 0;
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: usize = 0;
    let mut v___x_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: u64 = 0;
    let mut v_hash_2051_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2033_ = lean_ctor_get(v_m_2031_, 1);
                v___x_2034_ = lean_array_get_size(v_buckets_2033_);
                if lean_obj_tag(v_a_2032_) == 0 {
                    v___x_2050_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_2036_ = v___x_2050_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2051_ = lean_ctor_get_uint64(
                        v_a_2032_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2036_ = v_hash_2051_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2037_ = 32u64;
                v___x_2038_ = lean_uint64_shift_right(v___y_2036_, v___x_2037_);
                v_fold_2039_ = lean_uint64_xor(v___y_2036_, v___x_2038_);
                v___x_2040_ = 16u64;
                v___x_2041_ = lean_uint64_shift_right(v_fold_2039_, v___x_2040_);
                v___x_2042_ = lean_uint64_xor(v_fold_2039_, v___x_2041_);
                v___x_2043_ = lean_uint64_to_usize(v___x_2042_);
                v___x_2044_ = lean_usize_of_nat(v___x_2034_);
                v___x_2045_ = 1usize;
                v___x_2046_ = lean_usize_sub(v___x_2044_, v___x_2045_);
                v___x_2047_ = lean_usize_land(v___x_2043_, v___x_2046_);
                v___x_2048_ = lean_array_uget_borrowed(v_buckets_2033_, v___x_2047_);
                v___x_2049_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(v_a_2032_, v___x_2048_);
                return v___x_2049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg___boxed(
    mut v_m_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2054_: *mut LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_m_2052_, v_a_2053_);
    lean_dec(v_a_2053_);
    lean_dec_ref(v_m_2052_);
    return v_res_2054_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(
    mut v_as_2055_: *mut LeanObject,
    mut v_sz_2056_: usize,
    mut v_i_2057_: usize,
    mut v_b_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: usize = 0;
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRename_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: u8 = 0;
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_unused_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_usize_dec_lt(v_i_2057_, v_sz_2056_);
                if v___x_2060_ == 0 {
                    v___x_2061_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2061_, 0, v_b_2058_);
                    return v___x_2061_;
                } else {
                    v_snd_2062_ = lean_ctor_get(v_b_2058_, 1);
                    v_isSharedCheck_2098_ = (!lean_is_exclusive(v_b_2058_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v_unused_2099_ = lean_ctor_get(v_b_2058_, 0);
                        lean_dec(v_unused_2099_);
                        v___x_2064_ = v_b_2058_;
                        v_isShared_2065_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2062_);
                        lean_dec(v_b_2058_);
                        v___x_2064_ = lean_box(0);
                        v_isShared_2065_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2066_ = lean_box(0);
                v_a_2075_ = lean_array_uget_borrowed(v_as_2055_, v_i_2057_);
                if lean_obj_tag(v_a_2075_) == 0 {
                    v_a_2068_ = v_snd_2062_;
                    state = 2;
                    continue;
                } else {
                    v_val_2076_ = lean_ctor_get(v_a_2075_, 0);
                    v_fst_2077_ = lean_ctor_get(v_snd_2062_, 0);
                    v_snd_2078_ = lean_ctor_get(v_snd_2062_, 1);
                    v_isSharedCheck_2097_ = (!lean_is_exclusive(v_snd_2062_)) as u8;
                    if v_isSharedCheck_2097_ == 0 {
                        v___x_2080_ = v_snd_2062_;
                        v_isShared_2081_ = v_isSharedCheck_2097_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2078_);
                        lean_inc(v_fst_2077_);
                        lean_dec(v_snd_2062_);
                        v___x_2080_ = lean_box(0);
                        v_isShared_2081_ = v_isSharedCheck_2097_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2065_ == 0 {
                    lean_ctor_set(v___x_2064_, 1, v_a_2068_);
                    lean_ctor_set(v___x_2064_, 0, v___x_2066_);
                    v___x_2070_ = v___x_2064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2066_);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_a_2068_);
                    v___x_2070_ = v_reuseFailAlloc_2074_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2071_ = 1usize;
                v___x_2072_ = lean_usize_add(v_i_2057_, v___x_2071_);
                v_i_2057_ = v___x_2072_;
                v_b_2058_ = v___x_2070_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2082_ = l_Lean_LocalDecl_userName(v_val_2076_);
                v___x_2090_ = l_Lean_Name_hasMacroScopes(v___x_2082_);
                if v___x_2090_ == 0 {
                    v___x_2091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_fst_2077_, v___x_2082_);
                    if lean_obj_tag(v___x_2091_) == 1 {
                        v_val_2092_ = lean_ctor_get(v___x_2091_, 0);
                        lean_inc(v_val_2092_);
                        lean_dec_ref_known(v___x_2091_, 1);
                        v___x_2093_ = lean_array_push(v_snd_2078_, v_val_2092_);
                        v_toRename_2084_ = v___x_2093_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2091_);
                        v_toRename_2084_ = v_snd_2078_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2082_);
                    lean_del_object(v___x_2080_);
                    v___x_2094_ = l_Lean_LocalDecl_fvarId(v_val_2076_);
                    v___x_2095_ = lean_array_push(v_snd_2078_, v___x_2094_);
                    v___x_2096_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2096_, 0, v_fst_2077_);
                    lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                    v_a_2068_ = v___x_2096_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2085_ = l_Lean_LocalDecl_fvarId(v_val_2076_);
                v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2077_, v___x_2082_, v___x_2085_);
                if v_isShared_2081_ == 0 {
                    lean_ctor_set(v___x_2080_, 1, v_toRename_2084_);
                    lean_ctor_set(v___x_2080_, 0, v___x_2086_);
                    v___x_2088_ = v___x_2080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
                    lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_toRename_2084_);
                    v___x_2088_ = v_reuseFailAlloc_2089_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2068_ = v___x_2088_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg___boxed(
    mut v_as_2100_: *mut LeanObject,
    mut v_sz_2101_: *mut LeanObject,
    mut v_i_2102_: *mut LeanObject,
    mut v_b_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2105_: usize = 0;
    let mut v_i_boxed_2106_: usize = 0;
    let mut v_res_2107_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2101_);
    lean_dec(v_sz_2101_);
    v_i_boxed_2106_ = lean_unbox_usize(v_i_2102_);
    lean_dec(v_i_2102_);
    v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(v_as_2100_, v_sz_boxed_2105_, v_i_boxed_2106_, v_b_2103_);
    lean_dec_ref(v_as_2100_);
    return v_res_2107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(
    mut v_as_2108_: *mut LeanObject,
    mut v_sz_2109_: usize,
    mut v_i_2110_: usize,
    mut v_b_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: usize = 0;
    let mut v___x_2129_: usize = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2138_: u8 = 0;
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRename_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_unused_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_lt(v_i_2110_, v_sz_2109_);
                if v___x_2117_ == 0 {
                    v___x_2118_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2118_, 0, v_b_2111_);
                    return v___x_2118_;
                } else {
                    v_snd_2119_ = lean_ctor_get(v_b_2111_, 1);
                    v_isSharedCheck_2155_ = (!lean_is_exclusive(v_b_2111_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v_unused_2156_ = lean_ctor_get(v_b_2111_, 0);
                        lean_dec(v_unused_2156_);
                        v___x_2121_ = v_b_2111_;
                        v_isShared_2122_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2119_);
                        lean_dec(v_b_2111_);
                        v___x_2121_ = lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2123_ = lean_box(0);
                v_a_2132_ = lean_array_uget_borrowed(v_as_2108_, v_i_2110_);
                if lean_obj_tag(v_a_2132_) == 0 {
                    v_a_2125_ = v_snd_2119_;
                    state = 2;
                    continue;
                } else {
                    v_val_2133_ = lean_ctor_get(v_a_2132_, 0);
                    v_fst_2134_ = lean_ctor_get(v_snd_2119_, 0);
                    v_snd_2135_ = lean_ctor_get(v_snd_2119_, 1);
                    v_isSharedCheck_2154_ = (!lean_is_exclusive(v_snd_2119_)) as u8;
                    if v_isSharedCheck_2154_ == 0 {
                        v___x_2137_ = v_snd_2119_;
                        v_isShared_2138_ = v_isSharedCheck_2154_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2135_);
                        lean_inc(v_fst_2134_);
                        lean_dec(v_snd_2119_);
                        v___x_2137_ = lean_box(0);
                        v_isShared_2138_ = v_isSharedCheck_2154_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2122_ == 0 {
                    lean_ctor_set(v___x_2121_, 1, v_a_2125_);
                    lean_ctor_set(v___x_2121_, 0, v___x_2123_);
                    v___x_2127_ = v___x_2121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2123_);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2125_);
                    v___x_2127_ = v_reuseFailAlloc_2131_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2128_ = 1usize;
                v___x_2129_ = lean_usize_add(v_i_2110_, v___x_2128_);
                v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(v_as_2108_, v_sz_2109_, v___x_2129_, v___x_2127_);
                return v___x_2130_;
            }
            4 => {
                v___x_2139_ = l_Lean_LocalDecl_userName(v_val_2133_);
                v___x_2147_ = l_Lean_Name_hasMacroScopes(v___x_2139_);
                if v___x_2147_ == 0 {
                    v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_fst_2134_, v___x_2139_);
                    if lean_obj_tag(v___x_2148_) == 1 {
                        v_val_2149_ = lean_ctor_get(v___x_2148_, 0);
                        lean_inc(v_val_2149_);
                        lean_dec_ref_known(v___x_2148_, 1);
                        v___x_2150_ = lean_array_push(v_snd_2135_, v_val_2149_);
                        v_toRename_2141_ = v___x_2150_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2148_);
                        v_toRename_2141_ = v_snd_2135_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2139_);
                    lean_del_object(v___x_2137_);
                    v___x_2151_ = l_Lean_LocalDecl_fvarId(v_val_2133_);
                    v___x_2152_ = lean_array_push(v_snd_2135_, v___x_2151_);
                    v___x_2153_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2153_, 0, v_fst_2134_);
                    lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                    v_a_2125_ = v___x_2153_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2142_ = l_Lean_LocalDecl_fvarId(v_val_2133_);
                v___x_2143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2134_, v___x_2139_, v___x_2142_);
                if v_isShared_2138_ == 0 {
                    lean_ctor_set(v___x_2137_, 1, v_toRename_2141_);
                    lean_ctor_set(v___x_2137_, 0, v___x_2143_);
                    v___x_2145_ = v___x_2137_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_toRename_2141_);
                    v___x_2145_ = v_reuseFailAlloc_2146_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2125_ = v___x_2145_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7___boxed(
    mut v_as_2157_: *mut LeanObject,
    mut v_sz_2158_: *mut LeanObject,
    mut v_i_2159_: *mut LeanObject,
    mut v_b_2160_: *mut LeanObject,
    mut v___y_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2166_: usize = 0;
    let mut v_i_boxed_2167_: usize = 0;
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2158_);
    lean_dec(v_sz_2158_);
    v_i_boxed_2167_ = lean_unbox_usize(v_i_2159_);
    lean_dec(v_i_2159_);
    v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(v_as_2157_, v_sz_boxed_2166_, v_i_boxed_2167_, v_b_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
    lean_dec(v___y_2164_);
    lean_dec_ref(v___y_2163_);
    lean_dec(v___y_2162_);
    lean_dec_ref(v___y_2161_);
    lean_dec_ref(v_as_2157_);
    return v_res_2168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(
    mut v_as_2169_: *mut LeanObject,
    mut v_sz_2170_: usize,
    mut v_i_2171_: usize,
    mut v_b_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: usize = 0;
    let mut v___x_2186_: usize = 0;
    let mut v_reuseFailAlloc_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRename_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_unused_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2174_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
                if v___x_2174_ == 0 {
                    v___x_2175_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2175_, 0, v_b_2172_);
                    return v___x_2175_;
                } else {
                    v_snd_2176_ = lean_ctor_get(v_b_2172_, 1);
                    v_isSharedCheck_2212_ = (!lean_is_exclusive(v_b_2172_)) as u8;
                    if v_isSharedCheck_2212_ == 0 {
                        v_unused_2213_ = lean_ctor_get(v_b_2172_, 0);
                        lean_dec(v_unused_2213_);
                        v___x_2178_ = v_b_2172_;
                        v_isShared_2179_ = v_isSharedCheck_2212_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2176_);
                        lean_dec(v_b_2172_);
                        v___x_2178_ = lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2180_ = lean_box(0);
                v_a_2189_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
                if lean_obj_tag(v_a_2189_) == 0 {
                    v_a_2182_ = v_snd_2176_;
                    state = 2;
                    continue;
                } else {
                    v_val_2190_ = lean_ctor_get(v_a_2189_, 0);
                    v_fst_2191_ = lean_ctor_get(v_snd_2176_, 0);
                    v_snd_2192_ = lean_ctor_get(v_snd_2176_, 1);
                    v_isSharedCheck_2211_ = (!lean_is_exclusive(v_snd_2176_)) as u8;
                    if v_isSharedCheck_2211_ == 0 {
                        v___x_2194_ = v_snd_2176_;
                        v_isShared_2195_ = v_isSharedCheck_2211_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2192_);
                        lean_inc(v_fst_2191_);
                        lean_dec(v_snd_2176_);
                        v___x_2194_ = lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2211_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2179_ == 0 {
                    lean_ctor_set(v___x_2178_, 1, v_a_2182_);
                    lean_ctor_set(v___x_2178_, 0, v___x_2180_);
                    v___x_2184_ = v___x_2178_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2180_);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2185_ = 1usize;
                v___x_2186_ = lean_usize_add(v_i_2171_, v___x_2185_);
                v_i_2171_ = v___x_2186_;
                v_b_2172_ = v___x_2184_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2196_ = l_Lean_LocalDecl_userName(v_val_2190_);
                v___x_2204_ = l_Lean_Name_hasMacroScopes(v___x_2196_);
                if v___x_2204_ == 0 {
                    v___x_2205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_fst_2191_, v___x_2196_);
                    if lean_obj_tag(v___x_2205_) == 1 {
                        v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
                        lean_inc(v_val_2206_);
                        lean_dec_ref_known(v___x_2205_, 1);
                        v___x_2207_ = lean_array_push(v_snd_2192_, v_val_2206_);
                        v_toRename_2198_ = v___x_2207_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2205_);
                        v_toRename_2198_ = v_snd_2192_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2196_);
                    lean_del_object(v___x_2194_);
                    v___x_2208_ = l_Lean_LocalDecl_fvarId(v_val_2190_);
                    v___x_2209_ = lean_array_push(v_snd_2192_, v___x_2208_);
                    v___x_2210_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2210_, 0, v_fst_2191_);
                    lean_ctor_set(v___x_2210_, 1, v___x_2209_);
                    v_a_2182_ = v___x_2210_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2199_ = l_Lean_LocalDecl_fvarId(v_val_2190_);
                v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2191_, v___x_2196_, v___x_2199_);
                if v_isShared_2195_ == 0 {
                    lean_ctor_set(v___x_2194_, 1, v_toRename_2198_);
                    lean_ctor_set(v___x_2194_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2194_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_toRename_2198_);
                    v___x_2202_ = v_reuseFailAlloc_2203_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2182_ = v___x_2202_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg___boxed(
    mut v_as_2214_: *mut LeanObject,
    mut v_sz_2215_: *mut LeanObject,
    mut v_i_2216_: *mut LeanObject,
    mut v_b_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2219_: usize = 0;
    let mut v_i_boxed_2220_: usize = 0;
    let mut v_res_2221_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2215_);
    lean_dec(v_sz_2215_);
    v_i_boxed_2220_ = lean_unbox_usize(v_i_2216_);
    lean_dec(v_i_2216_);
    v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(v_as_2214_, v_sz_boxed_2219_, v_i_boxed_2220_, v_b_2217_);
    lean_dec_ref(v_as_2214_);
    return v_res_2221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(
    mut v_as_2222_: *mut LeanObject,
    mut v_sz_2223_: usize,
    mut v_i_2224_: usize,
    mut v_b_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRename_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut v_unused_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
                if v___x_2231_ == 0 {
                    v___x_2232_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2232_, 0, v_b_2225_);
                    return v___x_2232_;
                } else {
                    v_snd_2233_ = lean_ctor_get(v_b_2225_, 1);
                    v_isSharedCheck_2269_ = (!lean_is_exclusive(v_b_2225_)) as u8;
                    if v_isSharedCheck_2269_ == 0 {
                        v_unused_2270_ = lean_ctor_get(v_b_2225_, 0);
                        lean_dec(v_unused_2270_);
                        v___x_2235_ = v_b_2225_;
                        v_isShared_2236_ = v_isSharedCheck_2269_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2233_);
                        lean_dec(v_b_2225_);
                        v___x_2235_ = lean_box(0);
                        v_isShared_2236_ = v_isSharedCheck_2269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2237_ = lean_box(0);
                v_a_2246_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
                if lean_obj_tag(v_a_2246_) == 0 {
                    v_a_2239_ = v_snd_2233_;
                    state = 2;
                    continue;
                } else {
                    v_val_2247_ = lean_ctor_get(v_a_2246_, 0);
                    v_fst_2248_ = lean_ctor_get(v_snd_2233_, 0);
                    v_snd_2249_ = lean_ctor_get(v_snd_2233_, 1);
                    v_isSharedCheck_2268_ = (!lean_is_exclusive(v_snd_2233_)) as u8;
                    if v_isSharedCheck_2268_ == 0 {
                        v___x_2251_ = v_snd_2233_;
                        v_isShared_2252_ = v_isSharedCheck_2268_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2249_);
                        lean_inc(v_fst_2248_);
                        lean_dec(v_snd_2233_);
                        v___x_2251_ = lean_box(0);
                        v_isShared_2252_ = v_isSharedCheck_2268_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2236_ == 0 {
                    lean_ctor_set(v___x_2235_, 1, v_a_2239_);
                    lean_ctor_set(v___x_2235_, 0, v___x_2237_);
                    v___x_2241_ = v___x_2235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2237_);
                    lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2239_);
                    v___x_2241_ = v_reuseFailAlloc_2245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2242_ = 1usize;
                v___x_2243_ = lean_usize_add(v_i_2224_, v___x_2242_);
                v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(v_as_2222_, v_sz_2223_, v___x_2243_, v___x_2241_);
                return v___x_2244_;
            }
            4 => {
                v___x_2253_ = l_Lean_LocalDecl_userName(v_val_2247_);
                v___x_2261_ = l_Lean_Name_hasMacroScopes(v___x_2253_);
                if v___x_2261_ == 0 {
                    v___x_2262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_fst_2248_, v___x_2253_);
                    if lean_obj_tag(v___x_2262_) == 1 {
                        v_val_2263_ = lean_ctor_get(v___x_2262_, 0);
                        lean_inc(v_val_2263_);
                        lean_dec_ref_known(v___x_2262_, 1);
                        v___x_2264_ = lean_array_push(v_snd_2249_, v_val_2263_);
                        v_toRename_2255_ = v___x_2264_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2262_);
                        v_toRename_2255_ = v_snd_2249_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2253_);
                    lean_del_object(v___x_2251_);
                    v___x_2265_ = l_Lean_LocalDecl_fvarId(v_val_2247_);
                    v___x_2266_ = lean_array_push(v_snd_2249_, v___x_2265_);
                    v___x_2267_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2267_, 0, v_fst_2248_);
                    lean_ctor_set(v___x_2267_, 1, v___x_2266_);
                    v_a_2239_ = v___x_2267_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2256_ = l_Lean_LocalDecl_fvarId(v_val_2247_);
                v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2248_, v___x_2253_, v___x_2256_);
                if v_isShared_2252_ == 0 {
                    lean_ctor_set(v___x_2251_, 1, v_toRename_2255_);
                    lean_ctor_set(v___x_2251_, 0, v___x_2257_);
                    v___x_2259_ = v___x_2251_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
                    lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_toRename_2255_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2239_ = v___x_2259_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9___boxed(
    mut v_as_2271_: *mut LeanObject,
    mut v_sz_2272_: *mut LeanObject,
    mut v_i_2273_: *mut LeanObject,
    mut v_b_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2280_: usize = 0;
    let mut v_i_boxed_2281_: usize = 0;
    let mut v_res_2282_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2280_ = lean_unbox_usize(v_sz_2272_);
    lean_dec(v_sz_2272_);
    v_i_boxed_2281_ = lean_unbox_usize(v_i_2273_);
    lean_dec(v_i_2273_);
    v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(v_as_2271_, v_sz_boxed_2280_, v_i_boxed_2281_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    lean_dec(v___y_2276_);
    lean_dec_ref(v___y_2275_);
    lean_dec_ref(v_as_2271_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(
    mut v_init_2283_: *mut LeanObject,
    mut v_n_2284_: *mut LeanObject,
    mut v_b_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v_fst_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_vs_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2323_: usize = 0;
    let mut v___x_2324_: usize = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v_fst_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_a_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_2284_) == 0 {
                    v_cs_2291_ = lean_ctor_get(v_n_2284_, 0);
                    v___x_2292_ = lean_box(0);
                    v___x_2293_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2293_, 0, v___x_2292_);
                    lean_ctor_set(v___x_2293_, 1, v_b_2285_);
                    v_sz_2294_ = lean_array_size(v_cs_2291_);
                    v___x_2295_ = 0usize;
                    v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8(v_init_2283_, v_cs_2291_, v_sz_2294_, v___x_2295_, v___x_2293_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
                    if lean_obj_tag(v___x_2296_) == 0 {
                        v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
                        v_isSharedCheck_2311_ = (!lean_is_exclusive(v___x_2296_)) as u8;
                        if v_isSharedCheck_2311_ == 0 {
                            v___x_2299_ = v___x_2296_;
                            v_isShared_2300_ = v_isSharedCheck_2311_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2297_);
                            lean_dec(v___x_2296_);
                            v___x_2299_ = lean_box(0);
                            v_isShared_2300_ = v_isSharedCheck_2311_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2312_ = lean_ctor_get(v___x_2296_, 0);
                        v_isSharedCheck_2319_ = (!lean_is_exclusive(v___x_2296_)) as u8;
                        if v_isSharedCheck_2319_ == 0 {
                            v___x_2314_ = v___x_2296_;
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2312_);
                            lean_dec(v___x_2296_);
                            v___x_2314_ = lean_box(0);
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2320_ = lean_ctor_get(v_n_2284_, 0);
                    v___x_2321_ = lean_box(0);
                    v___x_2322_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2322_, 0, v___x_2321_);
                    lean_ctor_set(v___x_2322_, 1, v_b_2285_);
                    v_sz_2323_ = lean_array_size(v_vs_2320_);
                    v___x_2324_ = 0usize;
                    v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(v_vs_2320_, v_sz_2323_, v___x_2324_, v___x_2322_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
                    if lean_obj_tag(v___x_2325_) == 0 {
                        v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
                        v_isSharedCheck_2340_ = (!lean_is_exclusive(v___x_2325_)) as u8;
                        if v_isSharedCheck_2340_ == 0 {
                            v___x_2328_ = v___x_2325_;
                            v_isShared_2329_ = v_isSharedCheck_2340_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2326_);
                            lean_dec(v___x_2325_);
                            v___x_2328_ = lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2340_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2341_ = lean_ctor_get(v___x_2325_, 0);
                        v_isSharedCheck_2348_ = (!lean_is_exclusive(v___x_2325_)) as u8;
                        if v_isSharedCheck_2348_ == 0 {
                            v___x_2343_ = v___x_2325_;
                            v_isShared_2344_ = v_isSharedCheck_2348_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2341_);
                            lean_dec(v___x_2325_);
                            v___x_2343_ = lean_box(0);
                            v_isShared_2344_ = v_isSharedCheck_2348_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2301_ = lean_ctor_get(v_a_2297_, 0);
                if lean_obj_tag(v_fst_2301_) == 0 {
                    v_snd_2302_ = lean_ctor_get(v_a_2297_, 1);
                    lean_inc(v_snd_2302_);
                    lean_dec(v_a_2297_);
                    v___x_2303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2303_, 0, v_snd_2302_);
                    if v_isShared_2300_ == 0 {
                        lean_ctor_set(v___x_2299_, 0, v___x_2303_);
                        v___x_2305_ = v___x_2299_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
                        v___x_2305_ = v_reuseFailAlloc_2306_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2301_);
                    lean_dec(v_a_2297_);
                    v_val_2307_ = lean_ctor_get(v_fst_2301_, 0);
                    lean_inc(v_val_2307_);
                    lean_dec_ref_known(v_fst_2301_, 1);
                    if v_isShared_2300_ == 0 {
                        lean_ctor_set(v___x_2299_, 0, v_val_2307_);
                        v___x_2309_ = v___x_2299_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_val_2307_);
                        v___x_2309_ = v_reuseFailAlloc_2310_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2305_;
            }
            3 => {
                return v___x_2309_;
            }
            4 => {
                if v_isShared_2315_ == 0 {
                    v___x_2317_ = v___x_2314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2317_;
            }
            6 => {
                v_fst_2330_ = lean_ctor_get(v_a_2326_, 0);
                if lean_obj_tag(v_fst_2330_) == 0 {
                    v_snd_2331_ = lean_ctor_get(v_a_2326_, 1);
                    lean_inc(v_snd_2331_);
                    lean_dec(v_a_2326_);
                    v___x_2332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2332_, 0, v_snd_2331_);
                    if v_isShared_2329_ == 0 {
                        lean_ctor_set(v___x_2328_, 0, v___x_2332_);
                        v___x_2334_ = v___x_2328_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
                        v___x_2334_ = v_reuseFailAlloc_2335_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2330_);
                    lean_dec(v_a_2326_);
                    v_val_2336_ = lean_ctor_get(v_fst_2330_, 0);
                    lean_inc(v_val_2336_);
                    lean_dec_ref_known(v_fst_2330_, 1);
                    if v_isShared_2329_ == 0 {
                        lean_ctor_set(v___x_2328_, 0, v_val_2336_);
                        v___x_2338_ = v___x_2328_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2336_);
                        v___x_2338_ = v_reuseFailAlloc_2339_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2334_;
            }
            8 => {
                return v___x_2338_;
            }
            9 => {
                if v_isShared_2344_ == 0 {
                    v___x_2346_ = v___x_2343_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
                    v___x_2346_ = v_reuseFailAlloc_2347_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8(
    mut v_init_2349_: *mut LeanObject,
    mut v_as_2350_: *mut LeanObject,
    mut v_sz_2351_: usize,
    mut v_i_2352_: usize,
    mut v_b_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_unused_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2359_ = lean_usize_dec_lt(v_i_2352_, v_sz_2351_);
                if v___x_2359_ == 0 {
                    v___x_2360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2360_, 0, v_b_2353_);
                    return v___x_2360_;
                } else {
                    v_snd_2361_ = lean_ctor_get(v_b_2353_, 1);
                    v_isSharedCheck_2395_ = (!lean_is_exclusive(v_b_2353_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v_unused_2396_ = lean_ctor_get(v_b_2353_, 0);
                        lean_dec(v_unused_2396_);
                        v___x_2363_ = v_b_2353_;
                        v_isShared_2364_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2361_);
                        lean_dec(v_b_2353_);
                        v___x_2363_ = lean_box(0);
                        v_isShared_2364_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2365_ = lean_array_uget_borrowed(v_as_2350_, v_i_2352_);
                lean_inc(v_snd_2361_);
                v___x_2366_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2349_, v_a_2365_, v_snd_2361_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
                if lean_obj_tag(v___x_2366_) == 0 {
                    v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
                    v_isSharedCheck_2386_ = (!lean_is_exclusive(v___x_2366_)) as u8;
                    if v_isSharedCheck_2386_ == 0 {
                        v___x_2369_ = v___x_2366_;
                        v_isShared_2370_ = v_isSharedCheck_2386_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2367_);
                        lean_dec(v___x_2366_);
                        v___x_2369_ = lean_box(0);
                        v_isShared_2370_ = v_isSharedCheck_2386_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2363_);
                    lean_dec(v_snd_2361_);
                    v_a_2387_ = lean_ctor_get(v___x_2366_, 0);
                    v_isSharedCheck_2394_ = (!lean_is_exclusive(v___x_2366_)) as u8;
                    if v_isSharedCheck_2394_ == 0 {
                        v___x_2389_ = v___x_2366_;
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2387_);
                        lean_dec(v___x_2366_);
                        v___x_2389_ = lean_box(0);
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2367_) == 0 {
                    v___x_2371_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2371_, 0, v_a_2367_);
                    if v_isShared_2364_ == 0 {
                        lean_ctor_set(v___x_2363_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2363_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2371_);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2361_);
                        v___x_2373_ = v_reuseFailAlloc_2377_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2369_);
                    lean_dec(v_snd_2361_);
                    v_a_2378_ = lean_ctor_get(v_a_2367_, 0);
                    lean_inc(v_a_2378_);
                    lean_dec_ref_known(v_a_2367_, 1);
                    v___x_2379_ = lean_box(0);
                    if v_isShared_2364_ == 0 {
                        lean_ctor_set(v___x_2363_, 1, v_a_2378_);
                        lean_ctor_set(v___x_2363_, 0, v___x_2379_);
                        v___x_2381_ = v___x_2363_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2379_);
                        lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2378_);
                        v___x_2381_ = v_reuseFailAlloc_2385_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2370_ == 0 {
                    lean_ctor_set(v___x_2369_, 0, v___x_2373_);
                    v___x_2375_ = v___x_2369_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
                    v___x_2375_ = v_reuseFailAlloc_2376_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2375_;
            }
            5 => {
                v___x_2382_ = 1usize;
                v___x_2383_ = lean_usize_add(v_i_2352_, v___x_2382_);
                v_i_2352_ = v___x_2383_;
                v_b_2353_ = v___x_2381_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2390_ == 0 {
                    v___x_2392_ = v___x_2389_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8___boxed(
    mut v_init_2397_: *mut LeanObject,
    mut v_as_2398_: *mut LeanObject,
    mut v_sz_2399_: *mut LeanObject,
    mut v_i_2400_: *mut LeanObject,
    mut v_b_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2407_: usize = 0;
    let mut v_i_boxed_2408_: usize = 0;
    let mut v_res_2409_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2399_);
    lean_dec(v_sz_2399_);
    v_i_boxed_2408_ = lean_unbox_usize(v_i_2400_);
    lean_dec(v_i_2400_);
    v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8(v_init_2397_, v_as_2398_, v_sz_boxed_2407_, v_i_boxed_2408_, v_b_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    lean_dec(v___y_2405_);
    lean_dec_ref(v___y_2404_);
    lean_dec(v___y_2403_);
    lean_dec_ref(v___y_2402_);
    lean_dec_ref(v_as_2398_);
    lean_dec_ref(v_init_2397_);
    return v_res_2409_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6___boxed(
    mut v_init_2410_: *mut LeanObject,
    mut v_n_2411_: *mut LeanObject,
    mut v_b_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2410_, v_n_2411_, v_b_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    lean_dec(v___y_2416_);
    lean_dec_ref(v___y_2415_);
    lean_dec(v___y_2414_);
    lean_dec_ref(v___y_2413_);
    lean_dec_ref(v_n_2411_);
    lean_dec_ref(v_init_2410_);
    return v_res_2418_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(
    mut v_t_2419_: *mut LeanObject,
    mut v_init_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v_a_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v_fst_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_a_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_a_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2426_ = lean_ctor_get(v_t_2419_, 0);
                v_tail_2427_ = lean_ctor_get(v_t_2419_, 1);
                lean_inc_ref(v_init_2420_);
                v___x_2428_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2420_, v_root_2426_, v_init_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
                lean_dec_ref(v_init_2420_);
                if lean_obj_tag(v___x_2428_) == 0 {
                    v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
                    v_isSharedCheck_2465_ = (!lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2465_ == 0 {
                        v___x_2431_ = v___x_2428_;
                        v_isShared_2432_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2429_);
                        lean_dec(v___x_2428_);
                        v___x_2431_ = lean_box(0);
                        v_isShared_2432_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2466_ = lean_ctor_get(v___x_2428_, 0);
                    v_isSharedCheck_2473_ = (!lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2473_ == 0 {
                        v___x_2468_ = v___x_2428_;
                        v_isShared_2469_ = v_isSharedCheck_2473_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2466_);
                        lean_dec(v___x_2428_);
                        v___x_2468_ = lean_box(0);
                        v_isShared_2469_ = v_isSharedCheck_2473_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2429_) == 0 {
                    v_a_2433_ = lean_ctor_get(v_a_2429_, 0);
                    lean_inc(v_a_2433_);
                    lean_dec_ref_known(v_a_2429_, 1);
                    if v_isShared_2432_ == 0 {
                        lean_ctor_set(v___x_2431_, 0, v_a_2433_);
                        v___x_2435_ = v___x_2431_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2433_);
                        v___x_2435_ = v_reuseFailAlloc_2436_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2431_);
                    v_a_2437_ = lean_ctor_get(v_a_2429_, 0);
                    lean_inc(v_a_2437_);
                    lean_dec_ref_known(v_a_2429_, 1);
                    v___x_2438_ = lean_box(0);
                    v___x_2439_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                    lean_ctor_set(v___x_2439_, 1, v_a_2437_);
                    v_sz_2440_ = lean_array_size(v_tail_2427_);
                    v___x_2441_ = 0usize;
                    v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(v_tail_2427_, v_sz_2440_, v___x_2441_, v___x_2439_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
                    if lean_obj_tag(v___x_2442_) == 0 {
                        v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
                        v_isSharedCheck_2456_ = (!lean_is_exclusive(v___x_2442_)) as u8;
                        if v_isSharedCheck_2456_ == 0 {
                            v___x_2445_ = v___x_2442_;
                            v_isShared_2446_ = v_isSharedCheck_2456_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2443_);
                            lean_dec(v___x_2442_);
                            v___x_2445_ = lean_box(0);
                            v_isShared_2446_ = v_isSharedCheck_2456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2457_ = lean_ctor_get(v___x_2442_, 0);
                        v_isSharedCheck_2464_ = (!lean_is_exclusive(v___x_2442_)) as u8;
                        if v_isSharedCheck_2464_ == 0 {
                            v___x_2459_ = v___x_2442_;
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2457_);
                            lean_dec(v___x_2442_);
                            v___x_2459_ = lean_box(0);
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2435_;
            }
            3 => {
                v_fst_2447_ = lean_ctor_get(v_a_2443_, 0);
                if lean_obj_tag(v_fst_2447_) == 0 {
                    v_snd_2448_ = lean_ctor_get(v_a_2443_, 1);
                    lean_inc(v_snd_2448_);
                    lean_dec(v_a_2443_);
                    if v_isShared_2446_ == 0 {
                        lean_ctor_set(v___x_2445_, 0, v_snd_2448_);
                        v___x_2450_ = v___x_2445_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_snd_2448_);
                        v___x_2450_ = v_reuseFailAlloc_2451_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2447_);
                    lean_dec(v_a_2443_);
                    v_val_2452_ = lean_ctor_get(v_fst_2447_, 0);
                    lean_inc(v_val_2452_);
                    lean_dec_ref_known(v_fst_2447_, 1);
                    if v_isShared_2446_ == 0 {
                        lean_ctor_set(v___x_2445_, 0, v_val_2452_);
                        v___x_2454_ = v___x_2445_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_val_2452_);
                        v___x_2454_ = v_reuseFailAlloc_2455_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2450_;
            }
            5 => {
                return v___x_2454_;
            }
            6 => {
                if v_isShared_2460_ == 0 {
                    v___x_2462_ = v___x_2459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
                    v___x_2462_ = v_reuseFailAlloc_2463_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2462_;
            }
            8 => {
                if v_isShared_2469_ == 0 {
                    v___x_2471_ = v___x_2468_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
                    v___x_2471_ = v_reuseFailAlloc_2472_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2___boxed(
    mut v_t_2474_: *mut LeanObject,
    mut v_init_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(v_t_2474_, v_init_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
    lean_dec(v___y_2479_);
    lean_dec_ref(v___y_2478_);
    lean_dec(v___y_2477_);
    lean_dec_ref(v___y_2476_);
    lean_dec_ref(v_t_2474_);
    return v_res_2481_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(
    mut v___x_2482_: *mut LeanObject,
    mut v_fvarId_u2081_2483_: *mut LeanObject,
    mut v_fvarId_u2082_2484_: *mut LeanObject,
) -> u8 {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    lean_inc_ref(v___x_2482_);
    v___x_2485_ = l_Lean_LocalContext_get_x21(v___x_2482_, v_fvarId_u2081_2483_);
    v___x_2486_ = l_Lean_LocalDecl_index(v___x_2485_);
    lean_dec_ref(v___x_2485_);
    v___x_2487_ = l_Lean_LocalContext_get_x21(v___x_2482_, v_fvarId_u2082_2484_);
    v___x_2488_ = l_Lean_LocalDecl_index(v___x_2487_);
    lean_dec_ref(v___x_2487_);
    v___x_2489_ = lean_nat_dec_lt(v___x_2486_, v___x_2488_);
    lean_dec(v___x_2488_);
    lean_dec(v___x_2486_);
    return v___x_2489_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0___boxed(
    mut v___x_2490_: *mut LeanObject,
    mut v_fvarId_u2081_2491_: *mut LeanObject,
    mut v_fvarId_u2082_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: u8 = 0;
    let mut v_r_2494_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2490_, v_fvarId_u2081_2491_, v_fvarId_u2082_2492_);
    v_r_2494_ = lean_box((v_res_2493_) as usize);
    return v_r_2494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(
    mut v___x_2495_: *mut LeanObject,
    mut v_hi_2496_: *mut LeanObject,
    mut v_pivot_2497_: *mut LeanObject,
    mut v_as_2498_: *mut LeanObject,
    mut v_i_2499_: *mut LeanObject,
    mut v_k_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_nat_dec_lt(v_k_2500_, v_hi_2496_);
                if v___x_2501_ == 0 {
                    lean_dec(v_k_2500_);
                    lean_dec(v_pivot_2497_);
                    lean_dec_ref(v___x_2495_);
                    v___x_2502_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_hi_2496_);
                    v___x_2503_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2503_, 0, v_i_2499_);
                    lean_ctor_set(v___x_2503_, 1, v___x_2502_);
                    return v___x_2503_;
                } else {
                    v___x_2504_ = lean_array_fget_borrowed(v_as_2498_, v_k_2500_);
                    lean_inc(v___x_2504_);
                    lean_inc_ref_n(v___x_2495_, 2);
                    v___x_2505_ = l_Lean_LocalContext_get_x21(v___x_2495_, v___x_2504_);
                    v___x_2506_ = l_Lean_LocalDecl_index(v___x_2505_);
                    lean_dec_ref(v___x_2505_);
                    lean_inc(v_pivot_2497_);
                    v___x_2507_ = l_Lean_LocalContext_get_x21(v___x_2495_, v_pivot_2497_);
                    v___x_2508_ = l_Lean_LocalDecl_index(v___x_2507_);
                    lean_dec_ref(v___x_2507_);
                    v___x_2509_ = lean_nat_dec_lt(v___x_2506_, v___x_2508_);
                    lean_dec(v___x_2508_);
                    lean_dec(v___x_2506_);
                    if v___x_2509_ == 0 {
                        v___x_2510_ = lean_unsigned_to_nat(1);
                        v___x_2511_ = lean_nat_add(v_k_2500_, v___x_2510_);
                        lean_dec(v_k_2500_);
                        v_k_2500_ = v___x_2511_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2513_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_k_2500_);
                        v___x_2514_ = lean_unsigned_to_nat(1);
                        v___x_2515_ = lean_nat_add(v_i_2499_, v___x_2514_);
                        lean_dec(v_i_2499_);
                        v___x_2516_ = lean_nat_add(v_k_2500_, v___x_2514_);
                        lean_dec(v_k_2500_);
                        v_as_2498_ = v___x_2513_;
                        v_i_2499_ = v___x_2515_;
                        v_k_2500_ = v___x_2516_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg___boxed(
    mut v___x_2518_: *mut LeanObject,
    mut v_hi_2519_: *mut LeanObject,
    mut v_pivot_2520_: *mut LeanObject,
    mut v_as_2521_: *mut LeanObject,
    mut v_i_2522_: *mut LeanObject,
    mut v_k_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2524_: *mut LeanObject = core::ptr::null_mut();
    v_res_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_2518_, v_hi_2519_, v_pivot_2520_, v_as_2521_, v_i_2522_, v_k_2523_);
    lean_dec(v_hi_2519_);
    return v_res_2524_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(
    mut v___x_2525_: *mut LeanObject,
    mut v_n_2526_: *mut LeanObject,
    mut v_as_2527_: *mut LeanObject,
    mut v_lo_2528_: *mut LeanObject,
    mut v_hi_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2541_ = lean_nat_dec_lt(v_lo_2528_, v_hi_2529_);
                if v___x_2541_ == 0 {
                    lean_dec(v_lo_2528_);
                    lean_dec_ref(v___x_2525_);
                    return v_as_2527_;
                } else {
                    v___x_2542_ = lean_nat_add(v_lo_2528_, v_hi_2529_);
                    v___x_2543_ = lean_unsigned_to_nat(1);
                    v_mid_2544_ = lean_nat_shiftr(v___x_2542_, v___x_2543_);
                    lean_dec(v___x_2542_);
                    v___x_2557_ = lean_array_fget_borrowed(v_as_2527_, v_mid_2544_);
                    v___x_2558_ = lean_array_fget_borrowed(v_as_2527_, v_lo_2528_);
                    lean_inc(v___x_2558_);
                    lean_inc(v___x_2557_);
                    lean_inc_ref(v___x_2525_);
                    v___x_2559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2525_, v___x_2557_, v___x_2558_);
                    if v___x_2559_ == 0 {
                        v___y_2552_ = v_as_2527_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2560_ = lean_array_fswap(v_as_2527_, v_lo_2528_, v_mid_2544_);
                        v___y_2552_ = v___x_2560_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2532_ = lean_array_fget(v___y_2531_, v_hi_2529_);
                lean_inc_n(v_lo_2528_, 2);
                lean_inc_ref(v___x_2525_);
                v___x_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_2525_, v_hi_2529_, v_pivot_2532_, v___y_2531_, v_lo_2528_, v_lo_2528_);
                v_fst_2534_ = lean_ctor_get(v___x_2533_, 0);
                lean_inc(v_fst_2534_);
                v_snd_2535_ = lean_ctor_get(v___x_2533_, 1);
                lean_inc(v_snd_2535_);
                lean_dec_ref(v___x_2533_);
                v___x_2536_ = lean_nat_dec_le(v_hi_2529_, v_fst_2534_);
                if v___x_2536_ == 0 {
                    lean_inc_ref(v___x_2525_);
                    v___x_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_2525_, v_n_2526_, v_snd_2535_, v_lo_2528_, v_fst_2534_);
                    v___x_2538_ = lean_unsigned_to_nat(1);
                    v___x_2539_ = lean_nat_add(v_fst_2534_, v___x_2538_);
                    lean_dec(v_fst_2534_);
                    v_as_2527_ = v___x_2537_;
                    v_lo_2528_ = v___x_2539_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2534_);
                    lean_dec(v_lo_2528_);
                    lean_dec_ref(v___x_2525_);
                    return v_snd_2535_;
                }
            }
            2 => {
                v___x_2547_ = lean_array_fget_borrowed(v___y_2546_, v_mid_2544_);
                v___x_2548_ = lean_array_fget_borrowed(v___y_2546_, v_hi_2529_);
                lean_inc(v___x_2548_);
                lean_inc(v___x_2547_);
                lean_inc_ref(v___x_2525_);
                v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2525_, v___x_2547_, v___x_2548_);
                if v___x_2549_ == 0 {
                    lean_dec(v_mid_2544_);
                    v___y_2531_ = v___y_2546_;
                    state = 1;
                    continue;
                } else {
                    v___x_2550_ = lean_array_fswap(v___y_2546_, v_mid_2544_, v_hi_2529_);
                    lean_dec(v_mid_2544_);
                    v___y_2531_ = v___x_2550_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2553_ = lean_array_fget_borrowed(v___y_2552_, v_hi_2529_);
                v___x_2554_ = lean_array_fget_borrowed(v___y_2552_, v_lo_2528_);
                lean_inc(v___x_2554_);
                lean_inc(v___x_2553_);
                lean_inc_ref(v___x_2525_);
                v___x_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2525_, v___x_2553_, v___x_2554_);
                if v___x_2555_ == 0 {
                    v___y_2546_ = v___y_2552_;
                    state = 2;
                    continue;
                } else {
                    v___x_2556_ = lean_array_fswap(v___y_2552_, v_lo_2528_, v_hi_2529_);
                    v___y_2546_ = v___x_2556_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___boxed(
    mut v___x_2561_: *mut LeanObject,
    mut v_n_2562_: *mut LeanObject,
    mut v_as_2563_: *mut LeanObject,
    mut v_lo_2564_: *mut LeanObject,
    mut v_hi_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2566_: *mut LeanObject = core::ptr::null_mut();
    v_res_2566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_2561_, v_n_2562_, v_as_2563_, v_lo_2564_, v_hi_2565_);
    lean_dec(v_hi_2565_);
    lean_dec(v_n_2562_);
    return v_res_2566_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(
    mut v_m_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2572_: u64 = 0;
    let mut v___x_2573_: u64 = 0;
    let mut v___x_2574_: u64 = 0;
    let mut v_fold_2575_: u64 = 0;
    let mut v___x_2576_: u64 = 0;
    let mut v___x_2577_: u64 = 0;
    let mut v___x_2578_: u64 = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: usize = 0;
    let mut v___x_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u64 = 0;
    let mut v_hash_2587_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2569_ = lean_ctor_get(v_m_2567_, 1);
                v___x_2570_ = lean_array_get_size(v_buckets_2569_);
                if lean_obj_tag(v_a_2568_) == 0 {
                    v___x_2586_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_2572_ = v___x_2586_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2587_ = lean_ctor_get_uint64(
                        v_a_2568_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2572_ = v_hash_2587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2573_ = 32u64;
                v___x_2574_ = lean_uint64_shift_right(v___y_2572_, v___x_2573_);
                v_fold_2575_ = lean_uint64_xor(v___y_2572_, v___x_2574_);
                v___x_2576_ = 16u64;
                v___x_2577_ = lean_uint64_shift_right(v_fold_2575_, v___x_2576_);
                v___x_2578_ = lean_uint64_xor(v_fold_2575_, v___x_2577_);
                v___x_2579_ = lean_uint64_to_usize(v___x_2578_);
                v___x_2580_ = lean_usize_of_nat(v___x_2570_);
                v___x_2581_ = 1usize;
                v___x_2582_ = lean_usize_sub(v___x_2580_, v___x_2581_);
                v___x_2583_ = lean_usize_land(v___x_2579_, v___x_2582_);
                v___x_2584_ = lean_array_uget_borrowed(v_buckets_2569_, v___x_2583_);
                v___x_2585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_2568_, v___x_2584_);
                return v___x_2585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg___boxed(
    mut v_m_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2590_: u8 = 0;
    let mut v_r_2591_: *mut LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v_m_2588_, v_a_2589_);
    lean_dec(v_a_2589_);
    lean_dec_ref(v_m_2588_);
    v_r_2591_ = lean_box((v_res_2590_) as usize);
    return v_r_2591_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(
    mut v___x_2592_: *mut LeanObject,
    mut v___x_2593_: *mut LeanObject,
    mut v_baseName_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2597_ = lean_ctor_get(v_a_2595_, 0);
                v_snd_2598_ = lean_ctor_get(v_a_2595_, 1);
                v_isSharedCheck_2615_ = (!lean_is_exclusive(v_a_2595_)) as u8;
                if v_isSharedCheck_2615_ == 0 {
                    v___x_2600_ = v_a_2595_;
                    v_isShared_2601_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2598_);
                    lean_inc(v_fst_2597_);
                    lean_dec(v_a_2595_);
                    v___x_2600_ = lean_box(0);
                    v_isShared_2601_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v___x_2592_, v_fst_2597_);
                if v___x_2607_ == 0 {
                    lean_dec(v_baseName_2594_);
                    state = 2;
                    continue;
                } else {
                    v___x_2608_ = lean_unsigned_to_nat(0);
                    v___x_2609_ = lean_nat_dec_eq(v___x_2593_, v___x_2608_);
                    if v___x_2609_ == 0 {
                        lean_del_object(v___x_2600_);
                        lean_dec(v_fst_2597_);
                        v___x_2610_ = lean_unsigned_to_nat(1);
                        v___x_2611_ = lean_nat_add(v_snd_2598_, v___x_2610_);
                        lean_dec(v_snd_2598_);
                        lean_inc(v___x_2611_);
                        lean_inc(v_baseName_2594_);
                        v___x_2612_ = lean_name_append_index_after(v_baseName_2594_, v___x_2611_);
                        v___x_2613_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                        lean_ctor_set(v___x_2613_, 1, v___x_2611_);
                        v_a_2595_ = v___x_2613_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_baseName_2594_);
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2601_ == 0 {
                    v___x_2604_ = v___x_2600_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_fst_2597_);
                    lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_snd_2598_);
                    v___x_2604_ = v_reuseFailAlloc_2606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2605_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2605_, 0, v___x_2604_);
                return v___x_2605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg___boxed(
    mut v___x_2616_: *mut LeanObject,
    mut v___x_2617_: *mut LeanObject,
    mut v_baseName_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2621_: *mut LeanObject = core::ptr::null_mut();
    v_res_2621_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v___x_2616_, v___x_2617_, v_baseName_2618_, v_a_2619_);
    lean_dec(v___x_2617_);
    lean_dec_ref(v___x_2616_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21___redArg(
    mut v_x_2622_: *mut LeanObject,
    mut v_x_2623_: *mut LeanObject,
    mut v_x_2624_: *mut LeanObject,
    mut v_x_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2626_ = lean_ctor_get(v_x_2622_, 0);
                v_vs_2627_ = lean_ctor_get(v_x_2622_, 1);
                v_isSharedCheck_2651_ = (!lean_is_exclusive(v_x_2622_)) as u8;
                if v_isSharedCheck_2651_ == 0 {
                    v___x_2629_ = v_x_2622_;
                    v_isShared_2630_ = v_isSharedCheck_2651_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2627_);
                    lean_inc(v_ks_2626_);
                    lean_dec(v_x_2622_);
                    v___x_2629_ = lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2631_ = lean_array_get_size(v_ks_2626_);
                v___x_2632_ = lean_nat_dec_lt(v_x_2623_, v___x_2631_);
                if v___x_2632_ == 0 {
                    lean_dec(v_x_2623_);
                    v___x_2633_ = lean_array_push(v_ks_2626_, v_x_2624_);
                    v___x_2634_ = lean_array_push(v_vs_2627_, v_x_2625_);
                    if v_isShared_2630_ == 0 {
                        lean_ctor_set(v___x_2629_, 1, v___x_2634_);
                        lean_ctor_set(v___x_2629_, 0, v___x_2633_);
                        v___x_2636_ = v___x_2629_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2633_);
                        lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2634_);
                        v___x_2636_ = v_reuseFailAlloc_2637_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2638_ = lean_array_fget_borrowed(v_ks_2626_, v_x_2623_);
                    v___x_2639_ = l_Lean_instBEqFVarId_beq(v_x_2624_, v_k_x27_2638_);
                    if v___x_2639_ == 0 {
                        if v_isShared_2630_ == 0 {
                            v___x_2641_ = v___x_2629_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_ks_2626_);
                            lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_vs_2627_);
                            v___x_2641_ = v_reuseFailAlloc_2645_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2646_ = lean_array_fset(v_ks_2626_, v_x_2623_, v_x_2624_);
                        v___x_2647_ = lean_array_fset(v_vs_2627_, v_x_2623_, v_x_2625_);
                        lean_dec(v_x_2623_);
                        if v_isShared_2630_ == 0 {
                            lean_ctor_set(v___x_2629_, 1, v___x_2647_);
                            lean_ctor_set(v___x_2629_, 0, v___x_2646_);
                            v___x_2649_ = v___x_2629_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2646_);
                            lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2647_);
                            v___x_2649_ = v_reuseFailAlloc_2650_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2636_;
            }
            3 => {
                v___x_2642_ = lean_unsigned_to_nat(1);
                v___x_2643_ = lean_nat_add(v_x_2623_, v___x_2642_);
                lean_dec(v_x_2623_);
                v_x_2622_ = v___x_2641_;
                v_x_2623_ = v___x_2643_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16___redArg(
    mut v_n_2652_: *mut LeanObject,
    mut v_k_2653_: *mut LeanObject,
    mut v_v_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = lean_unsigned_to_nat(0);
    v___x_2656_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21___redArg(v_n_2652_, v___x_2655_, v_k_2653_, v_v_2654_);
    return v___x_2656_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0()
-> usize {
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    v___x_2657_ = 5usize;
    v___x_2658_ = 1usize;
    v___x_2659_ = lean_usize_shift_left(v___x_2658_, v___x_2657_);
    return v___x_2659_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1()
-> usize {
    let mut v___x_2660_: usize = 0;
    let mut v___x_2661_: usize = 0;
    let mut v___x_2662_: usize = 0;
    v___x_2660_ = 1usize;
    v___x_2661_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0);
    v___x_2662_ = lean_usize_sub(v___x_2661_, v___x_2660_);
    return v___x_2662_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2663_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(
    mut v_x_2664_: *mut LeanObject,
    mut v_x_2665_: usize,
    mut v_x_2666_: usize,
    mut v_x_2667_: *mut LeanObject,
    mut v_x_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: usize = 0;
    let mut v___x_2672_: usize = 0;
    let mut v___x_2673_: usize = 0;
    let mut v_j_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_v_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_node_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_unused_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: u8 = 0;
    let mut v_ks_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: usize = 0;
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v_reuseFailAlloc_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2664_) == 0 {
                    v_es_2669_ = lean_ctor_get(v_x_2664_, 0);
                    v___x_2670_ = 5usize;
                    v___x_2671_ = 1usize;
                    v___x_2672_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1);
                    v___x_2673_ = lean_usize_land(v_x_2665_, v___x_2672_);
                    v_j_2674_ = lean_usize_to_nat(v___x_2673_);
                    v___x_2675_ = lean_array_get_size(v_es_2669_);
                    v___x_2676_ = lean_nat_dec_lt(v_j_2674_, v___x_2675_);
                    if v___x_2676_ == 0 {
                        lean_dec(v_j_2674_);
                        lean_dec(v_x_2668_);
                        lean_dec(v_x_2667_);
                        return v_x_2664_;
                    } else {
                        lean_inc_ref(v_es_2669_);
                        v_isSharedCheck_2713_ = (!lean_is_exclusive(v_x_2664_)) as u8;
                        if v_isSharedCheck_2713_ == 0 {
                            v_unused_2714_ = lean_ctor_get(v_x_2664_, 0);
                            lean_dec(v_unused_2714_);
                            v___x_2678_ = v_x_2664_;
                            v_isShared_2679_ = v_isSharedCheck_2713_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2664_);
                            v___x_2678_ = lean_box(0);
                            v_isShared_2679_ = v_isSharedCheck_2713_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2715_ = lean_ctor_get(v_x_2664_, 0);
                    v_vs_2716_ = lean_ctor_get(v_x_2664_, 1);
                    v_isSharedCheck_2736_ = (!lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2736_ == 0 {
                        v___x_2718_ = v_x_2664_;
                        v_isShared_2719_ = v_isSharedCheck_2736_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2716_);
                        lean_inc(v_ks_2715_);
                        lean_dec(v_x_2664_);
                        v___x_2718_ = lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2736_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2680_ = lean_array_fget(v_es_2669_, v_j_2674_);
                v___x_2681_ = lean_box(0);
                v_xs_x27_2682_ = lean_array_fset(v_es_2669_, v_j_2674_, v___x_2681_);
                match lean_obj_tag(v_v_2680_) {
                    0 => {
                        v_key_2689_ = lean_ctor_get(v_v_2680_, 0);
                        v_val_2690_ = lean_ctor_get(v_v_2680_, 1);
                        v_isSharedCheck_2700_ = (!lean_is_exclusive(v_v_2680_)) as u8;
                        if v_isSharedCheck_2700_ == 0 {
                            v___x_2692_ = v_v_2680_;
                            v_isShared_2693_ = v_isSharedCheck_2700_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2690_);
                            lean_inc(v_key_2689_);
                            lean_dec(v_v_2680_);
                            v___x_2692_ = lean_box(0);
                            v_isShared_2693_ = v_isSharedCheck_2700_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2701_ = lean_ctor_get(v_v_2680_, 0);
                        v_isSharedCheck_2711_ = (!lean_is_exclusive(v_v_2680_)) as u8;
                        if v_isSharedCheck_2711_ == 0 {
                            v___x_2703_ = v_v_2680_;
                            v_isShared_2704_ = v_isSharedCheck_2711_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2701_);
                            lean_dec(v_v_2680_);
                            v___x_2703_ = lean_box(0);
                            v_isShared_2704_ = v_isSharedCheck_2711_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2712_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2712_, 0, v_x_2667_);
                        lean_ctor_set(v___x_2712_, 1, v_x_2668_);
                        v___y_2684_ = v___x_2712_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = lean_array_fset(v_xs_x27_2682_, v_j_2674_, v___y_2684_);
                lean_dec(v_j_2674_);
                if v_isShared_2679_ == 0 {
                    lean_ctor_set(v___x_2678_, 0, v___x_2685_);
                    v___x_2687_ = v___x_2678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
                    v___x_2687_ = v_reuseFailAlloc_2688_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2687_;
            }
            4 => {
                v___x_2694_ = l_Lean_instBEqFVarId_beq(v_x_2667_, v_key_2689_);
                if v___x_2694_ == 0 {
                    lean_del_object(v___x_2692_);
                    v___x_2695_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2689_,
                        v_val_2690_,
                        v_x_2667_,
                        v_x_2668_,
                    );
                    v___x_2696_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2696_, 0, v___x_2695_);
                    v___y_2684_ = v___x_2696_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2690_);
                    lean_dec(v_key_2689_);
                    if v_isShared_2693_ == 0 {
                        lean_ctor_set(v___x_2692_, 1, v_x_2668_);
                        lean_ctor_set(v___x_2692_, 0, v_x_2667_);
                        v___x_2698_ = v___x_2692_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_x_2667_);
                        lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_x_2668_);
                        v___x_2698_ = v_reuseFailAlloc_2699_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2684_ = v___x_2698_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2705_ = lean_usize_shift_right(v_x_2665_, v___x_2670_);
                v___x_2706_ = lean_usize_add(v_x_2666_, v___x_2671_);
                v___x_2707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_node_2701_, v___x_2705_, v___x_2706_, v_x_2667_, v_x_2668_);
                if v_isShared_2704_ == 0 {
                    lean_ctor_set(v___x_2703_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2703_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2684_ = v___x_2709_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2719_ == 0 {
                    v___x_2721_ = v___x_2718_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_ks_2715_);
                    lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_vs_2716_);
                    v___x_2721_ = v_reuseFailAlloc_2735_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2722_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16___redArg(v___x_2721_, v_x_2667_, v_x_2668_);
                v___x_2730_ = 7usize;
                v___x_2731_ = lean_usize_dec_le(v___x_2730_, v_x_2666_);
                if v___x_2731_ == 0 {
                    v___x_2732_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2722_);
                    v___x_2733_ = lean_unsigned_to_nat(4);
                    v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
                    lean_dec(v___x_2732_);
                    v___y_2724_ = v___x_2734_;
                    state = 10;
                    continue;
                } else {
                    v___y_2724_ = v___x_2731_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2724_ == 0 {
                    v_ks_2725_ = lean_ctor_get(v_newNode_2722_, 0);
                    lean_inc_ref(v_ks_2725_);
                    v_vs_2726_ = lean_ctor_get(v_newNode_2722_, 1);
                    lean_inc_ref(v_vs_2726_);
                    lean_dec_ref(v_newNode_2722_);
                    v___x_2727_ = lean_unsigned_to_nat(0);
                    v___x_2728_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2);
                    v___x_2729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_x_2666_, v_ks_2725_, v_vs_2726_, v___x_2727_, v___x_2728_);
                    lean_dec_ref(v_vs_2726_);
                    lean_dec_ref(v_ks_2725_);
                    return v___x_2729_;
                } else {
                    return v_newNode_2722_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(
    mut v_depth_2737_: usize,
    mut v_keys_2738_: *mut LeanObject,
    mut v_vals_2739_: *mut LeanObject,
    mut v_i_2740_: *mut LeanObject,
    mut v_entries_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v_k_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u64 = 0;
    let mut v_h_2747_: usize = 0;
    let mut v___x_2748_: usize = 0;
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: usize = 0;
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v_h_2753_: usize = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2742_ = lean_array_get_size(v_keys_2738_);
                v___x_2743_ = lean_nat_dec_lt(v_i_2740_, v___x_2742_);
                if v___x_2743_ == 0 {
                    lean_dec(v_i_2740_);
                    return v_entries_2741_;
                } else {
                    v_k_2744_ = lean_array_fget_borrowed(v_keys_2738_, v_i_2740_);
                    v_v_2745_ = lean_array_fget_borrowed(v_vals_2739_, v_i_2740_);
                    v___x_2746_ = l_Lean_instHashableFVarId_hash(v_k_2744_);
                    v_h_2747_ = lean_uint64_to_usize(v___x_2746_);
                    v___x_2748_ = 5usize;
                    v___x_2749_ = lean_unsigned_to_nat(1);
                    v___x_2750_ = 1usize;
                    v___x_2751_ = lean_usize_sub(v_depth_2737_, v___x_2750_);
                    v___x_2752_ = lean_usize_mul(v___x_2748_, v___x_2751_);
                    v_h_2753_ = lean_usize_shift_right(v_h_2747_, v___x_2752_);
                    v___x_2754_ = lean_nat_add(v_i_2740_, v___x_2749_);
                    lean_dec(v_i_2740_);
                    lean_inc(v_v_2745_);
                    lean_inc(v_k_2744_);
                    v___x_2755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_entries_2741_, v_h_2753_, v_depth_2737_, v_k_2744_, v_v_2745_);
                    v_i_2740_ = v___x_2754_;
                    v_entries_2741_ = v___x_2755_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg___boxed(
    mut v_depth_2757_: *mut LeanObject,
    mut v_keys_2758_: *mut LeanObject,
    mut v_vals_2759_: *mut LeanObject,
    mut v_i_2760_: *mut LeanObject,
    mut v_entries_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2762_: usize = 0;
    let mut v_res_2763_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2762_ = lean_unbox_usize(v_depth_2757_);
    lean_dec(v_depth_2757_);
    v_res_2763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_depth_boxed_2762_, v_keys_2758_, v_vals_2759_, v_i_2760_, v_entries_2761_);
    lean_dec_ref(v_vals_2759_);
    lean_dec_ref(v_keys_2758_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___boxed(
    mut v_x_2764_: *mut LeanObject,
    mut v_x_2765_: *mut LeanObject,
    mut v_x_2766_: *mut LeanObject,
    mut v_x_2767_: *mut LeanObject,
    mut v_x_2768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10581__boxed_2769_: usize = 0;
    let mut v_x_10582__boxed_2770_: usize = 0;
    let mut v_res_2771_: *mut LeanObject = core::ptr::null_mut();
    v_x_10581__boxed_2769_ = lean_unbox_usize(v_x_2765_);
    lean_dec(v_x_2765_);
    v_x_10582__boxed_2770_ = lean_unbox_usize(v_x_2766_);
    lean_dec(v_x_2766_);
    v_res_2771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_2764_, v_x_10581__boxed_2769_, v_x_10582__boxed_2770_, v_x_2767_, v_x_2768_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(
    mut v_x_2772_: *mut LeanObject,
    mut v_x_2773_: *mut LeanObject,
    mut v_x_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2775_: u64 = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: usize = 0;
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2775_ = l_Lean_instHashableFVarId_hash(v_x_2773_);
    v___x_2776_ = lean_uint64_to_usize(v___x_2775_);
    v___x_2777_ = 1usize;
    v___x_2778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_2772_, v___x_2776_, v___x_2777_, v_x_2773_, v_x_2774_);
    return v___x_2778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(
    mut v___x_2788_: *mut LeanObject,
    mut v_as_2789_: *mut LeanObject,
    mut v_sz_2790_: usize,
    mut v_i_2791_: usize,
    mut v_b_2792_: *mut LeanObject,
    mut v___y_2793_: *mut LeanObject,
    mut v___y_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: usize = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___y_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_reuseFailAlloc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2828_ = lean_usize_dec_lt(v_i_2791_, v_sz_2790_);
                if v___x_2828_ == 0 {
                    v___x_2829_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2829_, 0, v_b_2792_);
                    return v___x_2829_;
                } else {
                    v_snd_2830_ = lean_ctor_get(v_b_2792_, 1);
                    lean_inc(v_snd_2830_);
                    v_fst_2831_ = lean_ctor_get(v_b_2792_, 0);
                    lean_inc(v_fst_2831_);
                    lean_dec_ref(v_b_2792_);
                    v_fst_2832_ = lean_ctor_get(v_snd_2830_, 0);
                    v_snd_2833_ = lean_ctor_get(v_snd_2830_, 1);
                    v_isSharedCheck_2900_ = (!lean_is_exclusive(v_snd_2830_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2835_ = v_snd_2830_;
                        v_isShared_2836_ = v_isSharedCheck_2900_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2833_);
                        lean_inc(v_fst_2832_);
                        lean_dec(v_snd_2830_);
                        v___x_2835_ = lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2900_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2802_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2802_, 0, v___y_2801_);
                lean_ctor_set(v___x_2802_, 1, v___y_2799_);
                v___x_2803_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2803_, 0, v___y_2800_);
                lean_ctor_set(v___x_2803_, 1, v___x_2802_);
                v___x_2804_ = 1usize;
                v___x_2805_ = lean_usize_add(v_i_2791_, v___x_2804_);
                v_i_2791_ = v___x_2805_;
                v_b_2792_ = v___x_2803_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2815_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2815_, 0, v___y_2809_);
                v___x_2816_ =
                    l_Lean_PersistentArray_set___redArg(v___y_2811_, v___y_2814_, v___x_2815_);
                lean_dec(v___y_2814_);
                v___x_2817_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2817_, 0, v___y_2810_);
                lean_ctor_set(v___x_2817_, 1, v___x_2816_);
                lean_ctor_set(v___x_2817_, 2, v___y_2808_);
                v___y_2799_ = v___y_2812_;
                v___y_2800_ = v___y_2813_;
                v___y_2801_ = v___x_2817_;
                state = 1;
                continue;
            }
            3 => {
                lean_inc_ref(v___y_2820_);
                v___x_2826_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(v___y_2822_, v___y_2825_, v___y_2820_);
                v_index_2827_ = lean_ctor_get(v___y_2820_, 0);
                lean_inc(v_index_2827_);
                v___y_2808_ = v___y_2819_;
                v___y_2809_ = v___y_2820_;
                v___y_2810_ = v___x_2826_;
                v___y_2811_ = v___y_2821_;
                v___y_2812_ = v___y_2823_;
                v___y_2813_ = v___y_2824_;
                v___y_2814_ = v_index_2827_;
                state = 2;
                continue;
            }
            4 => {
                v___x_2837_ = lean_unsigned_to_nat(0);
                v_a_2838_ = lean_array_uget_borrowed(v_as_2789_, v_i_2791_);
                lean_inc(v_a_2838_);
                lean_inc(v_fst_2832_);
                v___x_2878_ = l_Lean_LocalContext_get_x21(v_fst_2832_, v_a_2838_);
                v___x_2879_ = l_Lean_LocalDecl_userName(v___x_2878_);
                v___x_2880_ = l_Lean_Name_hasMacroScopes(v___x_2879_);
                if v___x_2880_ == 0 {
                    lean_dec_ref(v___x_2878_);
                    v_baseName_2871_ = v___x_2879_;
                    v___y_2872_ = v___y_2793_;
                    v___y_2873_ = v___y_2794_;
                    v___y_2874_ = v___y_2795_;
                    v___y_2875_ = v___y_2796_;
                    state = 9;
                    continue;
                } else {
                    v___x_2881_ = lean_erase_macro_scopes(v___x_2879_);
                    v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3;
                    v___x_2897_ = lean_name_eq(v___x_2881_, v___x_2896_);
                    if v___x_2897_ == 0 {
                        v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5;
                        v___x_2899_ = lean_name_eq(v___x_2881_, v___x_2898_);
                        if v___x_2899_ == 0 {
                            lean_dec_ref(v___x_2878_);
                            v_baseName_2871_ = v___x_2881_;
                            v___y_2872_ = v___y_2793_;
                            v___y_2873_ = v___y_2794_;
                            v___y_2874_ = v___y_2795_;
                            v___y_2875_ = v___y_2796_;
                            state = 9;
                            continue;
                        } else {
                            state = 10;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v___y_2840_);
                if v_isShared_2836_ == 0 {
                    lean_ctor_set(v___x_2835_, 1, v___y_2845_);
                    lean_ctor_set(v___x_2835_, 0, v___y_2840_);
                    v___x_2847_ = v___x_2835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___y_2840_);
                    lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___y_2845_);
                    v___x_2847_ = v_reuseFailAlloc_2869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc(v___y_2840_);
                v___x_2848_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v_fst_2831_, v___x_2788_, v___y_2840_, v___x_2847_);
                if lean_obj_tag(v___x_2848_) == 0 {
                    v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
                    lean_inc(v_a_2849_);
                    lean_dec_ref_known(v___x_2848_, 1);
                    v_fst_2850_ = lean_ctor_get(v_a_2849_, 0);
                    lean_inc_n(v_fst_2850_, 2);
                    v_snd_2851_ = lean_ctor_get(v_a_2849_, 1);
                    lean_inc(v_snd_2851_);
                    lean_dec(v_a_2849_);
                    v_fvarIdToDecl_2852_ = lean_ctor_get(v_fst_2832_, 0);
                    v_decls_2853_ = lean_ctor_get(v_fst_2832_, 1);
                    v_auxDeclToFullName_2854_ = lean_ctor_get(v_fst_2832_, 2);
                    v___x_2855_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_snd_2833_, v___y_2840_, v_snd_2851_);
                    lean_inc_n(v_a_2838_, 2);
                    v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2831_, v_fst_2850_, v_a_2838_);
                    lean_inc(v_fst_2832_);
                    v___x_2857_ = lean_local_ctx_find(v_fst_2832_, v_a_2838_);
                    if lean_obj_tag(v___x_2857_) == 0 {
                        lean_dec(v_fst_2850_);
                        v___y_2799_ = v___x_2855_;
                        v___y_2800_ = v___x_2856_;
                        v___y_2801_ = v_fst_2832_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_auxDeclToFullName_2854_);
                        lean_inc_ref(v_decls_2853_);
                        lean_inc_ref(v_fvarIdToDecl_2852_);
                        lean_dec(v_fst_2832_);
                        v_val_2858_ = lean_ctor_get(v___x_2857_, 0);
                        lean_inc(v_val_2858_);
                        lean_dec_ref_known(v___x_2857_, 1);
                        v___x_2859_ = l_Lean_LocalDecl_setUserName(v_val_2858_, v_fst_2850_);
                        v_fvarId_2860_ = lean_ctor_get(v___x_2859_, 1);
                        lean_inc(v_fvarId_2860_);
                        v___y_2819_ = v_auxDeclToFullName_2854_;
                        v___y_2820_ = v___x_2859_;
                        v___y_2821_ = v_decls_2853_;
                        v___y_2822_ = v_fvarIdToDecl_2852_;
                        v___y_2823_ = v___x_2855_;
                        v___y_2824_ = v___x_2856_;
                        v___y_2825_ = v_fvarId_2860_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2840_);
                    lean_dec(v_snd_2833_);
                    lean_dec(v_fst_2832_);
                    lean_dec(v_fst_2831_);
                    v_a_2861_ = lean_ctor_get(v___x_2848_, 0);
                    v_isSharedCheck_2868_ = (!lean_is_exclusive(v___x_2848_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2848_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2861_);
                        lean_dec(v___x_2848_);
                        v___x_2863_ = lean_box(0);
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2866_;
            }
            9 => {
                v___x_2876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_snd_2833_, v_baseName_2871_);
                if lean_obj_tag(v___x_2876_) == 0 {
                    v___y_2840_ = v_baseName_2871_;
                    v___y_2841_ = v___y_2872_;
                    v___y_2842_ = v___y_2874_;
                    v___y_2843_ = v___y_2873_;
                    v___y_2844_ = v___y_2875_;
                    v___y_2845_ = v___x_2837_;
                    state = 5;
                    continue;
                } else {
                    v_val_2877_ = lean_ctor_get(v___x_2876_, 0);
                    lean_inc(v_val_2877_);
                    lean_dec_ref_known(v___x_2876_, 1);
                    v___y_2840_ = v_baseName_2871_;
                    v___y_2841_ = v___y_2872_;
                    v___y_2842_ = v___y_2874_;
                    v___y_2843_ = v___y_2873_;
                    v___y_2844_ = v___y_2875_;
                    v___y_2845_ = v_val_2877_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v___x_2883_ = l_Lean_LocalDecl_type(v___x_2878_);
                lean_dec_ref(v___x_2878_);
                v___x_2884_ = l_Lean_Meta_isProp(
                    v___x_2883_,
                    v___y_2793_,
                    v___y_2794_,
                    v___y_2795_,
                    v___y_2796_,
                );
                if lean_obj_tag(v___x_2884_) == 0 {
                    v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
                    lean_inc(v_a_2885_);
                    lean_dec_ref_known(v___x_2884_, 1);
                    v___x_2886_ = (lean_unbox(v_a_2885_) as u8);
                    lean_dec(v_a_2885_);
                    if v___x_2886_ == 0 {
                        v_baseName_2871_ = v___x_2881_;
                        v___y_2872_ = v___y_2793_;
                        v___y_2873_ = v___y_2794_;
                        v___y_2874_ = v___y_2795_;
                        v___y_2875_ = v___y_2796_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_2881_);
                        v___x_2887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1;
                        v_baseName_2871_ = v___x_2887_;
                        v___y_2872_ = v___y_2793_;
                        v___y_2873_ = v___y_2794_;
                        v___y_2874_ = v___y_2795_;
                        v___y_2875_ = v___y_2796_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2881_);
                    lean_del_object(v___x_2835_);
                    lean_dec(v_snd_2833_);
                    lean_dec(v_fst_2832_);
                    lean_dec(v_fst_2831_);
                    v_a_2888_ = lean_ctor_get(v___x_2884_, 0);
                    v_isSharedCheck_2895_ = (!lean_is_exclusive(v___x_2884_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2890_ = v___x_2884_;
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2888_);
                        lean_dec(v___x_2884_);
                        v___x_2890_ = lean_box(0);
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_2891_ == 0 {
                    v___x_2893_ = v___x_2890_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___boxed(
    mut v___x_2901_: *mut LeanObject,
    mut v_as_2902_: *mut LeanObject,
    mut v_sz_2903_: *mut LeanObject,
    mut v_i_2904_: *mut LeanObject,
    mut v_b_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2911_: usize = 0;
    let mut v_i_boxed_2912_: usize = 0;
    let mut v_res_2913_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2911_ = lean_unbox_usize(v_sz_2903_);
    lean_dec(v_sz_2903_);
    v_i_boxed_2912_ = lean_unbox_usize(v_i_2904_);
    lean_dec(v_i_2904_);
    v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(v___x_2901_, v_as_2902_, v_sz_boxed_2911_, v_i_boxed_2912_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
    lean_dec(v___y_2909_);
    lean_dec_ref(v___y_2908_);
    lean_dec(v___y_2907_);
    lean_dec_ref(v___y_2906_);
    lean_dec_ref(v_as_2902_);
    lean_dec(v___x_2901_);
    return v_res_2913_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0()
-> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_box(0);
    v___x_2915_ = lean_unsigned_to_nat(16);
    v___x_2916_ = lean_mk_array(v___x_2915_, v___x_2914_);
    return v___x_2916_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1()
-> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2919_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0);
    v___x_2918_ = lean_unsigned_to_nat(0);
    v_map_2919_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_map_2919_, 0, v___x_2918_);
    lean_ctor_set(v_map_2919_, 1, v___x_2917_);
    return v_map_2919_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3()
-> *mut LeanObject {
    let mut v_toRename_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v_toRename_2922_ =
        l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2;
    v_map_2923_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1);
    v___x_2924_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2924_, 0, v_map_2923_);
    lean_ctor_set(v___x_2924_, 1, v_toRename_2922_);
    return v___x_2924_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_fst_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut v___y_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2952_: usize = 0;
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v_snd_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_a_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2972_: u8 = 0;
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_isSharedCheck_2988_: u8 = 0;
    let mut v_a_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2930_ = lean_ctor_get(v_a_2925_, 2);
                v_decls_2931_ = lean_ctor_get(v_lctx_2930_, 1);
                v___x_2932_ = lean_unsigned_to_nat(0);
                v_map_2933_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1);
                v___x_2934_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3);
                v___x_2935_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(v_decls_2931_, v___x_2934_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                if lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2988_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2988_ == 0 {
                        v___x_2938_ = v___x_2935_;
                        v_isShared_2939_ = v_isSharedCheck_2988_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2936_);
                        lean_dec(v___x_2935_);
                        v___x_2938_ = lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2989_ = lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2996_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v___x_2991_ = v___x_2935_;
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2989_);
                        lean_dec(v___x_2935_);
                        v___x_2991_ = lean_box(0);
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2940_ = lean_ctor_get(v_a_2936_, 0);
                v_snd_2941_ = lean_ctor_get(v_a_2936_, 1);
                v_isSharedCheck_2987_ = (!lean_is_exclusive(v_a_2936_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v___x_2943_ = v_a_2936_;
                    v_isShared_2944_ = v_isSharedCheck_2987_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2941_);
                    lean_inc(v_fst_2940_);
                    lean_dec(v_a_2936_);
                    v___x_2943_ = lean_box(0);
                    v_isShared_2944_ = v_isSharedCheck_2987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2945_ = lean_array_get_size(v_snd_2941_);
                v___x_2946_ = lean_nat_dec_eq(v___x_2945_, v___x_2932_);
                if v___x_2946_ == 0 {
                    lean_del_object(v___x_2938_);
                    if v___x_2946_ == 0 {
                        v___x_2978_ = lean_unsigned_to_nat(1);
                        v___x_2979_ = lean_nat_sub(v___x_2945_, v___x_2978_);
                        v___x_2983_ = lean_nat_dec_le(v___x_2932_, v___x_2979_);
                        if v___x_2983_ == 0 {
                            lean_inc(v___x_2979_);
                            v___y_2981_ = v___x_2979_;
                            state = 10;
                            continue;
                        } else {
                            v___y_2981_ = v___x_2932_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___y_2948_ = v_snd_2941_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2943_);
                    lean_dec(v_snd_2941_);
                    lean_dec(v_fst_2940_);
                    lean_inc_ref(v_lctx_2930_);
                    if v_isShared_2939_ == 0 {
                        lean_ctor_set(v___x_2938_, 0, v_lctx_2930_);
                        v___x_2985_ = v___x_2938_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_lctx_2930_);
                        v___x_2985_ = v_reuseFailAlloc_2986_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc_ref(v_lctx_2930_);
                if v_isShared_2944_ == 0 {
                    lean_ctor_set(v___x_2943_, 1, v_map_2933_);
                    lean_ctor_set(v___x_2943_, 0, v_lctx_2930_);
                    v___x_2950_ = v___x_2943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_lctx_2930_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_map_2933_);
                    v___x_2950_ = v_reuseFailAlloc_2973_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2951_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2951_, 0, v_fst_2940_);
                lean_ctor_set(v___x_2951_, 1, v___x_2950_);
                v_sz_2952_ = lean_array_size(v___y_2948_);
                v___x_2953_ = 0usize;
                v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(v___x_2945_, v___y_2948_, v_sz_2952_, v___x_2953_, v___x_2951_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                lean_dec_ref(v___y_2948_);
                if lean_obj_tag(v___x_2954_) == 0 {
                    v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
                    v_isSharedCheck_2964_ = (!lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2957_ = v___x_2954_;
                        v_isShared_2958_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2955_);
                        lean_dec(v___x_2954_);
                        v___x_2957_ = lean_box(0);
                        v_isShared_2958_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2965_ = lean_ctor_get(v___x_2954_, 0);
                    v_isSharedCheck_2972_ = (!lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2972_ == 0 {
                        v___x_2967_ = v___x_2954_;
                        v_isShared_2968_ = v_isSharedCheck_2972_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2965_);
                        lean_dec(v___x_2954_);
                        v___x_2967_ = lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_2972_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_2959_ = lean_ctor_get(v_a_2955_, 1);
                lean_inc(v_snd_2959_);
                lean_dec(v_a_2955_);
                v_fst_2960_ = lean_ctor_get(v_snd_2959_, 0);
                lean_inc(v_fst_2960_);
                lean_dec(v_snd_2959_);
                if v_isShared_2958_ == 0 {
                    lean_ctor_set(v___x_2957_, 0, v_fst_2960_);
                    v___x_2962_ = v___x_2957_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2960_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2962_;
            }
            7 => {
                if v_isShared_2968_ == 0 {
                    v___x_2970_ = v___x_2967_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
                    v___x_2970_ = v_reuseFailAlloc_2971_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2970_;
            }
            9 => {
                lean_inc_ref(v_lctx_2930_);
                v___x_2977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v_lctx_2930_, v___x_2945_, v_snd_2941_, v___y_2975_, v___y_2976_);
                lean_dec(v___y_2976_);
                v___y_2948_ = v___x_2977_;
                state = 3;
                continue;
            }
            10 => {
                v___x_2982_ = lean_nat_dec_le(v___y_2981_, v___x_2979_);
                if v___x_2982_ == 0 {
                    lean_dec(v___x_2979_);
                    lean_inc(v___y_2981_);
                    v___y_2975_ = v___y_2981_;
                    v___y_2976_ = v___y_2981_;
                    state = 9;
                    continue;
                } else {
                    v___y_2975_ = v___y_2981_;
                    v___y_2976_ = v___x_2979_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                return v___x_2985_;
            }
            12 => {
                if v_isShared_2992_ == 0 {
                    v___x_2994_ = v___x_2991_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
                    v___x_2994_ = v_reuseFailAlloc_2995_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___boxed(
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3002_: *mut LeanObject = core::ptr::null_mut();
    v_res_3002_ = l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
        v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
    );
    lean_dec(v_a_3000_);
    lean_dec_ref(v_a_2999_);
    lean_dec(v_a_2998_);
    lean_dec_ref(v_a_2997_);
    return v_res_3002_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0(
    mut v_00_u03b2_3003_: *mut LeanObject,
    mut v_m_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v_b_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v___x_3007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_m_3004_, v_a_3005_, v_b_3006_);
    return v___x_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1(
    mut v_00_u03b2_3008_: *mut LeanObject,
    mut v_m_3009_: *mut LeanObject,
    mut v_a_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_m_3009_, v_a_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___boxed(
    mut v_00_u03b2_3012_: *mut LeanObject,
    mut v_m_3013_: *mut LeanObject,
    mut v_a_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3015_: *mut LeanObject = core::ptr::null_mut();
    v_res_3015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1(v_00_u03b2_3012_, v_m_3013_, v_a_3014_);
    lean_dec(v_a_3014_);
    lean_dec_ref(v_m_3013_);
    return v_res_3015_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3(
    mut v_00_u03b2_3016_: *mut LeanObject,
    mut v_m_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
) -> u8 {
    let mut v___x_3019_: u8 = 0;
    v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v_m_3017_, v_a_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___boxed(
    mut v_00_u03b2_3020_: *mut LeanObject,
    mut v_m_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3023_: u8 = 0;
    let mut v_r_3024_: *mut LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3(v_00_u03b2_3020_, v_m_3021_, v_a_3022_);
    lean_dec(v_a_3022_);
    lean_dec_ref(v_m_3021_);
    v_r_3024_ = lean_box((v_res_3023_) as usize);
    return v_r_3024_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4(
    mut v___x_3025_: *mut LeanObject,
    mut v___x_3026_: *mut LeanObject,
    mut v_baseName_3027_: *mut LeanObject,
    mut v_inst_3028_: *mut LeanObject,
    mut v_a_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    v___x_3035_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v___x_3025_, v___x_3026_, v_baseName_3027_, v_a_3029_);
    return v___x_3035_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___boxed(
    mut v___x_3036_: *mut LeanObject,
    mut v___x_3037_: *mut LeanObject,
    mut v_baseName_3038_: *mut LeanObject,
    mut v_inst_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
    mut v___y_3044_: *mut LeanObject,
    mut v___y_3045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3046_: *mut LeanObject = core::ptr::null_mut();
    v_res_3046_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4(v___x_3036_, v___x_3037_, v_baseName_3038_, v_inst_3039_, v_a_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
    lean_dec(v___y_3044_);
    lean_dec_ref(v___y_3043_);
    lean_dec(v___y_3042_);
    lean_dec_ref(v___y_3041_);
    lean_dec(v___x_3037_);
    lean_dec_ref(v___x_3036_);
    return v_res_3046_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5(
    mut v_00_u03b2_3047_: *mut LeanObject,
    mut v_x_3048_: *mut LeanObject,
    mut v_x_3049_: *mut LeanObject,
    mut v_x_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(v_x_3048_, v_x_3049_, v_x_3050_);
    return v___x_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7(
    mut v___x_3052_: *mut LeanObject,
    mut v_n_3053_: *mut LeanObject,
    mut v_as_3054_: *mut LeanObject,
    mut v_lo_3055_: *mut LeanObject,
    mut v_hi_3056_: *mut LeanObject,
    mut v_w_3057_: *mut LeanObject,
    mut v_hlo_3058_: *mut LeanObject,
    mut v_hhi_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    v___x_3060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_3052_, v_n_3053_, v_as_3054_, v_lo_3055_, v_hi_3056_);
    return v___x_3060_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___boxed(
    mut v___x_3061_: *mut LeanObject,
    mut v_n_3062_: *mut LeanObject,
    mut v_as_3063_: *mut LeanObject,
    mut v_lo_3064_: *mut LeanObject,
    mut v_hi_3065_: *mut LeanObject,
    mut v_w_3066_: *mut LeanObject,
    mut v_hlo_3067_: *mut LeanObject,
    mut v_hhi_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3069_: *mut LeanObject = core::ptr::null_mut();
    v_res_3069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7(v___x_3061_, v_n_3062_, v_as_3063_, v_lo_3064_, v_hi_3065_, v_w_3066_, v_hlo_3067_, v_hhi_3068_);
    lean_dec(v_hi_3065_);
    lean_dec(v_n_3062_);
    return v_res_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0(
    mut v_00_u03b2_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_x_3072_: *mut LeanObject,
) -> u8 {
    let mut v___x_3073_: u8 = 0;
    v___x_3073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_3071_, v_x_3072_);
    return v___x_3073_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___boxed(
    mut v_00_u03b2_3074_: *mut LeanObject,
    mut v_a_3075_: *mut LeanObject,
    mut v_x_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3077_: u8 = 0;
    let mut v_r_3078_: *mut LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0(v_00_u03b2_3074_, v_a_3075_, v_x_3076_);
    lean_dec(v_x_3076_);
    lean_dec(v_a_3075_);
    v_r_3078_ = lean_box((v_res_3077_) as usize);
    return v_r_3078_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1(
    mut v_00_u03b2_3079_: *mut LeanObject,
    mut v_data_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    v___x_3081_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1___redArg(v_data_3080_);
    return v___x_3081_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2(
    mut v_00_u03b2_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_b_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(v_a_3083_, v_b_3084_, v_x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4(
    mut v_00_u03b2_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_x_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(v_a_3088_, v_x_3089_);
    return v___x_3090_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___boxed(
    mut v_00_u03b2_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_x_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3094_: *mut LeanObject = core::ptr::null_mut();
    v_res_3094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4(v_00_u03b2_3091_, v_a_3092_, v_x_3093_);
    lean_dec(v_x_3093_);
    lean_dec(v_a_3092_);
    return v_res_3094_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11(
    mut v_00_u03b2_3095_: *mut LeanObject,
    mut v_x_3096_: *mut LeanObject,
    mut v_x_3097_: usize,
    mut v_x_3098_: usize,
    mut v_x_3099_: *mut LeanObject,
    mut v_x_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_3096_, v_x_3097_, v_x_3098_, v_x_3099_, v_x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___boxed(
    mut v_00_u03b2_3102_: *mut LeanObject,
    mut v_x_3103_: *mut LeanObject,
    mut v_x_3104_: *mut LeanObject,
    mut v_x_3105_: *mut LeanObject,
    mut v_x_3106_: *mut LeanObject,
    mut v_x_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_11219__boxed_3108_: usize = 0;
    let mut v_x_11220__boxed_3109_: usize = 0;
    let mut v_res_3110_: *mut LeanObject = core::ptr::null_mut();
    v_x_11219__boxed_3108_ = lean_unbox_usize(v_x_3104_);
    lean_dec(v_x_3104_);
    v_x_11220__boxed_3109_ = lean_unbox_usize(v_x_3105_);
    lean_dec(v_x_3105_);
    v_res_3110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11(v_00_u03b2_3102_, v_x_3103_, v_x_11219__boxed_3108_, v_x_11220__boxed_3109_, v_x_3106_, v_x_3107_);
    return v_res_3110_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14(
    mut v___x_3111_: *mut LeanObject,
    mut v_n_3112_: *mut LeanObject,
    mut v_lo_3113_: *mut LeanObject,
    mut v_hi_3114_: *mut LeanObject,
    mut v_hhi_3115_: *mut LeanObject,
    mut v_pivot_3116_: *mut LeanObject,
    mut v_as_3117_: *mut LeanObject,
    mut v_i_3118_: *mut LeanObject,
    mut v_k_3119_: *mut LeanObject,
    mut v_ilo_3120_: *mut LeanObject,
    mut v_ik_3121_: *mut LeanObject,
    mut v_w_3122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    v___x_3123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_3111_, v_hi_3114_, v_pivot_3116_, v_as_3117_, v_i_3118_, v_k_3119_);
    return v___x_3123_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___boxed(
    mut v___x_3124_: *mut LeanObject,
    mut v_n_3125_: *mut LeanObject,
    mut v_lo_3126_: *mut LeanObject,
    mut v_hi_3127_: *mut LeanObject,
    mut v_hhi_3128_: *mut LeanObject,
    mut v_pivot_3129_: *mut LeanObject,
    mut v_as_3130_: *mut LeanObject,
    mut v_i_3131_: *mut LeanObject,
    mut v_k_3132_: *mut LeanObject,
    mut v_ilo_3133_: *mut LeanObject,
    mut v_ik_3134_: *mut LeanObject,
    mut v_w_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3136_: *mut LeanObject = core::ptr::null_mut();
    v_res_3136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14(v___x_3124_, v_n_3125_, v_lo_3126_, v_hi_3127_, v_hhi_3128_, v_pivot_3129_, v_as_3130_, v_i_3131_, v_k_3132_, v_ilo_3133_, v_ik_3134_, v_w_3135_);
    lean_dec(v_hi_3127_);
    lean_dec(v_lo_3126_);
    lean_dec(v_n_3125_);
    return v_res_3136_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3137_: *mut LeanObject,
    mut v_i_3138_: *mut LeanObject,
    mut v_source_3139_: *mut LeanObject,
    mut v_target_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    v___x_3141_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2___redArg(v_i_3138_, v_source_3139_, v_target_3140_);
    return v___x_3141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11(
    mut v_as_3142_: *mut LeanObject,
    mut v_sz_3143_: usize,
    mut v_i_3144_: usize,
    mut v_b_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(v_as_3142_, v_sz_3143_, v_i_3144_, v_b_3145_);
    return v___x_3151_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___boxed(
    mut v_as_3152_: *mut LeanObject,
    mut v_sz_3153_: *mut LeanObject,
    mut v_i_3154_: *mut LeanObject,
    mut v_b_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
    mut v___y_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3161_: usize = 0;
    let mut v_i_boxed_3162_: usize = 0;
    let mut v_res_3163_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3153_);
    lean_dec(v_sz_3153_);
    v_i_boxed_3162_ = lean_unbox_usize(v_i_3154_);
    lean_dec(v_i_3154_);
    v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11(v_as_3152_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
    lean_dec(v___y_3159_);
    lean_dec_ref(v___y_3158_);
    lean_dec(v___y_3157_);
    lean_dec_ref(v___y_3156_);
    lean_dec_ref(v_as_3152_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16(
    mut v_00_u03b2_3164_: *mut LeanObject,
    mut v_n_3165_: *mut LeanObject,
    mut v_k_3166_: *mut LeanObject,
    mut v_v_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16___redArg(v_n_3165_, v_k_3166_, v_v_3167_);
    return v___x_3168_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17(
    mut v_00_u03b2_3169_: *mut LeanObject,
    mut v_depth_3170_: usize,
    mut v_keys_3171_: *mut LeanObject,
    mut v_vals_3172_: *mut LeanObject,
    mut v_heq_3173_: *mut LeanObject,
    mut v_i_3174_: *mut LeanObject,
    mut v_entries_3175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    v___x_3176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_depth_3170_, v_keys_3171_, v_vals_3172_, v_i_3174_, v_entries_3175_);
    return v___x_3176_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___boxed(
    mut v_00_u03b2_3177_: *mut LeanObject,
    mut v_depth_3178_: *mut LeanObject,
    mut v_keys_3179_: *mut LeanObject,
    mut v_vals_3180_: *mut LeanObject,
    mut v_heq_3181_: *mut LeanObject,
    mut v_i_3182_: *mut LeanObject,
    mut v_entries_3183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3184_: usize = 0;
    let mut v_res_3185_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3184_ = lean_unbox_usize(v_depth_3178_);
    lean_dec(v_depth_3178_);
    v_res_3185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17(v_00_u03b2_3177_, v_depth_boxed_3184_, v_keys_3179_, v_vals_3180_, v_heq_3181_, v_i_3182_, v_entries_3183_);
    lean_dec_ref(v_vals_3180_);
    lean_dec_ref(v_keys_3179_);
    return v_res_3185_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10(
    mut v_00_u03b2_3186_: *mut LeanObject,
    mut v_x_3187_: *mut LeanObject,
    mut v_x_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(v_x_3187_, v_x_3188_);
    return v___x_3189_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16(
    mut v_as_3190_: *mut LeanObject,
    mut v_sz_3191_: usize,
    mut v_i_3192_: usize,
    mut v_b_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(v_as_3190_, v_sz_3191_, v_i_3192_, v_b_3193_);
    return v___x_3199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___boxed(
    mut v_as_3200_: *mut LeanObject,
    mut v_sz_3201_: *mut LeanObject,
    mut v_i_3202_: *mut LeanObject,
    mut v_b_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
    mut v___y_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3209_: usize = 0;
    let mut v_i_boxed_3210_: usize = 0;
    let mut v_res_3211_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3209_ = lean_unbox_usize(v_sz_3201_);
    lean_dec(v_sz_3201_);
    v_i_boxed_3210_ = lean_unbox_usize(v_i_3202_);
    lean_dec(v_i_3202_);
    v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16(v_as_3200_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
    lean_dec(v___y_3207_);
    lean_dec_ref(v___y_3206_);
    lean_dec(v___y_3205_);
    lean_dec_ref(v___y_3204_);
    lean_dec_ref(v_as_3200_);
    return v_res_3211_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21(
    mut v_00_u03b2_3212_: *mut LeanObject,
    mut v_x_3213_: *mut LeanObject,
    mut v_x_3214_: *mut LeanObject,
    mut v_x_3215_: *mut LeanObject,
    mut v_x_3216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    v___x_3217_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21___redArg(v_x_3213_, v_x_3214_, v_x_3215_, v_x_3216_);
    return v___x_3217_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
    mut v_mvarId_3218_: *mut LeanObject,
    mut v_x_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_a_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3218_,
                    v_x_3219_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___y_3223_,
                );
                if lean_obj_tag(v___x_3225_) == 0 {
                    v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
                    v_isSharedCheck_3233_ = (!lean_is_exclusive(v___x_3225_)) as u8;
                    if v_isSharedCheck_3233_ == 0 {
                        v___x_3228_ = v___x_3225_;
                        v_isShared_3229_ = v_isSharedCheck_3233_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3226_);
                        lean_dec(v___x_3225_);
                        v___x_3228_ = lean_box(0);
                        v_isShared_3229_ = v_isSharedCheck_3233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3234_ = lean_ctor_get(v___x_3225_, 0);
                    v_isSharedCheck_3241_ = (!lean_is_exclusive(v___x_3225_)) as u8;
                    if v_isSharedCheck_3241_ == 0 {
                        v___x_3236_ = v___x_3225_;
                        v_isShared_3237_ = v_isSharedCheck_3241_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3234_);
                        lean_dec(v___x_3225_);
                        v___x_3236_ = lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3241_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3229_ == 0 {
                    v___x_3231_ = v___x_3228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
                    v___x_3231_ = v_reuseFailAlloc_3232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3231_;
            }
            3 => {
                if v_isShared_3237_ == 0 {
                    v___x_3239_ = v___x_3236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
                    v___x_3239_ = v_reuseFailAlloc_3240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg___boxed(
    mut v_mvarId_3242_: *mut LeanObject,
    mut v_x_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3249_: *mut LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
        v_mvarId_3242_,
        v_x_3243_,
        v___y_3244_,
        v___y_3245_,
        v___y_3246_,
        v___y_3247_,
    );
    lean_dec(v___y_3247_);
    lean_dec_ref(v___y_3246_);
    lean_dec(v___y_3245_);
    lean_dec_ref(v___y_3244_);
    return v_res_3249_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1(
    mut v_00_u03b1_3250_: *mut LeanObject,
    mut v_mvarId_3251_: *mut LeanObject,
    mut v_x_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
    mut v___y_3255_: *mut LeanObject,
    mut v___y_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
        v_mvarId_3251_,
        v_x_3252_,
        v___y_3253_,
        v___y_3254_,
        v___y_3255_,
        v___y_3256_,
    );
    return v___x_3258_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___boxed(
    mut v_00_u03b1_3259_: *mut LeanObject,
    mut v_mvarId_3260_: *mut LeanObject,
    mut v_x_3261_: *mut LeanObject,
    mut v___y_3262_: *mut LeanObject,
    mut v___y_3263_: *mut LeanObject,
    mut v___y_3264_: *mut LeanObject,
    mut v___y_3265_: *mut LeanObject,
    mut v___y_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3267_: *mut LeanObject = core::ptr::null_mut();
    v_res_3267_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1(
        v_00_u03b1_3259_,
        v_mvarId_3260_,
        v_x_3261_,
        v___y_3262_,
        v___y_3263_,
        v___y_3264_,
        v___y_3265_,
    );
    lean_dec(v___y_3265_);
    lean_dec_ref(v___y_3264_);
    lean_dec(v___y_3263_);
    lean_dec_ref(v___y_3262_);
    return v_res_3267_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_3268_: *mut LeanObject,
    mut v_x_3269_: *mut LeanObject,
    mut v_x_3270_: *mut LeanObject,
    mut v_x_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3272_ = lean_ctor_get(v_x_3268_, 0);
                v_vs_3273_ = lean_ctor_get(v_x_3268_, 1);
                v_isSharedCheck_3297_ = (!lean_is_exclusive(v_x_3268_)) as u8;
                if v_isSharedCheck_3297_ == 0 {
                    v___x_3275_ = v_x_3268_;
                    v_isShared_3276_ = v_isSharedCheck_3297_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3273_);
                    lean_inc(v_ks_3272_);
                    lean_dec(v_x_3268_);
                    v___x_3275_ = lean_box(0);
                    v_isShared_3276_ = v_isSharedCheck_3297_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3277_ = lean_array_get_size(v_ks_3272_);
                v___x_3278_ = lean_nat_dec_lt(v_x_3269_, v___x_3277_);
                if v___x_3278_ == 0 {
                    lean_dec(v_x_3269_);
                    v___x_3279_ = lean_array_push(v_ks_3272_, v_x_3270_);
                    v___x_3280_ = lean_array_push(v_vs_3273_, v_x_3271_);
                    if v_isShared_3276_ == 0 {
                        lean_ctor_set(v___x_3275_, 1, v___x_3280_);
                        lean_ctor_set(v___x_3275_, 0, v___x_3279_);
                        v___x_3282_ = v___x_3275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3279_);
                        lean_ctor_set(v_reuseFailAlloc_3283_, 1, v___x_3280_);
                        v___x_3282_ = v_reuseFailAlloc_3283_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3284_ = lean_array_fget_borrowed(v_ks_3272_, v_x_3269_);
                    v___x_3285_ = l_Lean_instBEqMVarId_beq(v_x_3270_, v_k_x27_3284_);
                    if v___x_3285_ == 0 {
                        if v_isShared_3276_ == 0 {
                            v___x_3287_ = v___x_3275_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_ks_3272_);
                            lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_vs_3273_);
                            v___x_3287_ = v_reuseFailAlloc_3291_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3292_ = lean_array_fset(v_ks_3272_, v_x_3269_, v_x_3270_);
                        v___x_3293_ = lean_array_fset(v_vs_3273_, v_x_3269_, v_x_3271_);
                        lean_dec(v_x_3269_);
                        if v_isShared_3276_ == 0 {
                            lean_ctor_set(v___x_3275_, 1, v___x_3293_);
                            lean_ctor_set(v___x_3275_, 0, v___x_3292_);
                            v___x_3295_ = v___x_3275_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3292_);
                            lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___x_3293_);
                            v___x_3295_ = v_reuseFailAlloc_3296_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3282_;
            }
            3 => {
                v___x_3288_ = lean_unsigned_to_nat(1);
                v___x_3289_ = lean_nat_add(v_x_3269_, v___x_3288_);
                lean_dec(v_x_3269_);
                v_x_3268_ = v___x_3287_;
                v_x_3269_ = v___x_3289_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_3298_: *mut LeanObject,
    mut v_k_3299_: *mut LeanObject,
    mut v_v_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = lean_unsigned_to_nat(0);
    v___x_3302_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_3298_, v___x_3301_, v_k_3299_, v_v_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(
    mut v_x_3303_: *mut LeanObject,
    mut v_x_3304_: usize,
    mut v_x_3305_: usize,
    mut v_x_3306_: *mut LeanObject,
    mut v_x_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: usize = 0;
    let mut v___x_3312_: usize = 0;
    let mut v_j_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3318_: u8 = 0;
    let mut v_v_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_node_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_unused_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3363_: u8 = 0;
    let mut v_ks_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: usize = 0;
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u8 = 0;
    let mut v_reuseFailAlloc_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3303_) == 0 {
                    v_es_3308_ = lean_ctor_get(v_x_3303_, 0);
                    v___x_3309_ = 5usize;
                    v___x_3310_ = 1usize;
                    v___x_3311_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1);
                    v___x_3312_ = lean_usize_land(v_x_3304_, v___x_3311_);
                    v_j_3313_ = lean_usize_to_nat(v___x_3312_);
                    v___x_3314_ = lean_array_get_size(v_es_3308_);
                    v___x_3315_ = lean_nat_dec_lt(v_j_3313_, v___x_3314_);
                    if v___x_3315_ == 0 {
                        lean_dec(v_j_3313_);
                        lean_dec(v_x_3307_);
                        lean_dec(v_x_3306_);
                        return v_x_3303_;
                    } else {
                        lean_inc_ref(v_es_3308_);
                        v_isSharedCheck_3352_ = (!lean_is_exclusive(v_x_3303_)) as u8;
                        if v_isSharedCheck_3352_ == 0 {
                            v_unused_3353_ = lean_ctor_get(v_x_3303_, 0);
                            lean_dec(v_unused_3353_);
                            v___x_3317_ = v_x_3303_;
                            v_isShared_3318_ = v_isSharedCheck_3352_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3303_);
                            v___x_3317_ = lean_box(0);
                            v_isShared_3318_ = v_isSharedCheck_3352_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3354_ = lean_ctor_get(v_x_3303_, 0);
                    v_vs_3355_ = lean_ctor_get(v_x_3303_, 1);
                    v_isSharedCheck_3375_ = (!lean_is_exclusive(v_x_3303_)) as u8;
                    if v_isSharedCheck_3375_ == 0 {
                        v___x_3357_ = v_x_3303_;
                        v_isShared_3358_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3355_);
                        lean_inc(v_ks_3354_);
                        lean_dec(v_x_3303_);
                        v___x_3357_ = lean_box(0);
                        v_isShared_3358_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3319_ = lean_array_fget(v_es_3308_, v_j_3313_);
                v___x_3320_ = lean_box(0);
                v_xs_x27_3321_ = lean_array_fset(v_es_3308_, v_j_3313_, v___x_3320_);
                match lean_obj_tag(v_v_3319_) {
                    0 => {
                        v_key_3328_ = lean_ctor_get(v_v_3319_, 0);
                        v_val_3329_ = lean_ctor_get(v_v_3319_, 1);
                        v_isSharedCheck_3339_ = (!lean_is_exclusive(v_v_3319_)) as u8;
                        if v_isSharedCheck_3339_ == 0 {
                            v___x_3331_ = v_v_3319_;
                            v_isShared_3332_ = v_isSharedCheck_3339_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3329_);
                            lean_inc(v_key_3328_);
                            lean_dec(v_v_3319_);
                            v___x_3331_ = lean_box(0);
                            v_isShared_3332_ = v_isSharedCheck_3339_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3340_ = lean_ctor_get(v_v_3319_, 0);
                        v_isSharedCheck_3350_ = (!lean_is_exclusive(v_v_3319_)) as u8;
                        if v_isSharedCheck_3350_ == 0 {
                            v___x_3342_ = v_v_3319_;
                            v_isShared_3343_ = v_isSharedCheck_3350_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3340_);
                            lean_dec(v_v_3319_);
                            v___x_3342_ = lean_box(0);
                            v_isShared_3343_ = v_isSharedCheck_3350_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3351_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3351_, 0, v_x_3306_);
                        lean_ctor_set(v___x_3351_, 1, v_x_3307_);
                        v___y_3323_ = v___x_3351_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3324_ = lean_array_fset(v_xs_x27_3321_, v_j_3313_, v___y_3323_);
                lean_dec(v_j_3313_);
                if v_isShared_3318_ == 0 {
                    lean_ctor_set(v___x_3317_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3326_;
            }
            4 => {
                v___x_3333_ = l_Lean_instBEqMVarId_beq(v_x_3306_, v_key_3328_);
                if v___x_3333_ == 0 {
                    lean_del_object(v___x_3331_);
                    v___x_3334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3328_,
                        v_val_3329_,
                        v_x_3306_,
                        v_x_3307_,
                    );
                    v___x_3335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3335_, 0, v___x_3334_);
                    v___y_3323_ = v___x_3335_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3329_);
                    lean_dec(v_key_3328_);
                    if v_isShared_3332_ == 0 {
                        lean_ctor_set(v___x_3331_, 1, v_x_3307_);
                        lean_ctor_set(v___x_3331_, 0, v_x_3306_);
                        v___x_3337_ = v___x_3331_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_x_3306_);
                        lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_x_3307_);
                        v___x_3337_ = v_reuseFailAlloc_3338_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3323_ = v___x_3337_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3344_ = lean_usize_shift_right(v_x_3304_, v___x_3309_);
                v___x_3345_ = lean_usize_add(v_x_3305_, v___x_3310_);
                v___x_3346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_node_3340_, v___x_3344_, v___x_3345_, v_x_3306_, v_x_3307_);
                if v_isShared_3343_ == 0 {
                    lean_ctor_set(v___x_3342_, 0, v___x_3346_);
                    v___x_3348_ = v___x_3342_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3323_ = v___x_3348_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3358_ == 0 {
                    v___x_3360_ = v___x_3357_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_ks_3354_);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_vs_3355_);
                    v___x_3360_ = v_reuseFailAlloc_3374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3___redArg(v___x_3360_, v_x_3306_, v_x_3307_);
                v___x_3369_ = 7usize;
                v___x_3370_ = lean_usize_dec_le(v___x_3369_, v_x_3305_);
                if v___x_3370_ == 0 {
                    v___x_3371_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3361_);
                    v___x_3372_ = lean_unsigned_to_nat(4);
                    v___x_3373_ = lean_nat_dec_lt(v___x_3371_, v___x_3372_);
                    lean_dec(v___x_3371_);
                    v___y_3363_ = v___x_3373_;
                    state = 10;
                    continue;
                } else {
                    v___y_3363_ = v___x_3370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3363_ == 0 {
                    v_ks_3364_ = lean_ctor_get(v_newNode_3361_, 0);
                    lean_inc_ref(v_ks_3364_);
                    v_vs_3365_ = lean_ctor_get(v_newNode_3361_, 1);
                    lean_inc_ref(v_vs_3365_);
                    lean_dec_ref(v_newNode_3361_);
                    v___x_3366_ = lean_unsigned_to_nat(0);
                    v___x_3367_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2);
                    v___x_3368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_x_3305_, v_ks_3364_, v_vs_3365_, v___x_3366_, v___x_3367_);
                    lean_dec_ref(v_vs_3365_);
                    lean_dec_ref(v_ks_3364_);
                    return v___x_3368_;
                } else {
                    return v_newNode_3361_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_3376_: usize,
    mut v_keys_3377_: *mut LeanObject,
    mut v_vals_3378_: *mut LeanObject,
    mut v_i_3379_: *mut LeanObject,
    mut v_entries_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v_k_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u64 = 0;
    let mut v_h_3386_: usize = 0;
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: usize = 0;
    let mut v_h_3392_: usize = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3381_ = lean_array_get_size(v_keys_3377_);
                v___x_3382_ = lean_nat_dec_lt(v_i_3379_, v___x_3381_);
                if v___x_3382_ == 0 {
                    lean_dec(v_i_3379_);
                    return v_entries_3380_;
                } else {
                    v_k_3383_ = lean_array_fget_borrowed(v_keys_3377_, v_i_3379_);
                    v_v_3384_ = lean_array_fget_borrowed(v_vals_3378_, v_i_3379_);
                    v___x_3385_ = l_Lean_instHashableMVarId_hash(v_k_3383_);
                    v_h_3386_ = lean_uint64_to_usize(v___x_3385_);
                    v___x_3387_ = 5usize;
                    v___x_3388_ = lean_unsigned_to_nat(1);
                    v___x_3389_ = 1usize;
                    v___x_3390_ = lean_usize_sub(v_depth_3376_, v___x_3389_);
                    v___x_3391_ = lean_usize_mul(v___x_3387_, v___x_3390_);
                    v_h_3392_ = lean_usize_shift_right(v_h_3386_, v___x_3391_);
                    v___x_3393_ = lean_nat_add(v_i_3379_, v___x_3388_);
                    lean_dec(v_i_3379_);
                    lean_inc(v_v_3384_);
                    lean_inc(v_k_3383_);
                    v___x_3394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_entries_3380_, v_h_3392_, v_depth_3376_, v_k_3383_, v_v_3384_);
                    v_i_3379_ = v___x_3393_;
                    v_entries_3380_ = v___x_3394_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_3396_: *mut LeanObject,
    mut v_keys_3397_: *mut LeanObject,
    mut v_vals_3398_: *mut LeanObject,
    mut v_i_3399_: *mut LeanObject,
    mut v_entries_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3401_: usize = 0;
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3401_ = lean_unbox_usize(v_depth_3396_);
    lean_dec(v_depth_3396_);
    v_res_3402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_3401_, v_keys_3397_, v_vals_3398_, v_i_3399_, v_entries_3400_);
    lean_dec_ref(v_vals_3398_);
    lean_dec_ref(v_keys_3397_);
    return v_res_3402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_3403_: *mut LeanObject,
    mut v_x_3404_: *mut LeanObject,
    mut v_x_3405_: *mut LeanObject,
    mut v_x_3406_: *mut LeanObject,
    mut v_x_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1508__boxed_3408_: usize = 0;
    let mut v_x_1509__boxed_3409_: usize = 0;
    let mut v_res_3410_: *mut LeanObject = core::ptr::null_mut();
    v_x_1508__boxed_3408_ = lean_unbox_usize(v_x_3404_);
    lean_dec(v_x_3404_);
    v_x_1509__boxed_3409_ = lean_unbox_usize(v_x_3405_);
    lean_dec(v_x_3405_);
    v_res_3410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3403_, v_x_1508__boxed_3408_, v_x_1509__boxed_3409_, v_x_3406_, v_x_3407_);
    return v_res_3410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(
    mut v_x_3411_: *mut LeanObject,
    mut v_x_3412_: *mut LeanObject,
    mut v_x_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3414_: u64 = 0;
    let mut v___x_3415_: usize = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_instHashableMVarId_hash(v_x_3412_);
    v___x_3415_ = lean_uint64_to_usize(v___x_3414_);
    v___x_3416_ = 1usize;
    v___x_3417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3411_, v___x_3415_, v___x_3416_, v_x_3412_, v_x_3413_);
    return v___x_3417_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
    mut v_mvarId_3418_: *mut LeanObject,
    mut v_val_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v_depth_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = lean_st_ref_take(v___y_3420_);
                v_mctx_3423_ = lean_ctor_get(v___x_3422_, 0);
                v_cache_3424_ = lean_ctor_get(v___x_3422_, 1);
                v_zetaDeltaFVarIds_3425_ = lean_ctor_get(v___x_3422_, 2);
                v_postponed_3426_ = lean_ctor_get(v___x_3422_, 3);
                v_diag_3427_ = lean_ctor_get(v___x_3422_, 4);
                v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3422_)) as u8;
                if v_isSharedCheck_3455_ == 0 {
                    v___x_3429_ = v___x_3422_;
                    v_isShared_3430_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3427_);
                    lean_inc(v_postponed_3426_);
                    lean_inc(v_zetaDeltaFVarIds_3425_);
                    lean_inc(v_cache_3424_);
                    lean_inc(v_mctx_3423_);
                    lean_dec(v___x_3422_);
                    v___x_3429_ = lean_box(0);
                    v_isShared_3430_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3431_ = lean_ctor_get(v_mctx_3423_, 0);
                v_levelAssignDepth_3432_ = lean_ctor_get(v_mctx_3423_, 1);
                v_lmvarCounter_3433_ = lean_ctor_get(v_mctx_3423_, 2);
                v_mvarCounter_3434_ = lean_ctor_get(v_mctx_3423_, 3);
                v_lDecls_3435_ = lean_ctor_get(v_mctx_3423_, 4);
                v_decls_3436_ = lean_ctor_get(v_mctx_3423_, 5);
                v_userNames_3437_ = lean_ctor_get(v_mctx_3423_, 6);
                v_lAssignment_3438_ = lean_ctor_get(v_mctx_3423_, 7);
                v_eAssignment_3439_ = lean_ctor_get(v_mctx_3423_, 8);
                v_dAssignment_3440_ = lean_ctor_get(v_mctx_3423_, 9);
                v_isSharedCheck_3454_ = (!lean_is_exclusive(v_mctx_3423_)) as u8;
                if v_isSharedCheck_3454_ == 0 {
                    v___x_3442_ = v_mctx_3423_;
                    v_isShared_3443_ = v_isSharedCheck_3454_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3440_);
                    lean_inc(v_eAssignment_3439_);
                    lean_inc(v_lAssignment_3438_);
                    lean_inc(v_userNames_3437_);
                    lean_inc(v_decls_3436_);
                    lean_inc(v_lDecls_3435_);
                    lean_inc(v_mvarCounter_3434_);
                    lean_inc(v_lmvarCounter_3433_);
                    lean_inc(v_levelAssignDepth_3432_);
                    lean_inc(v_depth_3431_);
                    lean_dec(v_mctx_3423_);
                    v___x_3442_ = lean_box(0);
                    v_isShared_3443_ = v_isSharedCheck_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(v_eAssignment_3439_, v_mvarId_3418_, v_val_3419_);
                if v_isShared_3443_ == 0 {
                    lean_ctor_set(v___x_3442_, 8, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_depth_3431_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_levelAssignDepth_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_lmvarCounter_3433_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_mvarCounter_3434_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_lDecls_3435_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 5, v_decls_3436_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 6, v_userNames_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 7, v_lAssignment_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 8, v___x_3444_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 9, v_dAssignment_3440_);
                    v___x_3446_ = v_reuseFailAlloc_3453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3430_ == 0 {
                    lean_ctor_set(v___x_3429_, 0, v___x_3446_);
                    v___x_3448_ = v___x_3429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_cache_3424_);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_zetaDeltaFVarIds_3425_);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_postponed_3426_);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_diag_3427_);
                    v___x_3448_ = v_reuseFailAlloc_3452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3449_ = lean_st_ref_set(v___y_3420_, v___x_3448_);
                v___x_3450_ = lean_box(0);
                v___x_3451_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                return v___x_3451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg___boxed(
    mut v_mvarId_3456_: *mut LeanObject,
    mut v_val_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3460_: *mut LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
        v_mvarId_3456_,
        v_val_3457_,
        v___y_3458_,
    );
    lean_dec(v___y_3458_);
    return v_res_3460_;
}
pub unsafe fn l_Lean_MVarId_exposeNames___lam__0(
    mut v_mvarId_3461_: *mut LeanObject,
    mut v___x_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
    mut v___y_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_unused_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_a_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut v_a_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3513_: u8 = 0;
    let mut v_a_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_a_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3525_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_3461_);
                v___x_3468_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3461_,
                    v___x_3462_,
                    v___y_3463_,
                    v___y_3464_,
                    v___y_3465_,
                    v___y_3466_,
                );
                if lean_obj_tag(v___x_3468_) == 0 {
                    lean_dec_ref_known(v___x_3468_, 1);
                    v___x_3469_ = l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
                    if lean_obj_tag(v___x_3469_) == 0 {
                        v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
                        lean_inc(v_a_3470_);
                        lean_dec_ref_known(v___x_3469_, 1);
                        lean_inc(v_mvarId_3461_);
                        v___x_3471_ = l_Lean_MVarId_getType(
                            v_mvarId_3461_,
                            v___y_3463_,
                            v___y_3464_,
                            v___y_3465_,
                            v___y_3466_,
                        );
                        if lean_obj_tag(v___x_3471_) == 0 {
                            v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
                            lean_inc(v_a_3472_);
                            lean_dec_ref_known(v___x_3471_, 1);
                            lean_inc(v_mvarId_3461_);
                            v___x_3473_ = l_Lean_MVarId_getTag(
                                v_mvarId_3461_,
                                v___y_3463_,
                                v___y_3464_,
                                v___y_3465_,
                                v___y_3466_,
                            );
                            if lean_obj_tag(v___x_3473_) == 0 {
                                v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
                                lean_inc(v_a_3474_);
                                lean_dec_ref_known(v___x_3473_, 1);
                                v_localInstances_3475_ = lean_ctor_get(v___y_3463_, 3);
                                lean_inc_ref(v_localInstances_3475_);
                                v___x_3476_ = 2;
                                v___x_3477_ = lean_unsigned_to_nat(0);
                                v___x_3478_ = l_Lean_Meta_mkFreshExprMVarAt(
                                    v_a_3470_,
                                    v_localInstances_3475_,
                                    v_a_3472_,
                                    v___x_3476_,
                                    v_a_3474_,
                                    v___x_3477_,
                                    v___y_3463_,
                                    v___y_3464_,
                                    v___y_3465_,
                                    v___y_3466_,
                                );
                                lean_dec_ref(v___y_3463_);
                                if lean_obj_tag(v___x_3478_) == 0 {
                                    v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
                                    lean_inc_n(v_a_3479_, 2);
                                    lean_dec_ref_known(v___x_3478_, 1);
                                    v___x_3480_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(v_mvarId_3461_, v_a_3479_, v___y_3464_);
                                    v_isSharedCheck_3488_ = (!lean_is_exclusive(v___x_3480_)) as u8;
                                    if v_isSharedCheck_3488_ == 0 {
                                        v_unused_3489_ = lean_ctor_get(v___x_3480_, 0);
                                        lean_dec(v_unused_3489_);
                                        v___x_3482_ = v___x_3480_;
                                        v_isShared_3483_ = v_isSharedCheck_3488_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3480_);
                                        v___x_3482_ = lean_box(0);
                                        v_isShared_3483_ = v_isSharedCheck_3488_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_mvarId_3461_);
                                    v_a_3490_ = lean_ctor_get(v___x_3478_, 0);
                                    v_isSharedCheck_3497_ = (!lean_is_exclusive(v___x_3478_)) as u8;
                                    if v_isSharedCheck_3497_ == 0 {
                                        v___x_3492_ = v___x_3478_;
                                        v_isShared_3493_ = v_isSharedCheck_3497_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3490_);
                                        lean_dec(v___x_3478_);
                                        v___x_3492_ = lean_box(0);
                                        v_isShared_3493_ = v_isSharedCheck_3497_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3472_);
                                lean_dec(v_a_3470_);
                                lean_dec_ref(v___y_3463_);
                                lean_dec(v_mvarId_3461_);
                                v_a_3498_ = lean_ctor_get(v___x_3473_, 0);
                                v_isSharedCheck_3505_ = (!lean_is_exclusive(v___x_3473_)) as u8;
                                if v_isSharedCheck_3505_ == 0 {
                                    v___x_3500_ = v___x_3473_;
                                    v_isShared_3501_ = v_isSharedCheck_3505_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3498_);
                                    lean_dec(v___x_3473_);
                                    v___x_3500_ = lean_box(0);
                                    v_isShared_3501_ = v_isSharedCheck_3505_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3470_);
                            lean_dec_ref(v___y_3463_);
                            lean_dec(v_mvarId_3461_);
                            v_a_3506_ = lean_ctor_get(v___x_3471_, 0);
                            v_isSharedCheck_3513_ = (!lean_is_exclusive(v___x_3471_)) as u8;
                            if v_isSharedCheck_3513_ == 0 {
                                v___x_3508_ = v___x_3471_;
                                v_isShared_3509_ = v_isSharedCheck_3513_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3506_);
                                lean_dec(v___x_3471_);
                                v___x_3508_ = lean_box(0);
                                v_isShared_3509_ = v_isSharedCheck_3513_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_3463_);
                        lean_dec(v_mvarId_3461_);
                        v_a_3514_ = lean_ctor_get(v___x_3469_, 0);
                        v_isSharedCheck_3521_ = (!lean_is_exclusive(v___x_3469_)) as u8;
                        if v_isSharedCheck_3521_ == 0 {
                            v___x_3516_ = v___x_3469_;
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3514_);
                            lean_dec(v___x_3469_);
                            v___x_3516_ = lean_box(0);
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3463_);
                    lean_dec(v_mvarId_3461_);
                    v_a_3522_ = lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3529_ = (!lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3529_ == 0 {
                        v___x_3524_ = v___x_3468_;
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3522_);
                        lean_dec(v___x_3468_);
                        v___x_3524_ = lean_box(0);
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3484_ = l_Lean_Expr_mvarId_x21(v_a_3479_);
                lean_dec(v_a_3479_);
                if v_isShared_3483_ == 0 {
                    lean_ctor_set(v___x_3482_, 0, v___x_3484_);
                    v___x_3486_ = v___x_3482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
                    v___x_3486_ = v_reuseFailAlloc_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3486_;
            }
            3 => {
                if v_isShared_3493_ == 0 {
                    v___x_3495_ = v___x_3492_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
                    v___x_3495_ = v_reuseFailAlloc_3496_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3495_;
            }
            5 => {
                if v_isShared_3501_ == 0 {
                    v___x_3503_ = v___x_3500_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
                    v___x_3503_ = v_reuseFailAlloc_3504_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3503_;
            }
            7 => {
                if v_isShared_3509_ == 0 {
                    v___x_3511_ = v___x_3508_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
                    v___x_3511_ = v_reuseFailAlloc_3512_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3511_;
            }
            9 => {
                if v_isShared_3517_ == 0 {
                    v___x_3519_ = v___x_3516_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3519_;
            }
            11 => {
                if v_isShared_3525_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_exposeNames___lam__0___boxed(
    mut v_mvarId_3530_: *mut LeanObject,
    mut v___x_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3537_: *mut LeanObject = core::ptr::null_mut();
    v_res_3537_ = l_Lean_MVarId_exposeNames___lam__0(
        v_mvarId_3530_,
        v___x_3531_,
        v___y_3532_,
        v___y_3533_,
        v___y_3534_,
        v___y_3535_,
    );
    lean_dec(v___y_3535_);
    lean_dec_ref(v___y_3534_);
    lean_dec(v___y_3533_);
    return v_res_3537_;
}
pub unsafe fn l_Lean_MVarId_exposeNames(
    mut v_mvarId_3541_: *mut LeanObject,
    mut v_a_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
    mut v_a_3544_: *mut LeanObject,
    mut v_a_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_MVarId_exposeNames___closed__1;
    lean_inc(v_mvarId_3541_);
    v___f_3548_ = lean_alloc_closure(
        l_Lean_MVarId_exposeNames___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_3548_, 0, v_mvarId_3541_);
    lean_closure_set(v___f_3548_, 1, v___x_3547_);
    v___x_3549_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
        v_mvarId_3541_,
        v___f_3548_,
        v_a_3542_,
        v_a_3543_,
        v_a_3544_,
        v_a_3545_,
    );
    return v___x_3549_;
}
pub unsafe fn l_Lean_MVarId_exposeNames___boxed(
    mut v_mvarId_3550_: *mut LeanObject,
    mut v_a_3551_: *mut LeanObject,
    mut v_a_3552_: *mut LeanObject,
    mut v_a_3553_: *mut LeanObject,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3556_: *mut LeanObject = core::ptr::null_mut();
    v_res_3556_ =
        l_Lean_MVarId_exposeNames(v_mvarId_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
    lean_dec(v_a_3554_);
    lean_dec_ref(v_a_3553_);
    lean_dec(v_a_3552_);
    lean_dec_ref(v_a_3551_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0(
    mut v_mvarId_3557_: *mut LeanObject,
    mut v_val_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    v___x_3564_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
        v_mvarId_3557_,
        v_val_3558_,
        v___y_3560_,
    );
    return v___x_3564_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___boxed(
    mut v_mvarId_3565_: *mut LeanObject,
    mut v_val_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3572_: *mut LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0(
        v_mvarId_3565_,
        v_val_3566_,
        v___y_3567_,
        v___y_3568_,
        v___y_3569_,
        v___y_3570_,
    );
    lean_dec(v___y_3570_);
    lean_dec_ref(v___y_3569_);
    lean_dec(v___y_3568_);
    lean_dec_ref(v___y_3567_);
    return v_res_3572_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0(
    mut v_00_u03b2_3573_: *mut LeanObject,
    mut v_x_3574_: *mut LeanObject,
    mut v_x_3575_: *mut LeanObject,
    mut v_x_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(v_x_3574_, v_x_3575_, v_x_3576_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3578_: *mut LeanObject,
    mut v_x_3579_: *mut LeanObject,
    mut v_x_3580_: usize,
    mut v_x_3581_: usize,
    mut v_x_3582_: *mut LeanObject,
    mut v_x_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_, v_x_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3585_: *mut LeanObject,
    mut v_x_3586_: *mut LeanObject,
    mut v_x_3587_: *mut LeanObject,
    mut v_x_3588_: *mut LeanObject,
    mut v_x_3589_: *mut LeanObject,
    mut v_x_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1908__boxed_3591_: usize = 0;
    let mut v_x_1909__boxed_3592_: usize = 0;
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_x_1908__boxed_3591_ = lean_unbox_usize(v_x_3587_);
    lean_dec(v_x_3587_);
    v_x_1909__boxed_3592_ = lean_unbox_usize(v_x_3588_);
    lean_dec(v_x_3588_);
    v_res_3593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2(v_00_u03b2_3585_, v_x_3586_, v_x_1908__boxed_3591_, v_x_1909__boxed_3592_, v_x_3589_, v_x_3590_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_3594_: *mut LeanObject,
    mut v_n_3595_: *mut LeanObject,
    mut v_k_3596_: *mut LeanObject,
    mut v_v_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3___redArg(v_n_3595_, v_k_3596_, v_v_3597_);
    return v___x_3598_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_3599_: *mut LeanObject,
    mut v_depth_3600_: usize,
    mut v_keys_3601_: *mut LeanObject,
    mut v_vals_3602_: *mut LeanObject,
    mut v_heq_3603_: *mut LeanObject,
    mut v_i_3604_: *mut LeanObject,
    mut v_entries_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_3600_, v_keys_3601_, v_vals_3602_, v_i_3604_, v_entries_3605_);
    return v___x_3606_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_3607_: *mut LeanObject,
    mut v_depth_3608_: *mut LeanObject,
    mut v_keys_3609_: *mut LeanObject,
    mut v_vals_3610_: *mut LeanObject,
    mut v_heq_3611_: *mut LeanObject,
    mut v_i_3612_: *mut LeanObject,
    mut v_entries_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3614_: usize = 0;
    let mut v_res_3615_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3614_ = lean_unbox_usize(v_depth_3608_);
    lean_dec(v_depth_3608_);
    v_res_3615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_3607_, v_depth_boxed_3614_, v_keys_3609_, v_vals_3610_, v_heq_3611_, v_i_3612_, v_entries_3613_);
    lean_dec_ref(v_vals_3610_);
    lean_dec_ref(v_keys_3609_);
    return v_res_3615_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3616_: *mut LeanObject,
    mut v_x_3617_: *mut LeanObject,
    mut v_x_3618_: *mut LeanObject,
    mut v_x_3619_: *mut LeanObject,
    mut v_x_3620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3621_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_3617_, v_x_3618_, v_x_3619_, v_x_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg(
    mut v_lctx_3622_: *mut LeanObject,
    mut v_localInsts_3623_: *mut LeanObject,
    mut v_x_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_a_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    lean_box(0),
                    v_lctx_3622_,
                    v_localInsts_3623_,
                    v_x_3624_,
                    v___y_3625_,
                    v___y_3626_,
                    v___y_3627_,
                    v___y_3628_,
                );
                if lean_obj_tag(v___x_3630_) == 0 {
                    v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3638_ = (!lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3638_ == 0 {
                        v___x_3633_ = v___x_3630_;
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3631_);
                        lean_dec(v___x_3630_);
                        v___x_3633_ = lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3639_ = lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3646_ = (!lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3641_ = v___x_3630_;
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3639_);
                        lean_dec(v___x_3630_);
                        v___x_3641_ = lean_box(0);
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3634_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
                    v___x_3636_ = v_reuseFailAlloc_3637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3636_;
            }
            3 => {
                if v_isShared_3642_ == 0 {
                    v___x_3644_ = v___x_3641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg___boxed(
    mut v_lctx_3647_: *mut LeanObject,
    mut v_localInsts_3648_: *mut LeanObject,
    mut v_x_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3655_: *mut LeanObject = core::ptr::null_mut();
    v_res_3655_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg(
        v_lctx_3647_,
        v_localInsts_3648_,
        v_x_3649_,
        v___y_3650_,
        v___y_3651_,
        v___y_3652_,
        v___y_3653_,
    );
    lean_dec(v___y_3653_);
    lean_dec_ref(v___y_3652_);
    lean_dec(v___y_3651_);
    lean_dec_ref(v___y_3650_);
    return v_res_3655_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0(
    mut v_00_u03b1_3656_: *mut LeanObject,
    mut v_lctx_3657_: *mut LeanObject,
    mut v_localInsts_3658_: *mut LeanObject,
    mut v_x_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
    mut v___y_3662_: *mut LeanObject,
    mut v___y_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg(
        v_lctx_3657_,
        v_localInsts_3658_,
        v_x_3659_,
        v___y_3660_,
        v___y_3661_,
        v___y_3662_,
        v___y_3663_,
    );
    return v___x_3665_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___boxed(
    mut v_00_u03b1_3666_: *mut LeanObject,
    mut v_lctx_3667_: *mut LeanObject,
    mut v_localInsts_3668_: *mut LeanObject,
    mut v_x_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3675_: *mut LeanObject = core::ptr::null_mut();
    v_res_3675_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0(
        v_00_u03b1_3666_,
        v_lctx_3667_,
        v_localInsts_3668_,
        v_x_3669_,
        v___y_3670_,
        v___y_3671_,
        v___y_3672_,
        v___y_3673_,
    );
    lean_dec(v___y_3673_);
    lean_dec_ref(v___y_3672_);
    lean_dec(v___y_3671_);
    lean_dec_ref(v___y_3670_);
    return v_res_3675_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(
    mut v_k_3676_: *mut LeanObject,
    mut v_allowLevelAssignments_3677_: u8,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_a_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3683_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_3677_,
                    v_k_3676_,
                    v___y_3678_,
                    v___y_3679_,
                    v___y_3680_,
                    v___y_3681_,
                );
                if lean_obj_tag(v___x_3683_) == 0 {
                    v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3691_ = (!lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v___x_3686_ = v___x_3683_;
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3684_);
                        lean_dec(v___x_3683_);
                        v___x_3686_ = lean_box(0);
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3692_ = lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3699_ = (!lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3699_ == 0 {
                        v___x_3694_ = v___x_3683_;
                        v_isShared_3695_ = v_isSharedCheck_3699_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3692_);
                        lean_dec(v___x_3683_);
                        v___x_3694_ = lean_box(0);
                        v_isShared_3695_ = v_isSharedCheck_3699_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3687_ == 0 {
                    v___x_3689_ = v___x_3686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3689_;
            }
            3 => {
                if v_isShared_3695_ == 0 {
                    v___x_3697_ = v___x_3694_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
                    v___x_3697_ = v_reuseFailAlloc_3698_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg___boxed(
    mut v_k_3700_: *mut LeanObject,
    mut v_allowLevelAssignments_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3707_: u8 = 0;
    let mut v_res_3708_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3707_ = (lean_unbox(v_allowLevelAssignments_3701_) as u8);
    v_res_3708_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(
        v_k_3700_,
        v_allowLevelAssignments_boxed_3707_,
        v___y_3702_,
        v___y_3703_,
        v___y_3704_,
        v___y_3705_,
    );
    lean_dec(v___y_3705_);
    lean_dec_ref(v___y_3704_);
    lean_dec(v___y_3703_);
    lean_dec_ref(v___y_3702_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1(
    mut v_00_u03b1_3709_: *mut LeanObject,
    mut v_k_3710_: *mut LeanObject,
    mut v_allowLevelAssignments_3711_: u8,
    mut v___y_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3717_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(
        v_k_3710_,
        v_allowLevelAssignments_3711_,
        v___y_3712_,
        v___y_3713_,
        v___y_3714_,
        v___y_3715_,
    );
    return v___x_3717_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___boxed(
    mut v_00_u03b1_3718_: *mut LeanObject,
    mut v_k_3719_: *mut LeanObject,
    mut v_allowLevelAssignments_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3726_: u8 = 0;
    let mut v_res_3727_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3726_ = (lean_unbox(v_allowLevelAssignments_3720_) as u8);
    v_res_3727_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1(
        v_00_u03b1_3718_,
        v_k_3719_,
        v_allowLevelAssignments_boxed_3726_,
        v___y_3721_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    lean_dec(v___y_3724_);
    lean_dec_ref(v___y_3723_);
    lean_dec(v___y_3722_);
    lean_dec_ref(v___y_3721_);
    return v_res_3727_;
}
pub unsafe fn l_Lean_Meta_withExposedNames___redArg(
    mut v_k_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3734_ =
                    l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
                        v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
                    );
                if lean_obj_tag(v___x_3734_) == 0 {
                    v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
                    lean_inc(v_a_3735_);
                    lean_dec_ref_known(v___x_3734_, 1);
                    v_localInstances_3736_ = lean_ctor_get(v_a_3729_, 3);
                    lean_inc_ref(v_localInstances_3736_);
                    v___x_3737_ = lean_alloc_closure(
                        l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    lean_closure_set(v___x_3737_, 0, lean_box(0));
                    lean_closure_set(v___x_3737_, 1, v_a_3735_);
                    lean_closure_set(v___x_3737_, 2, v_localInstances_3736_);
                    lean_closure_set(v___x_3737_, 3, v_k_3728_);
                    v___x_3738_ = 0;
                    v___x_3739_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(v___x_3737_, v___x_3738_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
                    return v___x_3739_;
                } else {
                    lean_dec_ref(v_k_3728_);
                    v_a_3740_ = lean_ctor_get(v___x_3734_, 0);
                    v_isSharedCheck_3747_ = (!lean_is_exclusive(v___x_3734_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3734_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3740_);
                        lean_dec(v___x_3734_);
                        v___x_3742_ = lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3743_ == 0 {
                    v___x_3745_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withExposedNames___redArg___boxed(
    mut v_k_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3754_: *mut LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_Lean_Meta_withExposedNames___redArg(
        v_k_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_,
    );
    lean_dec(v_a_3752_);
    lean_dec_ref(v_a_3751_);
    lean_dec(v_a_3750_);
    lean_dec_ref(v_a_3749_);
    return v_res_3754_;
}
pub unsafe fn l_Lean_Meta_withExposedNames(
    mut v_00_u03b1_3755_: *mut LeanObject,
    mut v_k_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
    mut v_a_3758_: *mut LeanObject,
    mut v_a_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Meta_withExposedNames___redArg(
        v_k_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_,
    );
    return v___x_3762_;
}
pub unsafe fn l_Lean_Meta_withExposedNames___boxed(
    mut v_00_u03b1_3763_: *mut LeanObject,
    mut v_k_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
    mut v_a_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3770_: *mut LeanObject = core::ptr::null_mut();
    v_res_3770_ = l_Lean_Meta_withExposedNames(
        v_00_u03b1_3763_,
        v_k_3764_,
        v_a_3765_,
        v_a_3766_,
        v_a_3767_,
        v_a_3768_,
    );
    lean_dec(v_a_3768_);
    lean_dec_ref(v_a_3767_);
    lean_dec(v_a_3766_);
    lean_dec_ref(v_a_3765_);
    return v_res_3770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_ExposeNames(builtin);
}
