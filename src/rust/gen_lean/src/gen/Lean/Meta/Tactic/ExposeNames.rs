// Lean compiler output
// Module: Lean.Meta.Tactic.ExposeNames
// Imports: Lean.Meta.Tactic.Util Init.While
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr, lean_nat_sub, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{l_Lean_Name_hasMacroScopes, lean_erase_macro_scopes};
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
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__0_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__2_value) as *mut leanh::LeanObject,13655884332201764339 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__4_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_exposeNames___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_MVarId_exposeNames___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_exposeNames___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__0_value)
                as *mut leanh::LeanObject,
            8944005891006136425 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_exposeNames___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exposeNames___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_b_1887_: *mut leanh::LeanObject,
    mut v_x_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1888_) == 0 {
                    leanh::lean_dec(v_b_1887_);
                    leanh::lean_dec(v_a_1886_);
                    return v_x_1888_;
                } else {
                    v_key_1889_ = leanh::lean_ctor_get(v_x_1888_, 0);
                    v_value_1890_ = leanh::lean_ctor_get(v_x_1888_, 1);
                    v_tail_1891_ = leanh::lean_ctor_get(v_x_1888_, 2);
                    v_isSharedCheck_1903_ = (!leanh::lean_is_exclusive(v_x_1888_)) as u8;
                    if v_isSharedCheck_1903_ == 0 {
                        v___x_1893_ = v_x_1888_;
                        v_isShared_1894_ = v_isSharedCheck_1903_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1891_);
                        leanh::lean_inc(v_value_1890_);
                        leanh::lean_inc(v_key_1889_);
                        leanh::lean_dec(v_x_1888_);
                        v___x_1893_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1893_, 2, v___x_1896_);
                        v___x_1898_ = v___x_1893_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1899_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_key_1889_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_value_1890_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___x_1896_);
                        v___x_1898_ = v_reuseFailAlloc_1899_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1890_);
                    leanh::lean_dec(v_key_1889_);
                    if v_isShared_1894_ == 0 {
                        leanh::lean_ctor_set(v___x_1893_, 1, v_b_1887_);
                        leanh::lean_ctor_set(v___x_1893_, 0, v_a_1886_);
                        v___x_1901_ = v___x_1893_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1902_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1886_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_b_1887_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_tail_1891_);
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
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u64 = 0;
    v___x_1904_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1905_ = lean_uint64_of_nat(v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(
    mut v_x_1906_: *mut leanh::LeanObject,
    mut v_x_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u64 = 0;
    let mut v_hash_1935_: u64 = 0;
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1907_) == 0 {
                    return v_x_1906_;
                } else {
                    v_key_1908_ = leanh::lean_ctor_get(v_x_1907_, 0);
                    v_value_1909_ = leanh::lean_ctor_get(v_x_1907_, 1);
                    v_tail_1910_ = leanh::lean_ctor_get(v_x_1907_, 2);
                    v_isSharedCheck_1936_ = (!leanh::lean_is_exclusive(v_x_1907_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1912_ = v_x_1907_;
                        v_isShared_1913_ = v_isSharedCheck_1936_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1910_);
                        leanh::lean_inc(v_value_1909_);
                        leanh::lean_inc(v_key_1908_);
                        leanh::lean_dec(v_x_1907_);
                        v___x_1912_ = leanh::lean_box(0);
                        v_isShared_1913_ = v_isSharedCheck_1936_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1914_ = lean_array_get_size(v_x_1906_);
                if leanh::lean_obj_tag(v_key_1908_) == 0 {
                    v___x_1934_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_1916_ = v___x_1934_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1935_ = leanh::lean_ctor_get_uint64(
                        v_key_1908_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_1928_);
                if v_isShared_1913_ == 0 {
                    leanh::lean_ctor_set(v___x_1912_, 2, v___x_1928_);
                    v___x_1930_ = v___x_1912_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_key_1908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_value_1909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1928_);
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
    mut v_i_1937_: *mut leanh::LeanObject,
    mut v_source_1938_: *mut leanh::LeanObject,
    mut v_target_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v_es_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_array_get_size(v_source_1938_);
                v___x_1941_ = lean_nat_dec_lt(v_i_1937_, v___x_1940_);
                if v___x_1941_ == 0 {
                    leanh::lean_dec_ref(v_source_1938_);
                    leanh::lean_dec(v_i_1937_);
                    return v_target_1939_;
                } else {
                    v_es_1942_ = lean_array_fget(v_source_1938_, v_i_1937_);
                    v___x_1943_ = leanh::lean_box(0);
                    v_source_1944_ = lean_array_fset(v_source_1938_, v_i_1937_, v___x_1943_);
                    v_target_1945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(v_target_1939_, v_es_1942_);
                    v___x_1946_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1947_ = lean_nat_add(v_i_1937_, v___x_1946_);
                    leanh::lean_dec(v_i_1937_);
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
    mut v_data_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_array_get_size(v_data_1949_);
    v___x_1951_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1952_ = lean_nat_mul(v___x_1950_, v___x_1951_);
    v___x_1953_ = leanh::lean_unsigned_to_nat(0);
    v___x_1954_ = leanh::lean_box(0);
    v___x_1955_ = lean_mk_array(v_nbuckets_1952_, v___x_1954_);
    v___x_1956_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2___redArg(v___x_1953_, v_data_1949_, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_x_1958_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1959_: u8 = 0;
    let mut v_key_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1958_) == 0 {
                    v___x_1959_ = 0;
                    return v___x_1959_;
                } else {
                    v_key_1960_ = leanh::lean_ctor_get(v_x_1958_, 0);
                    v_tail_1961_ = leanh::lean_ctor_get(v_x_1958_, 2);
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
    mut v_a_1964_: *mut leanh::LeanObject,
    mut v_x_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: u8 = 0;
    let mut v_r_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_1964_, v_x_1965_);
    leanh::lean_dec(v_x_1965_);
    leanh::lean_dec(v_a_1964_);
    v_r_1967_ = leanh::lean_box((v_res_1966_) as usize);
    return v_r_1967_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(
    mut v_m_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
    mut v_b_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v_val_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u64 = 0;
    let mut v_hash_2017_: u64 = 0;
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1971_ = leanh::lean_ctor_get(v_m_1968_, 0);
                v_buckets_1972_ = leanh::lean_ctor_get(v_m_1968_, 1);
                v_isSharedCheck_2018_ = (!leanh::lean_is_exclusive(v_m_1968_)) as u8;
                if v_isSharedCheck_2018_ == 0 {
                    v___x_1974_ = v_m_1968_;
                    v_isShared_1975_ = v_isSharedCheck_2018_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1972_);
                    leanh::lean_inc(v_size_1971_);
                    leanh::lean_dec(v_m_1968_);
                    v___x_1974_ = leanh::lean_box(0);
                    v_isShared_1975_ = v_isSharedCheck_2018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1976_ = lean_array_get_size(v_buckets_1972_);
                if leanh::lean_obj_tag(v_a_1969_) == 0 {
                    v___x_2016_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_1978_ = v___x_2016_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2017_ = leanh::lean_ctor_get_uint64(
                        v_a_1969_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    v___x_1992_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1993_ = lean_nat_add(v_size_1971_, v___x_1992_);
                    leanh::lean_dec(v_size_1971_);
                    leanh::lean_inc(v_bkt_1990_);
                    v___x_1994_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1994_, 0, v_a_1969_);
                    leanh::lean_ctor_set(v___x_1994_, 1, v_b_1970_);
                    leanh::lean_ctor_set(v___x_1994_, 2, v_bkt_1990_);
                    v_buckets_x27_1995_ =
                        lean_array_uset(v_buckets_1972_, v___x_1989_, v___x_1994_);
                    v___x_1996_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1997_ = lean_nat_mul(v_size_x27_1993_, v___x_1996_);
                    v___x_1998_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1999_ = lean_nat_div(v___x_1997_, v___x_1998_);
                    leanh::lean_dec(v___x_1997_);
                    v___x_2000_ = lean_array_get_size(v_buckets_x27_1995_);
                    v___x_2001_ = lean_nat_dec_le(v___x_1999_, v___x_2000_);
                    leanh::lean_dec(v___x_1999_);
                    if v___x_2001_ == 0 {
                        v_val_2002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1___redArg(v_buckets_x27_1995_);
                        if v_isShared_1975_ == 0 {
                            leanh::lean_ctor_set(v___x_1974_, 1, v_val_2002_);
                            leanh::lean_ctor_set(v___x_1974_, 0, v_size_x27_1993_);
                            v___x_2004_ = v___x_1974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2005_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2005_,
                                0,
                                v_size_x27_1993_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_val_2002_);
                            v___x_2004_ = v_reuseFailAlloc_2005_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1975_ == 0 {
                            leanh::lean_ctor_set(v___x_1974_, 1, v_buckets_x27_1995_);
                            leanh::lean_ctor_set(v___x_1974_, 0, v_size_x27_1993_);
                            v___x_2007_ = v___x_1974_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2008_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2008_,
                                0,
                                v_size_x27_1993_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2008_,
                                1,
                                v_buckets_x27_1995_,
                            );
                            v___x_2007_ = v_reuseFailAlloc_2008_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1990_);
                    v___x_2009_ = leanh::lean_box(0);
                    v_buckets_x27_2010_ =
                        lean_array_uset(v_buckets_1972_, v___x_1989_, v___x_2009_);
                    v___x_2011_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(v_a_1969_, v_b_1970_, v_bkt_1990_);
                    v___x_2012_ = lean_array_uset(v_buckets_x27_2010_, v___x_1989_, v___x_2011_);
                    if v_isShared_1975_ == 0 {
                        leanh::lean_ctor_set(v___x_1974_, 1, v___x_2012_);
                        v___x_2014_ = v___x_1974_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2015_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_size_1971_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2012_);
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
    mut v_a_2019_: *mut leanh::LeanObject,
    mut v_x_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2020_) == 0 {
                    v___x_2021_ = leanh::lean_box(0);
                    return v___x_2021_;
                } else {
                    v_key_2022_ = leanh::lean_ctor_get(v_x_2020_, 0);
                    v_value_2023_ = leanh::lean_ctor_get(v_x_2020_, 1);
                    v_tail_2024_ = leanh::lean_ctor_get(v_x_2020_, 2);
                    v___x_2025_ = lean_name_eq(v_key_2022_, v_a_2019_);
                    if v___x_2025_ == 0 {
                        v_x_2020_ = v_tail_2024_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2023_);
                        v___x_2027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2027_, 0, v_value_2023_);
                        return v___x_2027_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg___boxed(
    mut v_a_2028_: *mut leanh::LeanObject,
    mut v_x_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(v_a_2028_, v_x_2029_);
    leanh::lean_dec(v_x_2029_);
    leanh::lean_dec(v_a_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(
    mut v_m_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: u64 = 0;
    let mut v_hash_2051_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2033_ = leanh::lean_ctor_get(v_m_2031_, 1);
                v___x_2034_ = lean_array_get_size(v_buckets_2033_);
                if leanh::lean_obj_tag(v_a_2032_) == 0 {
                    v___x_2050_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_2036_ = v___x_2050_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2051_ = leanh::lean_ctor_get_uint64(
                        v_a_2032_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_2052_: *mut leanh::LeanObject,
    mut v_a_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_m_2052_, v_a_2053_);
    leanh::lean_dec(v_a_2053_);
    leanh::lean_dec_ref(v_m_2052_);
    return v_res_2054_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(
    mut v_as_2055_: *mut leanh::LeanObject,
    mut v_sz_2056_: usize,
    mut v_i_2057_: usize,
    mut v_b_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: usize = 0;
    let mut v_reuseFailAlloc_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRename_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: u8 = 0;
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_unused_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_usize_dec_lt(v_i_2057_, v_sz_2056_);
                if v___x_2060_ == 0 {
                    v___x_2061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2061_, 0, v_b_2058_);
                    return v___x_2061_;
                } else {
                    v_snd_2062_ = leanh::lean_ctor_get(v_b_2058_, 1);
                    v_isSharedCheck_2098_ = (!leanh::lean_is_exclusive(v_b_2058_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v_unused_2099_ = leanh::lean_ctor_get(v_b_2058_, 0);
                        leanh::lean_dec(v_unused_2099_);
                        v___x_2064_ = v_b_2058_;
                        v_isShared_2065_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2062_);
                        leanh::lean_dec(v_b_2058_);
                        v___x_2064_ = leanh::lean_box(0);
                        v_isShared_2065_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2066_ = leanh::lean_box(0);
                v_a_2075_ = lean_array_uget_borrowed(v_as_2055_, v_i_2057_);
                if leanh::lean_obj_tag(v_a_2075_) == 0 {
                    v_a_2068_ = v_snd_2062_;
                    state = 2;
                    continue;
                } else {
                    v_val_2076_ = leanh::lean_ctor_get(v_a_2075_, 0);
                    v_fst_2077_ = leanh::lean_ctor_get(v_snd_2062_, 0);
                    v_snd_2078_ = leanh::lean_ctor_get(v_snd_2062_, 1);
                    v_isSharedCheck_2097_ = (!leanh::lean_is_exclusive(v_snd_2062_)) as u8;
                    if v_isSharedCheck_2097_ == 0 {
                        v___x_2080_ = v_snd_2062_;
                        v_isShared_2081_ = v_isSharedCheck_2097_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2078_);
                        leanh::lean_inc(v_fst_2077_);
                        leanh::lean_dec(v_snd_2062_);
                        v___x_2080_ = leanh::lean_box(0);
                        v_isShared_2081_ = v_isSharedCheck_2097_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2065_ == 0 {
                    leanh::lean_ctor_set(v___x_2064_, 1, v_a_2068_);
                    leanh::lean_ctor_set(v___x_2064_, 0, v___x_2066_);
                    v___x_2070_ = v___x_2064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_a_2068_);
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
                    if leanh::lean_obj_tag(v___x_2091_) == 1 {
                        v_val_2092_ = leanh::lean_ctor_get(v___x_2091_, 0);
                        leanh::lean_inc(v_val_2092_);
                        leanh::lean_dec_ref_known(v___x_2091_, 1);
                        v___x_2093_ = lean_array_push(v_snd_2078_, v_val_2092_);
                        v_toRename_2084_ = v___x_2093_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2091_);
                        v_toRename_2084_ = v_snd_2078_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2082_);
                    leanh::lean_del_object(v___x_2080_);
                    v___x_2094_ = l_Lean_LocalDecl_fvarId(v_val_2076_);
                    v___x_2095_ = lean_array_push(v_snd_2078_, v___x_2094_);
                    v___x_2096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2096_, 0, v_fst_2077_);
                    leanh::lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                    v_a_2068_ = v___x_2096_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2085_ = l_Lean_LocalDecl_fvarId(v_val_2076_);
                v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2077_, v___x_2082_, v___x_2085_);
                if v_isShared_2081_ == 0 {
                    leanh::lean_ctor_set(v___x_2080_, 1, v_toRename_2084_);
                    leanh::lean_ctor_set(v___x_2080_, 0, v___x_2086_);
                    v___x_2088_ = v___x_2080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_toRename_2084_);
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
    mut v_as_2100_: *mut leanh::LeanObject,
    mut v_sz_2101_: *mut leanh::LeanObject,
    mut v_i_2102_: *mut leanh::LeanObject,
    mut v_b_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2105_: usize = 0;
    let mut v_i_boxed_2106_: usize = 0;
    let mut v_res_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2105_ = leanh::lean_unbox_usize(v_sz_2101_);
    leanh::lean_dec(v_sz_2101_);
    v_i_boxed_2106_ = leanh::lean_unbox_usize(v_i_2102_);
    leanh::lean_dec(v_i_2102_);
    v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(v_as_2100_, v_sz_boxed_2105_, v_i_boxed_2106_, v_b_2103_);
    leanh::lean_dec_ref(v_as_2100_);
    return v_res_2107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(
    mut v_as_2108_: *mut leanh::LeanObject,
    mut v_sz_2109_: usize,
    mut v_i_2110_: usize,
    mut v_b_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: usize = 0;
    let mut v___x_2129_: usize = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2138_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRename_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: u8 = 0;
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_unused_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_lt(v_i_2110_, v_sz_2109_);
                if v___x_2117_ == 0 {
                    v___x_2118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2118_, 0, v_b_2111_);
                    return v___x_2118_;
                } else {
                    v_snd_2119_ = leanh::lean_ctor_get(v_b_2111_, 1);
                    v_isSharedCheck_2155_ = (!leanh::lean_is_exclusive(v_b_2111_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v_unused_2156_ = leanh::lean_ctor_get(v_b_2111_, 0);
                        leanh::lean_dec(v_unused_2156_);
                        v___x_2121_ = v_b_2111_;
                        v_isShared_2122_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2119_);
                        leanh::lean_dec(v_b_2111_);
                        v___x_2121_ = leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2123_ = leanh::lean_box(0);
                v_a_2132_ = lean_array_uget_borrowed(v_as_2108_, v_i_2110_);
                if leanh::lean_obj_tag(v_a_2132_) == 0 {
                    v_a_2125_ = v_snd_2119_;
                    state = 2;
                    continue;
                } else {
                    v_val_2133_ = leanh::lean_ctor_get(v_a_2132_, 0);
                    v_fst_2134_ = leanh::lean_ctor_get(v_snd_2119_, 0);
                    v_snd_2135_ = leanh::lean_ctor_get(v_snd_2119_, 1);
                    v_isSharedCheck_2154_ = (!leanh::lean_is_exclusive(v_snd_2119_)) as u8;
                    if v_isSharedCheck_2154_ == 0 {
                        v___x_2137_ = v_snd_2119_;
                        v_isShared_2138_ = v_isSharedCheck_2154_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2135_);
                        leanh::lean_inc(v_fst_2134_);
                        leanh::lean_dec(v_snd_2119_);
                        v___x_2137_ = leanh::lean_box(0);
                        v_isShared_2138_ = v_isSharedCheck_2154_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 1, v_a_2125_);
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2123_);
                    v___x_2127_ = v___x_2121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2125_);
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
                    if leanh::lean_obj_tag(v___x_2148_) == 1 {
                        v_val_2149_ = leanh::lean_ctor_get(v___x_2148_, 0);
                        leanh::lean_inc(v_val_2149_);
                        leanh::lean_dec_ref_known(v___x_2148_, 1);
                        v___x_2150_ = lean_array_push(v_snd_2135_, v_val_2149_);
                        v_toRename_2141_ = v___x_2150_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2148_);
                        v_toRename_2141_ = v_snd_2135_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2139_);
                    leanh::lean_del_object(v___x_2137_);
                    v___x_2151_ = l_Lean_LocalDecl_fvarId(v_val_2133_);
                    v___x_2152_ = lean_array_push(v_snd_2135_, v___x_2151_);
                    v___x_2153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2153_, 0, v_fst_2134_);
                    leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                    v_a_2125_ = v___x_2153_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2142_ = l_Lean_LocalDecl_fvarId(v_val_2133_);
                v___x_2143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2134_, v___x_2139_, v___x_2142_);
                if v_isShared_2138_ == 0 {
                    leanh::lean_ctor_set(v___x_2137_, 1, v_toRename_2141_);
                    leanh::lean_ctor_set(v___x_2137_, 0, v___x_2143_);
                    v___x_2145_ = v___x_2137_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_toRename_2141_);
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
    mut v_as_2157_: *mut leanh::LeanObject,
    mut v_sz_2158_: *mut leanh::LeanObject,
    mut v_i_2159_: *mut leanh::LeanObject,
    mut v_b_2160_: *mut leanh::LeanObject,
    mut v___y_2161_: *mut leanh::LeanObject,
    mut v___y_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2166_: usize = 0;
    let mut v_i_boxed_2167_: usize = 0;
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2166_ = leanh::lean_unbox_usize(v_sz_2158_);
    leanh::lean_dec(v_sz_2158_);
    v_i_boxed_2167_ = leanh::lean_unbox_usize(v_i_2159_);
    leanh::lean_dec(v_i_2159_);
    v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(v_as_2157_, v_sz_boxed_2166_, v_i_boxed_2167_, v_b_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
    leanh::lean_dec(v___y_2164_);
    leanh::lean_dec_ref(v___y_2163_);
    leanh::lean_dec(v___y_2162_);
    leanh::lean_dec_ref(v___y_2161_);
    leanh::lean_dec_ref(v_as_2157_);
    return v_res_2168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(
    mut v_as_2169_: *mut leanh::LeanObject,
    mut v_sz_2170_: usize,
    mut v_i_2171_: usize,
    mut v_b_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: usize = 0;
    let mut v___x_2186_: usize = 0;
    let mut v_reuseFailAlloc_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRename_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_unused_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2174_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
                if v___x_2174_ == 0 {
                    v___x_2175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2175_, 0, v_b_2172_);
                    return v___x_2175_;
                } else {
                    v_snd_2176_ = leanh::lean_ctor_get(v_b_2172_, 1);
                    v_isSharedCheck_2212_ = (!leanh::lean_is_exclusive(v_b_2172_)) as u8;
                    if v_isSharedCheck_2212_ == 0 {
                        v_unused_2213_ = leanh::lean_ctor_get(v_b_2172_, 0);
                        leanh::lean_dec(v_unused_2213_);
                        v___x_2178_ = v_b_2172_;
                        v_isShared_2179_ = v_isSharedCheck_2212_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2176_);
                        leanh::lean_dec(v_b_2172_);
                        v___x_2178_ = leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2180_ = leanh::lean_box(0);
                v_a_2189_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
                if leanh::lean_obj_tag(v_a_2189_) == 0 {
                    v_a_2182_ = v_snd_2176_;
                    state = 2;
                    continue;
                } else {
                    v_val_2190_ = leanh::lean_ctor_get(v_a_2189_, 0);
                    v_fst_2191_ = leanh::lean_ctor_get(v_snd_2176_, 0);
                    v_snd_2192_ = leanh::lean_ctor_get(v_snd_2176_, 1);
                    v_isSharedCheck_2211_ = (!leanh::lean_is_exclusive(v_snd_2176_)) as u8;
                    if v_isSharedCheck_2211_ == 0 {
                        v___x_2194_ = v_snd_2176_;
                        v_isShared_2195_ = v_isSharedCheck_2211_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2192_);
                        leanh::lean_inc(v_fst_2191_);
                        leanh::lean_dec(v_snd_2176_);
                        v___x_2194_ = leanh::lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2211_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2179_ == 0 {
                    leanh::lean_ctor_set(v___x_2178_, 1, v_a_2182_);
                    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2180_);
                    v___x_2184_ = v___x_2178_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
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
                    if leanh::lean_obj_tag(v___x_2205_) == 1 {
                        v_val_2206_ = leanh::lean_ctor_get(v___x_2205_, 0);
                        leanh::lean_inc(v_val_2206_);
                        leanh::lean_dec_ref_known(v___x_2205_, 1);
                        v___x_2207_ = lean_array_push(v_snd_2192_, v_val_2206_);
                        v_toRename_2198_ = v___x_2207_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2205_);
                        v_toRename_2198_ = v_snd_2192_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2196_);
                    leanh::lean_del_object(v___x_2194_);
                    v___x_2208_ = l_Lean_LocalDecl_fvarId(v_val_2190_);
                    v___x_2209_ = lean_array_push(v_snd_2192_, v___x_2208_);
                    v___x_2210_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2210_, 0, v_fst_2191_);
                    leanh::lean_ctor_set(v___x_2210_, 1, v___x_2209_);
                    v_a_2182_ = v___x_2210_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2199_ = l_Lean_LocalDecl_fvarId(v_val_2190_);
                v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2191_, v___x_2196_, v___x_2199_);
                if v_isShared_2195_ == 0 {
                    leanh::lean_ctor_set(v___x_2194_, 1, v_toRename_2198_);
                    leanh::lean_ctor_set(v___x_2194_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2194_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_toRename_2198_);
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
    mut v_as_2214_: *mut leanh::LeanObject,
    mut v_sz_2215_: *mut leanh::LeanObject,
    mut v_i_2216_: *mut leanh::LeanObject,
    mut v_b_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2219_: usize = 0;
    let mut v_i_boxed_2220_: usize = 0;
    let mut v_res_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2219_ = leanh::lean_unbox_usize(v_sz_2215_);
    leanh::lean_dec(v_sz_2215_);
    v_i_boxed_2220_ = leanh::lean_unbox_usize(v_i_2216_);
    leanh::lean_dec(v_i_2216_);
    v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(v_as_2214_, v_sz_boxed_2219_, v_i_boxed_2220_, v_b_2217_);
    leanh::lean_dec_ref(v_as_2214_);
    return v_res_2221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(
    mut v_as_2222_: *mut leanh::LeanObject,
    mut v_sz_2223_: usize,
    mut v_i_2224_: usize,
    mut v_b_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
    mut v___y_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRename_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut v_unused_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
                if v___x_2231_ == 0 {
                    v___x_2232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2232_, 0, v_b_2225_);
                    return v___x_2232_;
                } else {
                    v_snd_2233_ = leanh::lean_ctor_get(v_b_2225_, 1);
                    v_isSharedCheck_2269_ = (!leanh::lean_is_exclusive(v_b_2225_)) as u8;
                    if v_isSharedCheck_2269_ == 0 {
                        v_unused_2270_ = leanh::lean_ctor_get(v_b_2225_, 0);
                        leanh::lean_dec(v_unused_2270_);
                        v___x_2235_ = v_b_2225_;
                        v_isShared_2236_ = v_isSharedCheck_2269_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2233_);
                        leanh::lean_dec(v_b_2225_);
                        v___x_2235_ = leanh::lean_box(0);
                        v_isShared_2236_ = v_isSharedCheck_2269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2237_ = leanh::lean_box(0);
                v_a_2246_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
                if leanh::lean_obj_tag(v_a_2246_) == 0 {
                    v_a_2239_ = v_snd_2233_;
                    state = 2;
                    continue;
                } else {
                    v_val_2247_ = leanh::lean_ctor_get(v_a_2246_, 0);
                    v_fst_2248_ = leanh::lean_ctor_get(v_snd_2233_, 0);
                    v_snd_2249_ = leanh::lean_ctor_get(v_snd_2233_, 1);
                    v_isSharedCheck_2268_ = (!leanh::lean_is_exclusive(v_snd_2233_)) as u8;
                    if v_isSharedCheck_2268_ == 0 {
                        v___x_2251_ = v_snd_2233_;
                        v_isShared_2252_ = v_isSharedCheck_2268_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2249_);
                        leanh::lean_inc(v_fst_2248_);
                        leanh::lean_dec(v_snd_2233_);
                        v___x_2251_ = leanh::lean_box(0);
                        v_isShared_2252_ = v_isSharedCheck_2268_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2236_ == 0 {
                    leanh::lean_ctor_set(v___x_2235_, 1, v_a_2239_);
                    leanh::lean_ctor_set(v___x_2235_, 0, v___x_2237_);
                    v___x_2241_ = v___x_2235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2239_);
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
                    if leanh::lean_obj_tag(v___x_2262_) == 1 {
                        v_val_2263_ = leanh::lean_ctor_get(v___x_2262_, 0);
                        leanh::lean_inc(v_val_2263_);
                        leanh::lean_dec_ref_known(v___x_2262_, 1);
                        v___x_2264_ = lean_array_push(v_snd_2249_, v_val_2263_);
                        v_toRename_2255_ = v___x_2264_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2262_);
                        v_toRename_2255_ = v_snd_2249_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2253_);
                    leanh::lean_del_object(v___x_2251_);
                    v___x_2265_ = l_Lean_LocalDecl_fvarId(v_val_2247_);
                    v___x_2266_ = lean_array_push(v_snd_2249_, v___x_2265_);
                    v___x_2267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2267_, 0, v_fst_2248_);
                    leanh::lean_ctor_set(v___x_2267_, 1, v___x_2266_);
                    v_a_2239_ = v___x_2267_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2256_ = l_Lean_LocalDecl_fvarId(v_val_2247_);
                v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2248_, v___x_2253_, v___x_2256_);
                if v_isShared_2252_ == 0 {
                    leanh::lean_ctor_set(v___x_2251_, 1, v_toRename_2255_);
                    leanh::lean_ctor_set(v___x_2251_, 0, v___x_2257_);
                    v___x_2259_ = v___x_2251_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_toRename_2255_);
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
    mut v_as_2271_: *mut leanh::LeanObject,
    mut v_sz_2272_: *mut leanh::LeanObject,
    mut v_i_2273_: *mut leanh::LeanObject,
    mut v_b_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2280_: usize = 0;
    let mut v_i_boxed_2281_: usize = 0;
    let mut v_res_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2280_ = leanh::lean_unbox_usize(v_sz_2272_);
    leanh::lean_dec(v_sz_2272_);
    v_i_boxed_2281_ = leanh::lean_unbox_usize(v_i_2273_);
    leanh::lean_dec(v_i_2273_);
    v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(v_as_2271_, v_sz_boxed_2280_, v_i_boxed_2281_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
    leanh::lean_dec(v___y_2278_);
    leanh::lean_dec_ref(v___y_2277_);
    leanh::lean_dec(v___y_2276_);
    leanh::lean_dec_ref(v___y_2275_);
    leanh::lean_dec_ref(v_as_2271_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(
    mut v_init_2283_: *mut leanh::LeanObject,
    mut v_n_2284_: *mut leanh::LeanObject,
    mut v_b_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v_fst_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_vs_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2323_: usize = 0;
    let mut v___x_2324_: usize = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v_fst_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_a_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_2284_) == 0 {
                    v_cs_2291_ = leanh::lean_ctor_get(v_n_2284_, 0);
                    v___x_2292_ = leanh::lean_box(0);
                    v___x_2293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
                    leanh::lean_ctor_set(v___x_2293_, 1, v_b_2285_);
                    v_sz_2294_ = lean_array_size(v_cs_2291_);
                    v___x_2295_ = 0usize;
                    v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8(v_init_2283_, v_cs_2291_, v_sz_2294_, v___x_2295_, v___x_2293_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
                    if leanh::lean_obj_tag(v___x_2296_) == 0 {
                        v_a_2297_ = leanh::lean_ctor_get(v___x_2296_, 0);
                        v_isSharedCheck_2311_ =
                            (!leanh::lean_is_exclusive(v___x_2296_)) as u8;
                        if v_isSharedCheck_2311_ == 0 {
                            v___x_2299_ = v___x_2296_;
                            v_isShared_2300_ = v_isSharedCheck_2311_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2297_);
                            leanh::lean_dec(v___x_2296_);
                            v___x_2299_ = leanh::lean_box(0);
                            v_isShared_2300_ = v_isSharedCheck_2311_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2312_ = leanh::lean_ctor_get(v___x_2296_, 0);
                        v_isSharedCheck_2319_ =
                            (!leanh::lean_is_exclusive(v___x_2296_)) as u8;
                        if v_isSharedCheck_2319_ == 0 {
                            v___x_2314_ = v___x_2296_;
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2312_);
                            leanh::lean_dec(v___x_2296_);
                            v___x_2314_ = leanh::lean_box(0);
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2320_ = leanh::lean_ctor_get(v_n_2284_, 0);
                    v___x_2321_ = leanh::lean_box(0);
                    v___x_2322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
                    leanh::lean_ctor_set(v___x_2322_, 1, v_b_2285_);
                    v_sz_2323_ = lean_array_size(v_vs_2320_);
                    v___x_2324_ = 0usize;
                    v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9(v_vs_2320_, v_sz_2323_, v___x_2324_, v___x_2322_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
                    if leanh::lean_obj_tag(v___x_2325_) == 0 {
                        v_a_2326_ = leanh::lean_ctor_get(v___x_2325_, 0);
                        v_isSharedCheck_2340_ =
                            (!leanh::lean_is_exclusive(v___x_2325_)) as u8;
                        if v_isSharedCheck_2340_ == 0 {
                            v___x_2328_ = v___x_2325_;
                            v_isShared_2329_ = v_isSharedCheck_2340_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2326_);
                            leanh::lean_dec(v___x_2325_);
                            v___x_2328_ = leanh::lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2340_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2341_ = leanh::lean_ctor_get(v___x_2325_, 0);
                        v_isSharedCheck_2348_ =
                            (!leanh::lean_is_exclusive(v___x_2325_)) as u8;
                        if v_isSharedCheck_2348_ == 0 {
                            v___x_2343_ = v___x_2325_;
                            v_isShared_2344_ = v_isSharedCheck_2348_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2341_);
                            leanh::lean_dec(v___x_2325_);
                            v___x_2343_ = leanh::lean_box(0);
                            v_isShared_2344_ = v_isSharedCheck_2348_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2301_ = leanh::lean_ctor_get(v_a_2297_, 0);
                if leanh::lean_obj_tag(v_fst_2301_) == 0 {
                    v_snd_2302_ = leanh::lean_ctor_get(v_a_2297_, 1);
                    leanh::lean_inc(v_snd_2302_);
                    leanh::lean_dec(v_a_2297_);
                    v___x_2303_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2303_, 0, v_snd_2302_);
                    if v_isShared_2300_ == 0 {
                        leanh::lean_ctor_set(v___x_2299_, 0, v___x_2303_);
                        v___x_2305_ = v___x_2299_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
                        v___x_2305_ = v_reuseFailAlloc_2306_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2301_);
                    leanh::lean_dec(v_a_2297_);
                    v_val_2307_ = leanh::lean_ctor_get(v_fst_2301_, 0);
                    leanh::lean_inc(v_val_2307_);
                    leanh::lean_dec_ref_known(v_fst_2301_, 1);
                    if v_isShared_2300_ == 0 {
                        leanh::lean_ctor_set(v___x_2299_, 0, v_val_2307_);
                        v___x_2309_ = v___x_2299_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2310_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_val_2307_);
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
                    v_reuseFailAlloc_2318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2317_;
            }
            6 => {
                v_fst_2330_ = leanh::lean_ctor_get(v_a_2326_, 0);
                if leanh::lean_obj_tag(v_fst_2330_) == 0 {
                    v_snd_2331_ = leanh::lean_ctor_get(v_a_2326_, 1);
                    leanh::lean_inc(v_snd_2331_);
                    leanh::lean_dec(v_a_2326_);
                    v___x_2332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2332_, 0, v_snd_2331_);
                    if v_isShared_2329_ == 0 {
                        leanh::lean_ctor_set(v___x_2328_, 0, v___x_2332_);
                        v___x_2334_ = v___x_2328_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
                        v___x_2334_ = v_reuseFailAlloc_2335_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2330_);
                    leanh::lean_dec(v_a_2326_);
                    v_val_2336_ = leanh::lean_ctor_get(v_fst_2330_, 0);
                    leanh::lean_inc(v_val_2336_);
                    leanh::lean_dec_ref_known(v_fst_2330_, 1);
                    if v_isShared_2329_ == 0 {
                        leanh::lean_ctor_set(v___x_2328_, 0, v_val_2336_);
                        v___x_2338_ = v___x_2328_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2336_);
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
                    v_reuseFailAlloc_2347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
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
    mut v_init_2349_: *mut leanh::LeanObject,
    mut v_as_2350_: *mut leanh::LeanObject,
    mut v_sz_2351_: usize,
    mut v_i_2352_: usize,
    mut v_b_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v_a_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v_reuseFailAlloc_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_unused_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2359_ = lean_usize_dec_lt(v_i_2352_, v_sz_2351_);
                if v___x_2359_ == 0 {
                    v___x_2360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2360_, 0, v_b_2353_);
                    return v___x_2360_;
                } else {
                    v_snd_2361_ = leanh::lean_ctor_get(v_b_2353_, 1);
                    v_isSharedCheck_2395_ = (!leanh::lean_is_exclusive(v_b_2353_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v_unused_2396_ = leanh::lean_ctor_get(v_b_2353_, 0);
                        leanh::lean_dec(v_unused_2396_);
                        v___x_2363_ = v_b_2353_;
                        v_isShared_2364_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2361_);
                        leanh::lean_dec(v_b_2353_);
                        v___x_2363_ = leanh::lean_box(0);
                        v_isShared_2364_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2365_ = lean_array_uget_borrowed(v_as_2350_, v_i_2352_);
                leanh::lean_inc(v_snd_2361_);
                v___x_2366_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2349_, v_a_2365_, v_snd_2361_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
                if leanh::lean_obj_tag(v___x_2366_) == 0 {
                    v_a_2367_ = leanh::lean_ctor_get(v___x_2366_, 0);
                    v_isSharedCheck_2386_ = (!leanh::lean_is_exclusive(v___x_2366_)) as u8;
                    if v_isSharedCheck_2386_ == 0 {
                        v___x_2369_ = v___x_2366_;
                        v_isShared_2370_ = v_isSharedCheck_2386_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2367_);
                        leanh::lean_dec(v___x_2366_);
                        v___x_2369_ = leanh::lean_box(0);
                        v_isShared_2370_ = v_isSharedCheck_2386_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2363_);
                    leanh::lean_dec(v_snd_2361_);
                    v_a_2387_ = leanh::lean_ctor_get(v___x_2366_, 0);
                    v_isSharedCheck_2394_ = (!leanh::lean_is_exclusive(v___x_2366_)) as u8;
                    if v_isSharedCheck_2394_ == 0 {
                        v___x_2389_ = v___x_2366_;
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2387_);
                        leanh::lean_dec(v___x_2366_);
                        v___x_2389_ = leanh::lean_box(0);
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2367_) == 0 {
                    v___x_2371_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2371_, 0, v_a_2367_);
                    if v_isShared_2364_ == 0 {
                        leanh::lean_ctor_set(v___x_2363_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2363_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2371_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2361_);
                        v___x_2373_ = v_reuseFailAlloc_2377_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2369_);
                    leanh::lean_dec(v_snd_2361_);
                    v_a_2378_ = leanh::lean_ctor_get(v_a_2367_, 0);
                    leanh::lean_inc(v_a_2378_);
                    leanh::lean_dec_ref_known(v_a_2367_, 1);
                    v___x_2379_ = leanh::lean_box(0);
                    if v_isShared_2364_ == 0 {
                        leanh::lean_ctor_set(v___x_2363_, 1, v_a_2378_);
                        leanh::lean_ctor_set(v___x_2363_, 0, v___x_2379_);
                        v___x_2381_ = v___x_2363_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2379_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2378_);
                        v___x_2381_ = v_reuseFailAlloc_2385_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2370_ == 0 {
                    leanh::lean_ctor_set(v___x_2369_, 0, v___x_2373_);
                    v___x_2375_ = v___x_2369_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
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
                    v_reuseFailAlloc_2393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
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
    mut v_init_2397_: *mut leanh::LeanObject,
    mut v_as_2398_: *mut leanh::LeanObject,
    mut v_sz_2399_: *mut leanh::LeanObject,
    mut v_i_2400_: *mut leanh::LeanObject,
    mut v_b_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2407_: usize = 0;
    let mut v_i_boxed_2408_: usize = 0;
    let mut v_res_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2407_ = leanh::lean_unbox_usize(v_sz_2399_);
    leanh::lean_dec(v_sz_2399_);
    v_i_boxed_2408_ = leanh::lean_unbox_usize(v_i_2400_);
    leanh::lean_dec(v_i_2400_);
    v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__8(v_init_2397_, v_as_2398_, v_sz_boxed_2407_, v_i_boxed_2408_, v_b_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    leanh::lean_dec(v___y_2405_);
    leanh::lean_dec_ref(v___y_2404_);
    leanh::lean_dec(v___y_2403_);
    leanh::lean_dec_ref(v___y_2402_);
    leanh::lean_dec_ref(v_as_2398_);
    leanh::lean_dec_ref(v_init_2397_);
    return v_res_2409_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6___boxed(
    mut v_init_2410_: *mut leanh::LeanObject,
    mut v_n_2411_: *mut leanh::LeanObject,
    mut v_b_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2410_, v_n_2411_, v_b_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    leanh::lean_dec(v___y_2416_);
    leanh::lean_dec_ref(v___y_2415_);
    leanh::lean_dec(v___y_2414_);
    leanh::lean_dec_ref(v___y_2413_);
    leanh::lean_dec_ref(v_n_2411_);
    leanh::lean_dec_ref(v_init_2410_);
    return v_res_2418_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(
    mut v_t_2419_: *mut leanh::LeanObject,
    mut v_init_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v_a_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v_fst_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_a_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_a_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2426_ = leanh::lean_ctor_get(v_t_2419_, 0);
                v_tail_2427_ = leanh::lean_ctor_get(v_t_2419_, 1);
                leanh::lean_inc_ref(v_init_2420_);
                v___x_2428_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6(v_init_2420_, v_root_2426_, v_init_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
                leanh::lean_dec_ref(v_init_2420_);
                if leanh::lean_obj_tag(v___x_2428_) == 0 {
                    v_a_2429_ = leanh::lean_ctor_get(v___x_2428_, 0);
                    v_isSharedCheck_2465_ = (!leanh::lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2465_ == 0 {
                        v___x_2431_ = v___x_2428_;
                        v_isShared_2432_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2429_);
                        leanh::lean_dec(v___x_2428_);
                        v___x_2431_ = leanh::lean_box(0);
                        v_isShared_2432_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2466_ = leanh::lean_ctor_get(v___x_2428_, 0);
                    v_isSharedCheck_2473_ = (!leanh::lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2473_ == 0 {
                        v___x_2468_ = v___x_2428_;
                        v_isShared_2469_ = v_isSharedCheck_2473_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2466_);
                        leanh::lean_dec(v___x_2428_);
                        v___x_2468_ = leanh::lean_box(0);
                        v_isShared_2469_ = v_isSharedCheck_2473_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2429_) == 0 {
                    v_a_2433_ = leanh::lean_ctor_get(v_a_2429_, 0);
                    leanh::lean_inc(v_a_2433_);
                    leanh::lean_dec_ref_known(v_a_2429_, 1);
                    if v_isShared_2432_ == 0 {
                        leanh::lean_ctor_set(v___x_2431_, 0, v_a_2433_);
                        v___x_2435_ = v___x_2431_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2436_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2433_);
                        v___x_2435_ = v_reuseFailAlloc_2436_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2431_);
                    v_a_2437_ = leanh::lean_ctor_get(v_a_2429_, 0);
                    leanh::lean_inc(v_a_2437_);
                    leanh::lean_dec_ref_known(v_a_2429_, 1);
                    v___x_2438_ = leanh::lean_box(0);
                    v___x_2439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                    leanh::lean_ctor_set(v___x_2439_, 1, v_a_2437_);
                    v_sz_2440_ = lean_array_size(v_tail_2427_);
                    v___x_2441_ = 0usize;
                    v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7(v_tail_2427_, v_sz_2440_, v___x_2441_, v___x_2439_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
                    if leanh::lean_obj_tag(v___x_2442_) == 0 {
                        v_a_2443_ = leanh::lean_ctor_get(v___x_2442_, 0);
                        v_isSharedCheck_2456_ =
                            (!leanh::lean_is_exclusive(v___x_2442_)) as u8;
                        if v_isSharedCheck_2456_ == 0 {
                            v___x_2445_ = v___x_2442_;
                            v_isShared_2446_ = v_isSharedCheck_2456_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2443_);
                            leanh::lean_dec(v___x_2442_);
                            v___x_2445_ = leanh::lean_box(0);
                            v_isShared_2446_ = v_isSharedCheck_2456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2457_ = leanh::lean_ctor_get(v___x_2442_, 0);
                        v_isSharedCheck_2464_ =
                            (!leanh::lean_is_exclusive(v___x_2442_)) as u8;
                        if v_isSharedCheck_2464_ == 0 {
                            v___x_2459_ = v___x_2442_;
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2457_);
                            leanh::lean_dec(v___x_2442_);
                            v___x_2459_ = leanh::lean_box(0);
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
                v_fst_2447_ = leanh::lean_ctor_get(v_a_2443_, 0);
                if leanh::lean_obj_tag(v_fst_2447_) == 0 {
                    v_snd_2448_ = leanh::lean_ctor_get(v_a_2443_, 1);
                    leanh::lean_inc(v_snd_2448_);
                    leanh::lean_dec(v_a_2443_);
                    if v_isShared_2446_ == 0 {
                        leanh::lean_ctor_set(v___x_2445_, 0, v_snd_2448_);
                        v___x_2450_ = v___x_2445_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_snd_2448_);
                        v___x_2450_ = v_reuseFailAlloc_2451_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2447_);
                    leanh::lean_dec(v_a_2443_);
                    v_val_2452_ = leanh::lean_ctor_get(v_fst_2447_, 0);
                    leanh::lean_inc(v_val_2452_);
                    leanh::lean_dec_ref_known(v_fst_2447_, 1);
                    if v_isShared_2446_ == 0 {
                        leanh::lean_ctor_set(v___x_2445_, 0, v_val_2452_);
                        v___x_2454_ = v___x_2445_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_val_2452_);
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
                    v_reuseFailAlloc_2463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
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
                    v_reuseFailAlloc_2472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
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
    mut v_t_2474_: *mut leanh::LeanObject,
    mut v_init_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
    mut v___y_2479_: *mut leanh::LeanObject,
    mut v___y_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(v_t_2474_, v_init_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
    leanh::lean_dec(v___y_2479_);
    leanh::lean_dec_ref(v___y_2478_);
    leanh::lean_dec(v___y_2477_);
    leanh::lean_dec_ref(v___y_2476_);
    leanh::lean_dec_ref(v_t_2474_);
    return v_res_2481_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(
    mut v___x_2482_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_2483_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_2484_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    leanh::lean_inc_ref(v___x_2482_);
    v___x_2485_ = l_Lean_LocalContext_get_x21(v___x_2482_, v_fvarId_u2081_2483_);
    v___x_2486_ = l_Lean_LocalDecl_index(v___x_2485_);
    leanh::lean_dec_ref(v___x_2485_);
    v___x_2487_ = l_Lean_LocalContext_get_x21(v___x_2482_, v_fvarId_u2082_2484_);
    v___x_2488_ = l_Lean_LocalDecl_index(v___x_2487_);
    leanh::lean_dec_ref(v___x_2487_);
    v___x_2489_ = lean_nat_dec_lt(v___x_2486_, v___x_2488_);
    leanh::lean_dec(v___x_2488_);
    leanh::lean_dec(v___x_2486_);
    return v___x_2489_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0___boxed(
    mut v___x_2490_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_2491_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2493_: u8 = 0;
    let mut v_r_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2490_, v_fvarId_u2081_2491_, v_fvarId_u2082_2492_);
    v_r_2494_ = leanh::lean_box((v_res_2493_) as usize);
    return v_r_2494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(
    mut v___x_2495_: *mut leanh::LeanObject,
    mut v_hi_2496_: *mut leanh::LeanObject,
    mut v_pivot_2497_: *mut leanh::LeanObject,
    mut v_as_2498_: *mut leanh::LeanObject,
    mut v_i_2499_: *mut leanh::LeanObject,
    mut v_k_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_nat_dec_lt(v_k_2500_, v_hi_2496_);
                if v___x_2501_ == 0 {
                    leanh::lean_dec(v_k_2500_);
                    leanh::lean_dec(v_pivot_2497_);
                    leanh::lean_dec_ref(v___x_2495_);
                    v___x_2502_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_hi_2496_);
                    v___x_2503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2503_, 0, v_i_2499_);
                    leanh::lean_ctor_set(v___x_2503_, 1, v___x_2502_);
                    return v___x_2503_;
                } else {
                    v___x_2504_ = lean_array_fget_borrowed(v_as_2498_, v_k_2500_);
                    leanh::lean_inc(v___x_2504_);
                    leanh::lean_inc_ref_n(v___x_2495_, 2);
                    v___x_2505_ = l_Lean_LocalContext_get_x21(v___x_2495_, v___x_2504_);
                    v___x_2506_ = l_Lean_LocalDecl_index(v___x_2505_);
                    leanh::lean_dec_ref(v___x_2505_);
                    leanh::lean_inc(v_pivot_2497_);
                    v___x_2507_ = l_Lean_LocalContext_get_x21(v___x_2495_, v_pivot_2497_);
                    v___x_2508_ = l_Lean_LocalDecl_index(v___x_2507_);
                    leanh::lean_dec_ref(v___x_2507_);
                    v___x_2509_ = lean_nat_dec_lt(v___x_2506_, v___x_2508_);
                    leanh::lean_dec(v___x_2508_);
                    leanh::lean_dec(v___x_2506_);
                    if v___x_2509_ == 0 {
                        v___x_2510_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2511_ = lean_nat_add(v_k_2500_, v___x_2510_);
                        leanh::lean_dec(v_k_2500_);
                        v_k_2500_ = v___x_2511_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2513_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_k_2500_);
                        v___x_2514_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2515_ = lean_nat_add(v_i_2499_, v___x_2514_);
                        leanh::lean_dec(v_i_2499_);
                        v___x_2516_ = lean_nat_add(v_k_2500_, v___x_2514_);
                        leanh::lean_dec(v_k_2500_);
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
    mut v___x_2518_: *mut leanh::LeanObject,
    mut v_hi_2519_: *mut leanh::LeanObject,
    mut v_pivot_2520_: *mut leanh::LeanObject,
    mut v_as_2521_: *mut leanh::LeanObject,
    mut v_i_2522_: *mut leanh::LeanObject,
    mut v_k_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_2518_, v_hi_2519_, v_pivot_2520_, v_as_2521_, v_i_2522_, v_k_2523_);
    leanh::lean_dec(v_hi_2519_);
    return v_res_2524_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(
    mut v___x_2525_: *mut leanh::LeanObject,
    mut v_n_2526_: *mut leanh::LeanObject,
    mut v_as_2527_: *mut leanh::LeanObject,
    mut v_lo_2528_: *mut leanh::LeanObject,
    mut v_hi_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2541_ = lean_nat_dec_lt(v_lo_2528_, v_hi_2529_);
                if v___x_2541_ == 0 {
                    leanh::lean_dec(v_lo_2528_);
                    leanh::lean_dec_ref(v___x_2525_);
                    return v_as_2527_;
                } else {
                    v___x_2542_ = lean_nat_add(v_lo_2528_, v_hi_2529_);
                    v___x_2543_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2544_ = lean_nat_shiftr(v___x_2542_, v___x_2543_);
                    leanh::lean_dec(v___x_2542_);
                    v___x_2557_ = lean_array_fget_borrowed(v_as_2527_, v_mid_2544_);
                    v___x_2558_ = lean_array_fget_borrowed(v_as_2527_, v_lo_2528_);
                    leanh::lean_inc(v___x_2558_);
                    leanh::lean_inc(v___x_2557_);
                    leanh::lean_inc_ref(v___x_2525_);
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
                leanh::lean_inc_n(v_lo_2528_, 2);
                leanh::lean_inc_ref(v___x_2525_);
                v___x_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_2525_, v_hi_2529_, v_pivot_2532_, v___y_2531_, v_lo_2528_, v_lo_2528_);
                v_fst_2534_ = leanh::lean_ctor_get(v___x_2533_, 0);
                leanh::lean_inc(v_fst_2534_);
                v_snd_2535_ = leanh::lean_ctor_get(v___x_2533_, 1);
                leanh::lean_inc(v_snd_2535_);
                leanh::lean_dec_ref(v___x_2533_);
                v___x_2536_ = lean_nat_dec_le(v_hi_2529_, v_fst_2534_);
                if v___x_2536_ == 0 {
                    leanh::lean_inc_ref(v___x_2525_);
                    v___x_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_2525_, v_n_2526_, v_snd_2535_, v_lo_2528_, v_fst_2534_);
                    v___x_2538_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2539_ = lean_nat_add(v_fst_2534_, v___x_2538_);
                    leanh::lean_dec(v_fst_2534_);
                    v_as_2527_ = v___x_2537_;
                    v_lo_2528_ = v___x_2539_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2534_);
                    leanh::lean_dec(v_lo_2528_);
                    leanh::lean_dec_ref(v___x_2525_);
                    return v_snd_2535_;
                }
            }
            2 => {
                v___x_2547_ = lean_array_fget_borrowed(v___y_2546_, v_mid_2544_);
                v___x_2548_ = lean_array_fget_borrowed(v___y_2546_, v_hi_2529_);
                leanh::lean_inc(v___x_2548_);
                leanh::lean_inc(v___x_2547_);
                leanh::lean_inc_ref(v___x_2525_);
                v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg___lam__0(v___x_2525_, v___x_2547_, v___x_2548_);
                if v___x_2549_ == 0 {
                    leanh::lean_dec(v_mid_2544_);
                    v___y_2531_ = v___y_2546_;
                    state = 1;
                    continue;
                } else {
                    v___x_2550_ = lean_array_fswap(v___y_2546_, v_mid_2544_, v_hi_2529_);
                    leanh::lean_dec(v_mid_2544_);
                    v___y_2531_ = v___x_2550_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2553_ = lean_array_fget_borrowed(v___y_2552_, v_hi_2529_);
                v___x_2554_ = lean_array_fget_borrowed(v___y_2552_, v_lo_2528_);
                leanh::lean_inc(v___x_2554_);
                leanh::lean_inc(v___x_2553_);
                leanh::lean_inc_ref(v___x_2525_);
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
    mut v___x_2561_: *mut leanh::LeanObject,
    mut v_n_2562_: *mut leanh::LeanObject,
    mut v_as_2563_: *mut leanh::LeanObject,
    mut v_lo_2564_: *mut leanh::LeanObject,
    mut v_hi_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_2561_, v_n_2562_, v_as_2563_, v_lo_2564_, v_hi_2565_);
    leanh::lean_dec(v_hi_2565_);
    leanh::lean_dec(v_n_2562_);
    return v_res_2566_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(
    mut v_m_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u64 = 0;
    let mut v_hash_2587_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2569_ = leanh::lean_ctor_get(v_m_2567_, 1);
                v___x_2570_ = lean_array_get_size(v_buckets_2569_);
                if leanh::lean_obj_tag(v_a_2568_) == 0 {
                    v___x_2586_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg___closed__0);
                    v___y_2572_ = v___x_2586_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2587_ = leanh::lean_ctor_get_uint64(
                        v_a_2568_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2590_: u8 = 0;
    let mut v_r_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v_m_2588_, v_a_2589_);
    leanh::lean_dec(v_a_2589_);
    leanh::lean_dec_ref(v_m_2588_);
    v_r_2591_ = leanh::lean_box((v_res_2590_) as usize);
    return v_r_2591_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(
    mut v___x_2592_: *mut leanh::LeanObject,
    mut v___x_2593_: *mut leanh::LeanObject,
    mut v_baseName_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2597_ = leanh::lean_ctor_get(v_a_2595_, 0);
                v_snd_2598_ = leanh::lean_ctor_get(v_a_2595_, 1);
                v_isSharedCheck_2615_ = (!leanh::lean_is_exclusive(v_a_2595_)) as u8;
                if v_isSharedCheck_2615_ == 0 {
                    v___x_2600_ = v_a_2595_;
                    v_isShared_2601_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2598_);
                    leanh::lean_inc(v_fst_2597_);
                    leanh::lean_dec(v_a_2595_);
                    v___x_2600_ = leanh::lean_box(0);
                    v_isShared_2601_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v___x_2592_, v_fst_2597_);
                if v___x_2607_ == 0 {
                    leanh::lean_dec(v_baseName_2594_);
                    state = 2;
                    continue;
                } else {
                    v___x_2608_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2609_ = lean_nat_dec_eq(v___x_2593_, v___x_2608_);
                    if v___x_2609_ == 0 {
                        leanh::lean_del_object(v___x_2600_);
                        leanh::lean_dec(v_fst_2597_);
                        v___x_2610_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2611_ = lean_nat_add(v_snd_2598_, v___x_2610_);
                        leanh::lean_dec(v_snd_2598_);
                        leanh::lean_inc(v___x_2611_);
                        leanh::lean_inc(v_baseName_2594_);
                        v___x_2612_ = lean_name_append_index_after(v_baseName_2594_, v___x_2611_);
                        v___x_2613_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                        leanh::lean_ctor_set(v___x_2613_, 1, v___x_2611_);
                        v_a_2595_ = v___x_2613_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_baseName_2594_);
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
                    v_reuseFailAlloc_2606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_fst_2597_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_snd_2598_);
                    v___x_2604_ = v_reuseFailAlloc_2606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2605_, 0, v___x_2604_);
                return v___x_2605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg___boxed(
    mut v___x_2616_: *mut leanh::LeanObject,
    mut v___x_2617_: *mut leanh::LeanObject,
    mut v_baseName_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v___y_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2621_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v___x_2616_, v___x_2617_, v_baseName_2618_, v_a_2619_);
    leanh::lean_dec(v___x_2617_);
    leanh::lean_dec_ref(v___x_2616_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21___redArg(
    mut v_x_2622_: *mut leanh::LeanObject,
    mut v_x_2623_: *mut leanh::LeanObject,
    mut v_x_2624_: *mut leanh::LeanObject,
    mut v_x_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2626_ = leanh::lean_ctor_get(v_x_2622_, 0);
                v_vs_2627_ = leanh::lean_ctor_get(v_x_2622_, 1);
                v_isSharedCheck_2651_ = (!leanh::lean_is_exclusive(v_x_2622_)) as u8;
                if v_isSharedCheck_2651_ == 0 {
                    v___x_2629_ = v_x_2622_;
                    v_isShared_2630_ = v_isSharedCheck_2651_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2627_);
                    leanh::lean_inc(v_ks_2626_);
                    leanh::lean_dec(v_x_2622_);
                    v___x_2629_ = leanh::lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2631_ = lean_array_get_size(v_ks_2626_);
                v___x_2632_ = lean_nat_dec_lt(v_x_2623_, v___x_2631_);
                if v___x_2632_ == 0 {
                    leanh::lean_dec(v_x_2623_);
                    v___x_2633_ = lean_array_push(v_ks_2626_, v_x_2624_);
                    v___x_2634_ = lean_array_push(v_vs_2627_, v_x_2625_);
                    if v_isShared_2630_ == 0 {
                        leanh::lean_ctor_set(v___x_2629_, 1, v___x_2634_);
                        leanh::lean_ctor_set(v___x_2629_, 0, v___x_2633_);
                        v___x_2636_ = v___x_2629_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2637_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2633_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2634_);
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
                            v_reuseFailAlloc_2645_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_ks_2626_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_vs_2627_);
                            v___x_2641_ = v_reuseFailAlloc_2645_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2646_ = lean_array_fset(v_ks_2626_, v_x_2623_, v_x_2624_);
                        v___x_2647_ = lean_array_fset(v_vs_2627_, v_x_2623_, v_x_2625_);
                        leanh::lean_dec(v_x_2623_);
                        if v_isShared_2630_ == 0 {
                            leanh::lean_ctor_set(v___x_2629_, 1, v___x_2647_);
                            leanh::lean_ctor_set(v___x_2629_, 0, v___x_2646_);
                            v___x_2649_ = v___x_2629_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2650_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2646_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2647_);
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
                v___x_2642_ = leanh::lean_unsigned_to_nat(1);
                v___x_2643_ = lean_nat_add(v_x_2623_, v___x_2642_);
                leanh::lean_dec(v_x_2623_);
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
    mut v_n_2652_: *mut leanh::LeanObject,
    mut v_k_2653_: *mut leanh::LeanObject,
    mut v_v_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_2661_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__0);
    v___x_2662_ = lean_usize_sub(v___x_2661_, v___x_2660_);
    return v___x_2662_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2663_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(
    mut v_x_2664_: *mut leanh::LeanObject,
    mut v_x_2665_: usize,
    mut v_x_2666_: usize,
    mut v_x_2667_: *mut leanh::LeanObject,
    mut v_x_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: usize = 0;
    let mut v___x_2672_: usize = 0;
    let mut v___x_2673_: usize = 0;
    let mut v_j_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_v_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_node_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_unused_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: u8 = 0;
    let mut v_ks_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: usize = 0;
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2664_) == 0 {
                    v_es_2669_ = leanh::lean_ctor_get(v_x_2664_, 0);
                    v___x_2670_ = 5usize;
                    v___x_2671_ = 1usize;
                    v___x_2672_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1);
                    v___x_2673_ = lean_usize_land(v_x_2665_, v___x_2672_);
                    v_j_2674_ = lean_usize_to_nat(v___x_2673_);
                    v___x_2675_ = lean_array_get_size(v_es_2669_);
                    v___x_2676_ = lean_nat_dec_lt(v_j_2674_, v___x_2675_);
                    if v___x_2676_ == 0 {
                        leanh::lean_dec(v_j_2674_);
                        leanh::lean_dec(v_x_2668_);
                        leanh::lean_dec(v_x_2667_);
                        return v_x_2664_;
                    } else {
                        leanh::lean_inc_ref(v_es_2669_);
                        v_isSharedCheck_2713_ = (!leanh::lean_is_exclusive(v_x_2664_)) as u8;
                        if v_isSharedCheck_2713_ == 0 {
                            v_unused_2714_ = leanh::lean_ctor_get(v_x_2664_, 0);
                            leanh::lean_dec(v_unused_2714_);
                            v___x_2678_ = v_x_2664_;
                            v_isShared_2679_ = v_isSharedCheck_2713_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2664_);
                            v___x_2678_ = leanh::lean_box(0);
                            v_isShared_2679_ = v_isSharedCheck_2713_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2715_ = leanh::lean_ctor_get(v_x_2664_, 0);
                    v_vs_2716_ = leanh::lean_ctor_get(v_x_2664_, 1);
                    v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2736_ == 0 {
                        v___x_2718_ = v_x_2664_;
                        v_isShared_2719_ = v_isSharedCheck_2736_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2716_);
                        leanh::lean_inc(v_ks_2715_);
                        leanh::lean_dec(v_x_2664_);
                        v___x_2718_ = leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2736_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2680_ = lean_array_fget(v_es_2669_, v_j_2674_);
                v___x_2681_ = leanh::lean_box(0);
                v_xs_x27_2682_ = lean_array_fset(v_es_2669_, v_j_2674_, v___x_2681_);
                match leanh::lean_obj_tag(v_v_2680_) {
                    0 => {
                        v_key_2689_ = leanh::lean_ctor_get(v_v_2680_, 0);
                        v_val_2690_ = leanh::lean_ctor_get(v_v_2680_, 1);
                        v_isSharedCheck_2700_ = (!leanh::lean_is_exclusive(v_v_2680_)) as u8;
                        if v_isSharedCheck_2700_ == 0 {
                            v___x_2692_ = v_v_2680_;
                            v_isShared_2693_ = v_isSharedCheck_2700_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2690_);
                            leanh::lean_inc(v_key_2689_);
                            leanh::lean_dec(v_v_2680_);
                            v___x_2692_ = leanh::lean_box(0);
                            v_isShared_2693_ = v_isSharedCheck_2700_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2701_ = leanh::lean_ctor_get(v_v_2680_, 0);
                        v_isSharedCheck_2711_ = (!leanh::lean_is_exclusive(v_v_2680_)) as u8;
                        if v_isSharedCheck_2711_ == 0 {
                            v___x_2703_ = v_v_2680_;
                            v_isShared_2704_ = v_isSharedCheck_2711_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2701_);
                            leanh::lean_dec(v_v_2680_);
                            v___x_2703_ = leanh::lean_box(0);
                            v_isShared_2704_ = v_isSharedCheck_2711_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2712_, 0, v_x_2667_);
                        leanh::lean_ctor_set(v___x_2712_, 1, v_x_2668_);
                        v___y_2684_ = v___x_2712_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = lean_array_fset(v_xs_x27_2682_, v_j_2674_, v___y_2684_);
                leanh::lean_dec(v_j_2674_);
                if v_isShared_2679_ == 0 {
                    leanh::lean_ctor_set(v___x_2678_, 0, v___x_2685_);
                    v___x_2687_ = v___x_2678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
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
                    leanh::lean_del_object(v___x_2692_);
                    v___x_2695_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2689_,
                        v_val_2690_,
                        v_x_2667_,
                        v_x_2668_,
                    );
                    v___x_2696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2696_, 0, v___x_2695_);
                    v___y_2684_ = v___x_2696_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2690_);
                    leanh::lean_dec(v_key_2689_);
                    if v_isShared_2693_ == 0 {
                        leanh::lean_ctor_set(v___x_2692_, 1, v_x_2668_);
                        leanh::lean_ctor_set(v___x_2692_, 0, v_x_2667_);
                        v___x_2698_ = v___x_2692_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_x_2667_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_x_2668_);
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
                    leanh::lean_ctor_set(v___x_2703_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2703_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
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
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_ks_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_vs_2716_);
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
                    v___x_2733_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
                    leanh::lean_dec(v___x_2732_);
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
                    v_ks_2725_ = leanh::lean_ctor_get(v_newNode_2722_, 0);
                    leanh::lean_inc_ref(v_ks_2725_);
                    v_vs_2726_ = leanh::lean_ctor_get(v_newNode_2722_, 1);
                    leanh::lean_inc_ref(v_vs_2726_);
                    leanh::lean_dec_ref(v_newNode_2722_);
                    v___x_2727_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2728_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2);
                    v___x_2729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_x_2666_, v_ks_2725_, v_vs_2726_, v___x_2727_, v___x_2728_);
                    leanh::lean_dec_ref(v_vs_2726_);
                    leanh::lean_dec_ref(v_ks_2725_);
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
    mut v_keys_2738_: *mut leanh::LeanObject,
    mut v_vals_2739_: *mut leanh::LeanObject,
    mut v_i_2740_: *mut leanh::LeanObject,
    mut v_entries_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v_k_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u64 = 0;
    let mut v_h_2747_: usize = 0;
    let mut v___x_2748_: usize = 0;
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: usize = 0;
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v_h_2753_: usize = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2742_ = lean_array_get_size(v_keys_2738_);
                v___x_2743_ = lean_nat_dec_lt(v_i_2740_, v___x_2742_);
                if v___x_2743_ == 0 {
                    leanh::lean_dec(v_i_2740_);
                    return v_entries_2741_;
                } else {
                    v_k_2744_ = lean_array_fget_borrowed(v_keys_2738_, v_i_2740_);
                    v_v_2745_ = lean_array_fget_borrowed(v_vals_2739_, v_i_2740_);
                    v___x_2746_ = l_Lean_instHashableFVarId_hash(v_k_2744_);
                    v_h_2747_ = lean_uint64_to_usize(v___x_2746_);
                    v___x_2748_ = 5usize;
                    v___x_2749_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2750_ = 1usize;
                    v___x_2751_ = lean_usize_sub(v_depth_2737_, v___x_2750_);
                    v___x_2752_ = lean_usize_mul(v___x_2748_, v___x_2751_);
                    v_h_2753_ = lean_usize_shift_right(v_h_2747_, v___x_2752_);
                    v___x_2754_ = lean_nat_add(v_i_2740_, v___x_2749_);
                    leanh::lean_dec(v_i_2740_);
                    leanh::lean_inc(v_v_2745_);
                    leanh::lean_inc(v_k_2744_);
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
    mut v_depth_2757_: *mut leanh::LeanObject,
    mut v_keys_2758_: *mut leanh::LeanObject,
    mut v_vals_2759_: *mut leanh::LeanObject,
    mut v_i_2760_: *mut leanh::LeanObject,
    mut v_entries_2761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2762_: usize = 0;
    let mut v_res_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2762_ = leanh::lean_unbox_usize(v_depth_2757_);
    leanh::lean_dec(v_depth_2757_);
    v_res_2763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_depth_boxed_2762_, v_keys_2758_, v_vals_2759_, v_i_2760_, v_entries_2761_);
    leanh::lean_dec_ref(v_vals_2759_);
    leanh::lean_dec_ref(v_keys_2758_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___boxed(
    mut v_x_2764_: *mut leanh::LeanObject,
    mut v_x_2765_: *mut leanh::LeanObject,
    mut v_x_2766_: *mut leanh::LeanObject,
    mut v_x_2767_: *mut leanh::LeanObject,
    mut v_x_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10581__boxed_2769_: usize = 0;
    let mut v_x_10582__boxed_2770_: usize = 0;
    let mut v_res_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10581__boxed_2769_ = leanh::lean_unbox_usize(v_x_2765_);
    leanh::lean_dec(v_x_2765_);
    v_x_10582__boxed_2770_ = leanh::lean_unbox_usize(v_x_2766_);
    leanh::lean_dec(v_x_2766_);
    v_res_2771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_2764_, v_x_10581__boxed_2769_, v_x_10582__boxed_2770_, v_x_2767_, v_x_2768_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(
    mut v_x_2772_: *mut leanh::LeanObject,
    mut v_x_2773_: *mut leanh::LeanObject,
    mut v_x_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2775_: u64 = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: usize = 0;
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = l_Lean_instHashableFVarId_hash(v_x_2773_);
    v___x_2776_ = lean_uint64_to_usize(v___x_2775_);
    v___x_2777_ = 1usize;
    v___x_2778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_2772_, v___x_2776_, v___x_2777_, v_x_2773_, v_x_2774_);
    return v___x_2778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(
    mut v___x_2788_: *mut leanh::LeanObject,
    mut v_as_2789_: *mut leanh::LeanObject,
    mut v_sz_2790_: usize,
    mut v_i_2791_: usize,
    mut v_b_2792_: *mut leanh::LeanObject,
    mut v___y_2793_: *mut leanh::LeanObject,
    mut v___y_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: usize = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___y_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_reuseFailAlloc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2828_ = lean_usize_dec_lt(v_i_2791_, v_sz_2790_);
                if v___x_2828_ == 0 {
                    v___x_2829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2829_, 0, v_b_2792_);
                    return v___x_2829_;
                } else {
                    v_snd_2830_ = leanh::lean_ctor_get(v_b_2792_, 1);
                    leanh::lean_inc(v_snd_2830_);
                    v_fst_2831_ = leanh::lean_ctor_get(v_b_2792_, 0);
                    leanh::lean_inc(v_fst_2831_);
                    leanh::lean_dec_ref(v_b_2792_);
                    v_fst_2832_ = leanh::lean_ctor_get(v_snd_2830_, 0);
                    v_snd_2833_ = leanh::lean_ctor_get(v_snd_2830_, 1);
                    v_isSharedCheck_2900_ = (!leanh::lean_is_exclusive(v_snd_2830_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2835_ = v_snd_2830_;
                        v_isShared_2836_ = v_isSharedCheck_2900_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2833_);
                        leanh::lean_inc(v_fst_2832_);
                        leanh::lean_dec(v_snd_2830_);
                        v___x_2835_ = leanh::lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2900_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2802_, 0, v___y_2801_);
                leanh::lean_ctor_set(v___x_2802_, 1, v___y_2799_);
                v___x_2803_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2803_, 0, v___y_2800_);
                leanh::lean_ctor_set(v___x_2803_, 1, v___x_2802_);
                v___x_2804_ = 1usize;
                v___x_2805_ = lean_usize_add(v_i_2791_, v___x_2804_);
                v_i_2791_ = v___x_2805_;
                v_b_2792_ = v___x_2803_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2815_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2815_, 0, v___y_2809_);
                v___x_2816_ =
                    l_Lean_PersistentArray_set___redArg(v___y_2811_, v___y_2814_, v___x_2815_);
                leanh::lean_dec(v___y_2814_);
                v___x_2817_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2817_, 0, v___y_2810_);
                leanh::lean_ctor_set(v___x_2817_, 1, v___x_2816_);
                leanh::lean_ctor_set(v___x_2817_, 2, v___y_2808_);
                v___y_2799_ = v___y_2812_;
                v___y_2800_ = v___y_2813_;
                v___y_2801_ = v___x_2817_;
                state = 1;
                continue;
            }
            3 => {
                leanh::lean_inc_ref(v___y_2820_);
                v___x_2826_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(v___y_2822_, v___y_2825_, v___y_2820_);
                v_index_2827_ = leanh::lean_ctor_get(v___y_2820_, 0);
                leanh::lean_inc(v_index_2827_);
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
                v___x_2837_ = leanh::lean_unsigned_to_nat(0);
                v_a_2838_ = lean_array_uget_borrowed(v_as_2789_, v_i_2791_);
                leanh::lean_inc(v_a_2838_);
                leanh::lean_inc(v_fst_2832_);
                v___x_2878_ = l_Lean_LocalContext_get_x21(v_fst_2832_, v_a_2838_);
                v___x_2879_ = l_Lean_LocalDecl_userName(v___x_2878_);
                v___x_2880_ = l_Lean_Name_hasMacroScopes(v___x_2879_);
                if v___x_2880_ == 0 {
                    leanh::lean_dec_ref(v___x_2878_);
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
                            leanh::lean_dec_ref(v___x_2878_);
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
                leanh::lean_inc(v___y_2840_);
                if v_isShared_2836_ == 0 {
                    leanh::lean_ctor_set(v___x_2835_, 1, v___y_2845_);
                    leanh::lean_ctor_set(v___x_2835_, 0, v___y_2840_);
                    v___x_2847_ = v___x_2835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___y_2840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___y_2845_);
                    v___x_2847_ = v_reuseFailAlloc_2869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v___y_2840_);
                v___x_2848_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v_fst_2831_, v___x_2788_, v___y_2840_, v___x_2847_);
                if leanh::lean_obj_tag(v___x_2848_) == 0 {
                    v_a_2849_ = leanh::lean_ctor_get(v___x_2848_, 0);
                    leanh::lean_inc(v_a_2849_);
                    leanh::lean_dec_ref_known(v___x_2848_, 1);
                    v_fst_2850_ = leanh::lean_ctor_get(v_a_2849_, 0);
                    leanh::lean_inc_n(v_fst_2850_, 2);
                    v_snd_2851_ = leanh::lean_ctor_get(v_a_2849_, 1);
                    leanh::lean_inc(v_snd_2851_);
                    leanh::lean_dec(v_a_2849_);
                    v_fvarIdToDecl_2852_ = leanh::lean_ctor_get(v_fst_2832_, 0);
                    v_decls_2853_ = leanh::lean_ctor_get(v_fst_2832_, 1);
                    v_auxDeclToFullName_2854_ = leanh::lean_ctor_get(v_fst_2832_, 2);
                    v___x_2855_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_snd_2833_, v___y_2840_, v_snd_2851_);
                    leanh::lean_inc_n(v_a_2838_, 2);
                    v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_fst_2831_, v_fst_2850_, v_a_2838_);
                    leanh::lean_inc(v_fst_2832_);
                    v___x_2857_ = lean_local_ctx_find(v_fst_2832_, v_a_2838_);
                    if leanh::lean_obj_tag(v___x_2857_) == 0 {
                        leanh::lean_dec(v_fst_2850_);
                        v___y_2799_ = v___x_2855_;
                        v___y_2800_ = v___x_2856_;
                        v___y_2801_ = v_fst_2832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_auxDeclToFullName_2854_);
                        leanh::lean_inc_ref(v_decls_2853_);
                        leanh::lean_inc_ref(v_fvarIdToDecl_2852_);
                        leanh::lean_dec(v_fst_2832_);
                        v_val_2858_ = leanh::lean_ctor_get(v___x_2857_, 0);
                        leanh::lean_inc(v_val_2858_);
                        leanh::lean_dec_ref_known(v___x_2857_, 1);
                        v___x_2859_ = l_Lean_LocalDecl_setUserName(v_val_2858_, v_fst_2850_);
                        v_fvarId_2860_ = leanh::lean_ctor_get(v___x_2859_, 1);
                        leanh::lean_inc(v_fvarId_2860_);
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
                    leanh::lean_dec(v___y_2840_);
                    leanh::lean_dec(v_snd_2833_);
                    leanh::lean_dec(v_fst_2832_);
                    leanh::lean_dec(v_fst_2831_);
                    v_a_2861_ = leanh::lean_ctor_get(v___x_2848_, 0);
                    v_isSharedCheck_2868_ = (!leanh::lean_is_exclusive(v___x_2848_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2848_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2861_);
                        leanh::lean_dec(v___x_2848_);
                        v___x_2863_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
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
                if leanh::lean_obj_tag(v___x_2876_) == 0 {
                    v___y_2840_ = v_baseName_2871_;
                    v___y_2841_ = v___y_2872_;
                    v___y_2842_ = v___y_2874_;
                    v___y_2843_ = v___y_2873_;
                    v___y_2844_ = v___y_2875_;
                    v___y_2845_ = v___x_2837_;
                    state = 5;
                    continue;
                } else {
                    v_val_2877_ = leanh::lean_ctor_get(v___x_2876_, 0);
                    leanh::lean_inc(v_val_2877_);
                    leanh::lean_dec_ref_known(v___x_2876_, 1);
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
                leanh::lean_dec_ref(v___x_2878_);
                v___x_2884_ = l_Lean_Meta_isProp(
                    v___x_2883_,
                    v___y_2793_,
                    v___y_2794_,
                    v___y_2795_,
                    v___y_2796_,
                );
                if leanh::lean_obj_tag(v___x_2884_) == 0 {
                    v_a_2885_ = leanh::lean_ctor_get(v___x_2884_, 0);
                    leanh::lean_inc(v_a_2885_);
                    leanh::lean_dec_ref_known(v___x_2884_, 1);
                    v___x_2886_ = (leanh::lean_unbox(v_a_2885_) as u8);
                    leanh::lean_dec(v_a_2885_);
                    if v___x_2886_ == 0 {
                        v_baseName_2871_ = v___x_2881_;
                        v___y_2872_ = v___y_2793_;
                        v___y_2873_ = v___y_2794_;
                        v___y_2874_ = v___y_2795_;
                        v___y_2875_ = v___y_2796_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2881_);
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
                    leanh::lean_dec(v___x_2881_);
                    leanh::lean_del_object(v___x_2835_);
                    leanh::lean_dec(v_snd_2833_);
                    leanh::lean_dec(v_fst_2832_);
                    leanh::lean_dec(v_fst_2831_);
                    v_a_2888_ = leanh::lean_ctor_get(v___x_2884_, 0);
                    v_isSharedCheck_2895_ = (!leanh::lean_is_exclusive(v___x_2884_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2890_ = v___x_2884_;
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2888_);
                        leanh::lean_dec(v___x_2884_);
                        v___x_2890_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
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
    mut v___x_2901_: *mut leanh::LeanObject,
    mut v_as_2902_: *mut leanh::LeanObject,
    mut v_sz_2903_: *mut leanh::LeanObject,
    mut v_i_2904_: *mut leanh::LeanObject,
    mut v_b_2905_: *mut leanh::LeanObject,
    mut v___y_2906_: *mut leanh::LeanObject,
    mut v___y_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2911_: usize = 0;
    let mut v_i_boxed_2912_: usize = 0;
    let mut v_res_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2911_ = leanh::lean_unbox_usize(v_sz_2903_);
    leanh::lean_dec(v_sz_2903_);
    v_i_boxed_2912_ = leanh::lean_unbox_usize(v_i_2904_);
    leanh::lean_dec(v_i_2904_);
    v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(v___x_2901_, v_as_2902_, v_sz_boxed_2911_, v_i_boxed_2912_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
    leanh::lean_dec(v___y_2909_);
    leanh::lean_dec_ref(v___y_2908_);
    leanh::lean_dec(v___y_2907_);
    leanh::lean_dec_ref(v___y_2906_);
    leanh::lean_dec_ref(v_as_2902_);
    leanh::lean_dec(v___x_2901_);
    return v_res_2913_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = leanh::lean_box(0);
    v___x_2915_ = leanh::lean_unsigned_to_nat(16);
    v___x_2916_ = lean_mk_array(v___x_2915_, v___x_2914_);
    return v___x_2916_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__0);
    v___x_2918_ = leanh::lean_unsigned_to_nat(0);
    v_map_2919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_map_2919_, 0, v___x_2918_);
    leanh::lean_ctor_set(v_map_2919_, 1, v___x_2917_);
    return v_map_2919_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3()
-> *mut leanh::LeanObject {
    let mut v_toRename_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toRename_2922_ =
        l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__2;
    v_map_2923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1);
    v___x_2924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2924_, 0, v_map_2923_);
    leanh::lean_ctor_set(v___x_2924_, 1, v_toRename_2922_);
    return v___x_2924_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
    mut v_a_2925_: *mut leanh::LeanObject,
    mut v_a_2926_: *mut leanh::LeanObject,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_fst_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2952_: usize = 0;
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v_snd_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_a_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2972_: u8 = 0;
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_isSharedCheck_2988_: u8 = 0;
    let mut v_a_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2930_ = leanh::lean_ctor_get(v_a_2925_, 2);
                v_decls_2931_ = leanh::lean_ctor_get(v_lctx_2930_, 1);
                v___x_2932_ = leanh::lean_unsigned_to_nat(0);
                v_map_2933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__1);
                v___x_2934_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3_once), _init_l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames___closed__3);
                v___x_2935_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2(v_decls_2931_, v___x_2934_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                if leanh::lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2988_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2988_ == 0 {
                        v___x_2938_ = v___x_2935_;
                        v_isShared_2939_ = v_isSharedCheck_2988_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2936_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2938_ = leanh::lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2989_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2996_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v___x_2991_ = v___x_2935_;
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2989_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2991_ = leanh::lean_box(0);
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2940_ = leanh::lean_ctor_get(v_a_2936_, 0);
                v_snd_2941_ = leanh::lean_ctor_get(v_a_2936_, 1);
                v_isSharedCheck_2987_ = (!leanh::lean_is_exclusive(v_a_2936_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v___x_2943_ = v_a_2936_;
                    v_isShared_2944_ = v_isSharedCheck_2987_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2941_);
                    leanh::lean_inc(v_fst_2940_);
                    leanh::lean_dec(v_a_2936_);
                    v___x_2943_ = leanh::lean_box(0);
                    v_isShared_2944_ = v_isSharedCheck_2987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2945_ = lean_array_get_size(v_snd_2941_);
                v___x_2946_ = lean_nat_dec_eq(v___x_2945_, v___x_2932_);
                if v___x_2946_ == 0 {
                    leanh::lean_del_object(v___x_2938_);
                    if v___x_2946_ == 0 {
                        v___x_2978_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2979_ = lean_nat_sub(v___x_2945_, v___x_2978_);
                        v___x_2983_ = lean_nat_dec_le(v___x_2932_, v___x_2979_);
                        if v___x_2983_ == 0 {
                            leanh::lean_inc(v___x_2979_);
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
                    leanh::lean_del_object(v___x_2943_);
                    leanh::lean_dec(v_snd_2941_);
                    leanh::lean_dec(v_fst_2940_);
                    leanh::lean_inc_ref(v_lctx_2930_);
                    if v_isShared_2939_ == 0 {
                        leanh::lean_ctor_set(v___x_2938_, 0, v_lctx_2930_);
                        v___x_2985_ = v___x_2938_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2986_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_lctx_2930_);
                        v___x_2985_ = v_reuseFailAlloc_2986_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc_ref(v_lctx_2930_);
                if v_isShared_2944_ == 0 {
                    leanh::lean_ctor_set(v___x_2943_, 1, v_map_2933_);
                    leanh::lean_ctor_set(v___x_2943_, 0, v_lctx_2930_);
                    v___x_2950_ = v___x_2943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_lctx_2930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_map_2933_);
                    v___x_2950_ = v_reuseFailAlloc_2973_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2951_, 0, v_fst_2940_);
                leanh::lean_ctor_set(v___x_2951_, 1, v___x_2950_);
                v_sz_2952_ = lean_array_size(v___y_2948_);
                v___x_2953_ = 0usize;
                v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__6(v___x_2945_, v___y_2948_, v_sz_2952_, v___x_2953_, v___x_2951_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                leanh::lean_dec_ref(v___y_2948_);
                if leanh::lean_obj_tag(v___x_2954_) == 0 {
                    v_a_2955_ = leanh::lean_ctor_get(v___x_2954_, 0);
                    v_isSharedCheck_2964_ = (!leanh::lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2957_ = v___x_2954_;
                        v_isShared_2958_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2955_);
                        leanh::lean_dec(v___x_2954_);
                        v___x_2957_ = leanh::lean_box(0);
                        v_isShared_2958_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2965_ = leanh::lean_ctor_get(v___x_2954_, 0);
                    v_isSharedCheck_2972_ = (!leanh::lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2972_ == 0 {
                        v___x_2967_ = v___x_2954_;
                        v_isShared_2968_ = v_isSharedCheck_2972_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2965_);
                        leanh::lean_dec(v___x_2954_);
                        v___x_2967_ = leanh::lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_2972_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_2959_ = leanh::lean_ctor_get(v_a_2955_, 1);
                leanh::lean_inc(v_snd_2959_);
                leanh::lean_dec(v_a_2955_);
                v_fst_2960_ = leanh::lean_ctor_get(v_snd_2959_, 0);
                leanh::lean_inc(v_fst_2960_);
                leanh::lean_dec(v_snd_2959_);
                if v_isShared_2958_ == 0 {
                    leanh::lean_ctor_set(v___x_2957_, 0, v_fst_2960_);
                    v___x_2962_ = v___x_2957_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2960_);
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
                    v_reuseFailAlloc_2971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
                    v___x_2970_ = v_reuseFailAlloc_2971_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2970_;
            }
            9 => {
                leanh::lean_inc_ref(v_lctx_2930_);
                v___x_2977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v_lctx_2930_, v___x_2945_, v_snd_2941_, v___y_2975_, v___y_2976_);
                leanh::lean_dec(v___y_2976_);
                v___y_2948_ = v___x_2977_;
                state = 3;
                continue;
            }
            10 => {
                v___x_2982_ = lean_nat_dec_le(v___y_2981_, v___x_2979_);
                if v___x_2982_ == 0 {
                    leanh::lean_dec(v___x_2979_);
                    leanh::lean_inc(v___y_2981_);
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
                    v_reuseFailAlloc_2995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
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
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3002_ = l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
        v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
    );
    leanh::lean_dec(v_a_3000_);
    leanh::lean_dec_ref(v_a_2999_);
    leanh::lean_dec(v_a_2998_);
    leanh::lean_dec_ref(v_a_2997_);
    return v_res_3002_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0(
    mut v_00_u03b2_3003_: *mut leanh::LeanObject,
    mut v_m_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_b_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0___redArg(v_m_3004_, v_a_3005_, v_b_3006_);
    return v___x_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1(
    mut v_00_u03b2_3008_: *mut leanh::LeanObject,
    mut v_m_3009_: *mut leanh::LeanObject,
    mut v_a_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___redArg(v_m_3009_, v_a_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1___boxed(
    mut v_00_u03b2_3012_: *mut leanh::LeanObject,
    mut v_m_3013_: *mut leanh::LeanObject,
    mut v_a_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1(v_00_u03b2_3012_, v_m_3013_, v_a_3014_);
    leanh::lean_dec(v_a_3014_);
    leanh::lean_dec_ref(v_m_3013_);
    return v_res_3015_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3(
    mut v_00_u03b2_3016_: *mut leanh::LeanObject,
    mut v_m_3017_: *mut leanh::LeanObject,
    mut v_a_3018_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3019_: u8 = 0;
    v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___redArg(v_m_3017_, v_a_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3___boxed(
    mut v_00_u03b2_3020_: *mut leanh::LeanObject,
    mut v_m_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3023_: u8 = 0;
    let mut v_r_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__3(v_00_u03b2_3020_, v_m_3021_, v_a_3022_);
    leanh::lean_dec(v_a_3022_);
    leanh::lean_dec_ref(v_m_3021_);
    v_r_3024_ = leanh::lean_box((v_res_3023_) as usize);
    return v_r_3024_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4(
    mut v___x_3025_: *mut leanh::LeanObject,
    mut v___x_3026_: *mut leanh::LeanObject,
    mut v_baseName_3027_: *mut leanh::LeanObject,
    mut v_inst_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
    mut v___y_3030_: *mut leanh::LeanObject,
    mut v___y_3031_: *mut leanh::LeanObject,
    mut v___y_3032_: *mut leanh::LeanObject,
    mut v___y_3033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___redArg(v___x_3025_, v___x_3026_, v_baseName_3027_, v_a_3029_);
    return v___x_3035_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4___boxed(
    mut v___x_3036_: *mut leanh::LeanObject,
    mut v___x_3037_: *mut leanh::LeanObject,
    mut v_baseName_3038_: *mut leanh::LeanObject,
    mut v_inst_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v___y_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
    mut v___y_3043_: *mut leanh::LeanObject,
    mut v___y_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3046_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__4(v___x_3036_, v___x_3037_, v_baseName_3038_, v_inst_3039_, v_a_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
    leanh::lean_dec(v___y_3044_);
    leanh::lean_dec_ref(v___y_3043_);
    leanh::lean_dec(v___y_3042_);
    leanh::lean_dec_ref(v___y_3041_);
    leanh::lean_dec(v___x_3037_);
    leanh::lean_dec_ref(v___x_3036_);
    return v_res_3046_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5(
    mut v_00_u03b2_3047_: *mut leanh::LeanObject,
    mut v_x_3048_: *mut leanh::LeanObject,
    mut v_x_3049_: *mut leanh::LeanObject,
    mut v_x_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5___redArg(v_x_3048_, v_x_3049_, v_x_3050_);
    return v___x_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7(
    mut v___x_3052_: *mut leanh::LeanObject,
    mut v_n_3053_: *mut leanh::LeanObject,
    mut v_as_3054_: *mut leanh::LeanObject,
    mut v_lo_3055_: *mut leanh::LeanObject,
    mut v_hi_3056_: *mut leanh::LeanObject,
    mut v_w_3057_: *mut leanh::LeanObject,
    mut v_hlo_3058_: *mut leanh::LeanObject,
    mut v_hhi_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___redArg(v___x_3052_, v_n_3053_, v_as_3054_, v_lo_3055_, v_hi_3056_);
    return v___x_3060_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7___boxed(
    mut v___x_3061_: *mut leanh::LeanObject,
    mut v_n_3062_: *mut leanh::LeanObject,
    mut v_as_3063_: *mut leanh::LeanObject,
    mut v_lo_3064_: *mut leanh::LeanObject,
    mut v_hi_3065_: *mut leanh::LeanObject,
    mut v_w_3066_: *mut leanh::LeanObject,
    mut v_hlo_3067_: *mut leanh::LeanObject,
    mut v_hhi_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7(v___x_3061_, v_n_3062_, v_as_3063_, v_lo_3064_, v_hi_3065_, v_w_3066_, v_hlo_3067_, v_hhi_3068_);
    leanh::lean_dec(v_hi_3065_);
    leanh::lean_dec(v_n_3062_);
    return v_res_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0(
    mut v_00_u03b2_3070_: *mut leanh::LeanObject,
    mut v_a_3071_: *mut leanh::LeanObject,
    mut v_x_3072_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3073_: u8 = 0;
    v___x_3073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___redArg(v_a_3071_, v_x_3072_);
    return v___x_3073_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0___boxed(
    mut v_00_u03b2_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_x_3076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3077_: u8 = 0;
    let mut v_r_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__0(v_00_u03b2_3074_, v_a_3075_, v_x_3076_);
    leanh::lean_dec(v_x_3076_);
    leanh::lean_dec(v_a_3075_);
    v_r_3078_ = leanh::lean_box((v_res_3077_) as usize);
    return v_r_3078_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1(
    mut v_00_u03b2_3079_: *mut leanh::LeanObject,
    mut v_data_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3081_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1___redArg(v_data_3080_);
    return v___x_3081_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2(
    mut v_00_u03b2_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_b_3084_: *mut leanh::LeanObject,
    mut v_x_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__2___redArg(v_a_3083_, v_b_3084_, v_x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4(
    mut v_00_u03b2_3087_: *mut leanh::LeanObject,
    mut v_a_3088_: *mut leanh::LeanObject,
    mut v_x_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___redArg(v_a_3088_, v_x_3089_);
    return v___x_3090_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4___boxed(
    mut v_00_u03b2_3091_: *mut leanh::LeanObject,
    mut v_a_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__1_spec__4(v_00_u03b2_3091_, v_a_3092_, v_x_3093_);
    leanh::lean_dec(v_x_3093_);
    leanh::lean_dec(v_a_3092_);
    return v_res_3094_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11(
    mut v_00_u03b2_3095_: *mut leanh::LeanObject,
    mut v_x_3096_: *mut leanh::LeanObject,
    mut v_x_3097_: usize,
    mut v_x_3098_: usize,
    mut v_x_3099_: *mut leanh::LeanObject,
    mut v_x_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg(v_x_3096_, v_x_3097_, v_x_3098_, v_x_3099_, v_x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___boxed(
    mut v_00_u03b2_3102_: *mut leanh::LeanObject,
    mut v_x_3103_: *mut leanh::LeanObject,
    mut v_x_3104_: *mut leanh::LeanObject,
    mut v_x_3105_: *mut leanh::LeanObject,
    mut v_x_3106_: *mut leanh::LeanObject,
    mut v_x_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_11219__boxed_3108_: usize = 0;
    let mut v_x_11220__boxed_3109_: usize = 0;
    let mut v_res_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_11219__boxed_3108_ = leanh::lean_unbox_usize(v_x_3104_);
    leanh::lean_dec(v_x_3104_);
    v_x_11220__boxed_3109_ = leanh::lean_unbox_usize(v_x_3105_);
    leanh::lean_dec(v_x_3105_);
    v_res_3110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11(v_00_u03b2_3102_, v_x_3103_, v_x_11219__boxed_3108_, v_x_11220__boxed_3109_, v_x_3106_, v_x_3107_);
    return v_res_3110_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14(
    mut v___x_3111_: *mut leanh::LeanObject,
    mut v_n_3112_: *mut leanh::LeanObject,
    mut v_lo_3113_: *mut leanh::LeanObject,
    mut v_hi_3114_: *mut leanh::LeanObject,
    mut v_hhi_3115_: *mut leanh::LeanObject,
    mut v_pivot_3116_: *mut leanh::LeanObject,
    mut v_as_3117_: *mut leanh::LeanObject,
    mut v_i_3118_: *mut leanh::LeanObject,
    mut v_k_3119_: *mut leanh::LeanObject,
    mut v_ilo_3120_: *mut leanh::LeanObject,
    mut v_ik_3121_: *mut leanh::LeanObject,
    mut v_w_3122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___redArg(v___x_3111_, v_hi_3114_, v_pivot_3116_, v_as_3117_, v_i_3118_, v_k_3119_);
    return v___x_3123_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14___boxed(
    mut v___x_3124_: *mut leanh::LeanObject,
    mut v_n_3125_: *mut leanh::LeanObject,
    mut v_lo_3126_: *mut leanh::LeanObject,
    mut v_hi_3127_: *mut leanh::LeanObject,
    mut v_hhi_3128_: *mut leanh::LeanObject,
    mut v_pivot_3129_: *mut leanh::LeanObject,
    mut v_as_3130_: *mut leanh::LeanObject,
    mut v_i_3131_: *mut leanh::LeanObject,
    mut v_k_3132_: *mut leanh::LeanObject,
    mut v_ilo_3133_: *mut leanh::LeanObject,
    mut v_ik_3134_: *mut leanh::LeanObject,
    mut v_w_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__7_spec__14(v___x_3124_, v_n_3125_, v_lo_3126_, v_hi_3127_, v_hhi_3128_, v_pivot_3129_, v_as_3130_, v_i_3131_, v_k_3132_, v_ilo_3133_, v_ik_3134_, v_w_3135_);
    leanh::lean_dec(v_hi_3127_);
    leanh::lean_dec(v_lo_3126_);
    leanh::lean_dec(v_n_3125_);
    return v_res_3136_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3137_: *mut leanh::LeanObject,
    mut v_i_3138_: *mut leanh::LeanObject,
    mut v_source_3139_: *mut leanh::LeanObject,
    mut v_target_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3141_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2___redArg(v_i_3138_, v_source_3139_, v_target_3140_);
    return v___x_3141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11(
    mut v_as_3142_: *mut leanh::LeanObject,
    mut v_sz_3143_: usize,
    mut v_i_3144_: usize,
    mut v_b_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___redArg(v_as_3142_, v_sz_3143_, v_i_3144_, v_b_3145_);
    return v___x_3151_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11___boxed(
    mut v_as_3152_: *mut leanh::LeanObject,
    mut v_sz_3153_: *mut leanh::LeanObject,
    mut v_i_3154_: *mut leanh::LeanObject,
    mut v_b_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3161_: usize = 0;
    let mut v_i_boxed_3162_: usize = 0;
    let mut v_res_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3161_ = leanh::lean_unbox_usize(v_sz_3153_);
    leanh::lean_dec(v_sz_3153_);
    v_i_boxed_3162_ = leanh::lean_unbox_usize(v_i_3154_);
    leanh::lean_dec(v_i_3154_);
    v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__7_spec__11(v_as_3152_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
    leanh::lean_dec(v___y_3159_);
    leanh::lean_dec_ref(v___y_3158_);
    leanh::lean_dec(v___y_3157_);
    leanh::lean_dec_ref(v___y_3156_);
    leanh::lean_dec_ref(v_as_3152_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16(
    mut v_00_u03b2_3164_: *mut leanh::LeanObject,
    mut v_n_3165_: *mut leanh::LeanObject,
    mut v_k_3166_: *mut leanh::LeanObject,
    mut v_v_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16___redArg(v_n_3165_, v_k_3166_, v_v_3167_);
    return v___x_3168_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17(
    mut v_00_u03b2_3169_: *mut leanh::LeanObject,
    mut v_depth_3170_: usize,
    mut v_keys_3171_: *mut leanh::LeanObject,
    mut v_vals_3172_: *mut leanh::LeanObject,
    mut v_heq_3173_: *mut leanh::LeanObject,
    mut v_i_3174_: *mut leanh::LeanObject,
    mut v_entries_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___redArg(v_depth_3170_, v_keys_3171_, v_vals_3172_, v_i_3174_, v_entries_3175_);
    return v___x_3176_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17___boxed(
    mut v_00_u03b2_3177_: *mut leanh::LeanObject,
    mut v_depth_3178_: *mut leanh::LeanObject,
    mut v_keys_3179_: *mut leanh::LeanObject,
    mut v_vals_3180_: *mut leanh::LeanObject,
    mut v_heq_3181_: *mut leanh::LeanObject,
    mut v_i_3182_: *mut leanh::LeanObject,
    mut v_entries_3183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3184_: usize = 0;
    let mut v_res_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3184_ = leanh::lean_unbox_usize(v_depth_3178_);
    leanh::lean_dec(v_depth_3178_);
    v_res_3185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__17(v_00_u03b2_3177_, v_depth_boxed_3184_, v_keys_3179_, v_vals_3180_, v_heq_3181_, v_i_3182_, v_entries_3183_);
    leanh::lean_dec_ref(v_vals_3180_);
    leanh::lean_dec_ref(v_keys_3179_);
    return v_res_3185_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10(
    mut v_00_u03b2_3186_: *mut leanh::LeanObject,
    mut v_x_3187_: *mut leanh::LeanObject,
    mut v_x_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__0_spec__1_spec__2_spec__10___redArg(v_x_3187_, v_x_3188_);
    return v___x_3189_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16(
    mut v_as_3190_: *mut leanh::LeanObject,
    mut v_sz_3191_: usize,
    mut v_i_3192_: usize,
    mut v_b_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___redArg(v_as_3190_, v_sz_3191_, v_i_3192_, v_b_3193_);
    return v___x_3199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16___boxed(
    mut v_as_3200_: *mut leanh::LeanObject,
    mut v_sz_3201_: *mut leanh::LeanObject,
    mut v_i_3202_: *mut leanh::LeanObject,
    mut v_b_3203_: *mut leanh::LeanObject,
    mut v___y_3204_: *mut leanh::LeanObject,
    mut v___y_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3209_: usize = 0;
    let mut v_i_boxed_3210_: usize = 0;
    let mut v_res_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3209_ = leanh::lean_unbox_usize(v_sz_3201_);
    leanh::lean_dec(v_sz_3201_);
    v_i_boxed_3210_ = leanh::lean_unbox_usize(v_i_3202_);
    leanh::lean_dec(v_i_3202_);
    v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__2_spec__6_spec__9_spec__16(v_as_3200_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
    leanh::lean_dec(v___y_3207_);
    leanh::lean_dec_ref(v___y_3206_);
    leanh::lean_dec(v___y_3205_);
    leanh::lean_dec_ref(v___y_3204_);
    leanh::lean_dec_ref(v_as_3200_);
    return v_res_3211_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21(
    mut v_00_u03b2_3212_: *mut leanh::LeanObject,
    mut v_x_3213_: *mut leanh::LeanObject,
    mut v_x_3214_: *mut leanh::LeanObject,
    mut v_x_3215_: *mut leanh::LeanObject,
    mut v_x_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11_spec__16_spec__21___redArg(v_x_3213_, v_x_3214_, v_x_3215_, v_x_3216_);
    return v___x_3217_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
    mut v_mvarId_3218_: *mut leanh::LeanObject,
    mut v_x_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
    mut v___y_3222_: *mut leanh::LeanObject,
    mut v___y_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_a_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3218_,
                    v_x_3219_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___y_3223_,
                );
                if leanh::lean_obj_tag(v___x_3225_) == 0 {
                    v_a_3226_ = leanh::lean_ctor_get(v___x_3225_, 0);
                    v_isSharedCheck_3233_ = (!leanh::lean_is_exclusive(v___x_3225_)) as u8;
                    if v_isSharedCheck_3233_ == 0 {
                        v___x_3228_ = v___x_3225_;
                        v_isShared_3229_ = v_isSharedCheck_3233_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3226_);
                        leanh::lean_dec(v___x_3225_);
                        v___x_3228_ = leanh::lean_box(0);
                        v_isShared_3229_ = v_isSharedCheck_3233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3234_ = leanh::lean_ctor_get(v___x_3225_, 0);
                    v_isSharedCheck_3241_ = (!leanh::lean_is_exclusive(v___x_3225_)) as u8;
                    if v_isSharedCheck_3241_ == 0 {
                        v___x_3236_ = v___x_3225_;
                        v_isShared_3237_ = v_isSharedCheck_3241_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3234_);
                        leanh::lean_dec(v___x_3225_);
                        v___x_3236_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
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
                    v_reuseFailAlloc_3240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
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
    mut v_mvarId_3242_: *mut leanh::LeanObject,
    mut v_x_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1___redArg(
        v_mvarId_3242_,
        v_x_3243_,
        v___y_3244_,
        v___y_3245_,
        v___y_3246_,
        v___y_3247_,
    );
    leanh::lean_dec(v___y_3247_);
    leanh::lean_dec_ref(v___y_3246_);
    leanh::lean_dec(v___y_3245_);
    leanh::lean_dec_ref(v___y_3244_);
    return v_res_3249_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1(
    mut v_00_u03b1_3250_: *mut leanh::LeanObject,
    mut v_mvarId_3251_: *mut leanh::LeanObject,
    mut v_x_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3259_: *mut leanh::LeanObject,
    mut v_mvarId_3260_: *mut leanh::LeanObject,
    mut v_x_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
    mut v___y_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3267_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_exposeNames_spec__1(
        v_00_u03b1_3259_,
        v_mvarId_3260_,
        v_x_3261_,
        v___y_3262_,
        v___y_3263_,
        v___y_3264_,
        v___y_3265_,
    );
    leanh::lean_dec(v___y_3265_);
    leanh::lean_dec_ref(v___y_3264_);
    leanh::lean_dec(v___y_3263_);
    leanh::lean_dec_ref(v___y_3262_);
    return v_res_3267_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_3268_: *mut leanh::LeanObject,
    mut v_x_3269_: *mut leanh::LeanObject,
    mut v_x_3270_: *mut leanh::LeanObject,
    mut v_x_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3272_ = leanh::lean_ctor_get(v_x_3268_, 0);
                v_vs_3273_ = leanh::lean_ctor_get(v_x_3268_, 1);
                v_isSharedCheck_3297_ = (!leanh::lean_is_exclusive(v_x_3268_)) as u8;
                if v_isSharedCheck_3297_ == 0 {
                    v___x_3275_ = v_x_3268_;
                    v_isShared_3276_ = v_isSharedCheck_3297_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3273_);
                    leanh::lean_inc(v_ks_3272_);
                    leanh::lean_dec(v_x_3268_);
                    v___x_3275_ = leanh::lean_box(0);
                    v_isShared_3276_ = v_isSharedCheck_3297_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3277_ = lean_array_get_size(v_ks_3272_);
                v___x_3278_ = lean_nat_dec_lt(v_x_3269_, v___x_3277_);
                if v___x_3278_ == 0 {
                    leanh::lean_dec(v_x_3269_);
                    v___x_3279_ = lean_array_push(v_ks_3272_, v_x_3270_);
                    v___x_3280_ = lean_array_push(v_vs_3273_, v_x_3271_);
                    if v_isShared_3276_ == 0 {
                        leanh::lean_ctor_set(v___x_3275_, 1, v___x_3280_);
                        leanh::lean_ctor_set(v___x_3275_, 0, v___x_3279_);
                        v___x_3282_ = v___x_3275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3283_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3279_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 1, v___x_3280_);
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
                            v_reuseFailAlloc_3291_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_ks_3272_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_vs_3273_);
                            v___x_3287_ = v_reuseFailAlloc_3291_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3292_ = lean_array_fset(v_ks_3272_, v_x_3269_, v_x_3270_);
                        v___x_3293_ = lean_array_fset(v_vs_3273_, v_x_3269_, v_x_3271_);
                        leanh::lean_dec(v_x_3269_);
                        if v_isShared_3276_ == 0 {
                            leanh::lean_ctor_set(v___x_3275_, 1, v___x_3293_);
                            leanh::lean_ctor_set(v___x_3275_, 0, v___x_3292_);
                            v___x_3295_ = v___x_3275_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3296_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3292_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___x_3293_);
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
                v___x_3288_ = leanh::lean_unsigned_to_nat(1);
                v___x_3289_ = lean_nat_add(v_x_3269_, v___x_3288_);
                leanh::lean_dec(v_x_3269_);
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
    mut v_n_3298_: *mut leanh::LeanObject,
    mut v_k_3299_: *mut leanh::LeanObject,
    mut v_v_3300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = leanh::lean_unsigned_to_nat(0);
    v___x_3302_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_3298_, v___x_3301_, v_k_3299_, v_v_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(
    mut v_x_3303_: *mut leanh::LeanObject,
    mut v_x_3304_: usize,
    mut v_x_3305_: usize,
    mut v_x_3306_: *mut leanh::LeanObject,
    mut v_x_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: usize = 0;
    let mut v___x_3312_: usize = 0;
    let mut v_j_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3318_: u8 = 0;
    let mut v_v_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_node_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_unused_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3363_: u8 = 0;
    let mut v_ks_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: usize = 0;
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u8 = 0;
    let mut v_reuseFailAlloc_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3303_) == 0 {
                    v_es_3308_ = leanh::lean_ctor_get(v_x_3303_, 0);
                    v___x_3309_ = 5usize;
                    v___x_3310_ = 1usize;
                    v___x_3311_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__1);
                    v___x_3312_ = lean_usize_land(v_x_3304_, v___x_3311_);
                    v_j_3313_ = lean_usize_to_nat(v___x_3312_);
                    v___x_3314_ = lean_array_get_size(v_es_3308_);
                    v___x_3315_ = lean_nat_dec_lt(v_j_3313_, v___x_3314_);
                    if v___x_3315_ == 0 {
                        leanh::lean_dec(v_j_3313_);
                        leanh::lean_dec(v_x_3307_);
                        leanh::lean_dec(v_x_3306_);
                        return v_x_3303_;
                    } else {
                        leanh::lean_inc_ref(v_es_3308_);
                        v_isSharedCheck_3352_ = (!leanh::lean_is_exclusive(v_x_3303_)) as u8;
                        if v_isSharedCheck_3352_ == 0 {
                            v_unused_3353_ = leanh::lean_ctor_get(v_x_3303_, 0);
                            leanh::lean_dec(v_unused_3353_);
                            v___x_3317_ = v_x_3303_;
                            v_isShared_3318_ = v_isSharedCheck_3352_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3303_);
                            v___x_3317_ = leanh::lean_box(0);
                            v_isShared_3318_ = v_isSharedCheck_3352_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3354_ = leanh::lean_ctor_get(v_x_3303_, 0);
                    v_vs_3355_ = leanh::lean_ctor_get(v_x_3303_, 1);
                    v_isSharedCheck_3375_ = (!leanh::lean_is_exclusive(v_x_3303_)) as u8;
                    if v_isSharedCheck_3375_ == 0 {
                        v___x_3357_ = v_x_3303_;
                        v_isShared_3358_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3355_);
                        leanh::lean_inc(v_ks_3354_);
                        leanh::lean_dec(v_x_3303_);
                        v___x_3357_ = leanh::lean_box(0);
                        v_isShared_3358_ = v_isSharedCheck_3375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3319_ = lean_array_fget(v_es_3308_, v_j_3313_);
                v___x_3320_ = leanh::lean_box(0);
                v_xs_x27_3321_ = lean_array_fset(v_es_3308_, v_j_3313_, v___x_3320_);
                match leanh::lean_obj_tag(v_v_3319_) {
                    0 => {
                        v_key_3328_ = leanh::lean_ctor_get(v_v_3319_, 0);
                        v_val_3329_ = leanh::lean_ctor_get(v_v_3319_, 1);
                        v_isSharedCheck_3339_ = (!leanh::lean_is_exclusive(v_v_3319_)) as u8;
                        if v_isSharedCheck_3339_ == 0 {
                            v___x_3331_ = v_v_3319_;
                            v_isShared_3332_ = v_isSharedCheck_3339_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3329_);
                            leanh::lean_inc(v_key_3328_);
                            leanh::lean_dec(v_v_3319_);
                            v___x_3331_ = leanh::lean_box(0);
                            v_isShared_3332_ = v_isSharedCheck_3339_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3340_ = leanh::lean_ctor_get(v_v_3319_, 0);
                        v_isSharedCheck_3350_ = (!leanh::lean_is_exclusive(v_v_3319_)) as u8;
                        if v_isSharedCheck_3350_ == 0 {
                            v___x_3342_ = v_v_3319_;
                            v_isShared_3343_ = v_isSharedCheck_3350_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3340_);
                            leanh::lean_dec(v_v_3319_);
                            v___x_3342_ = leanh::lean_box(0);
                            v_isShared_3343_ = v_isSharedCheck_3350_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3351_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3351_, 0, v_x_3306_);
                        leanh::lean_ctor_set(v___x_3351_, 1, v_x_3307_);
                        v___y_3323_ = v___x_3351_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3324_ = lean_array_fset(v_xs_x27_3321_, v_j_3313_, v___y_3323_);
                leanh::lean_dec(v_j_3313_);
                if v_isShared_3318_ == 0 {
                    leanh::lean_ctor_set(v___x_3317_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
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
                    leanh::lean_del_object(v___x_3331_);
                    v___x_3334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3328_,
                        v_val_3329_,
                        v_x_3306_,
                        v_x_3307_,
                    );
                    v___x_3335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3335_, 0, v___x_3334_);
                    v___y_3323_ = v___x_3335_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3329_);
                    leanh::lean_dec(v_key_3328_);
                    if v_isShared_3332_ == 0 {
                        leanh::lean_ctor_set(v___x_3331_, 1, v_x_3307_);
                        leanh::lean_ctor_set(v___x_3331_, 0, v_x_3306_);
                        v___x_3337_ = v___x_3331_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_x_3306_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_x_3307_);
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
                    leanh::lean_ctor_set(v___x_3342_, 0, v___x_3346_);
                    v___x_3348_ = v___x_3342_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
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
                    v_reuseFailAlloc_3374_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_ks_3354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_vs_3355_);
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
                    v___x_3372_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3373_ = lean_nat_dec_lt(v___x_3371_, v___x_3372_);
                    leanh::lean_dec(v___x_3371_);
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
                    v_ks_3364_ = leanh::lean_ctor_get(v_newNode_3361_, 0);
                    leanh::lean_inc_ref(v_ks_3364_);
                    v_vs_3365_ = leanh::lean_ctor_get(v_newNode_3361_, 1);
                    leanh::lean_inc_ref(v_vs_3365_);
                    leanh::lean_dec_ref(v_newNode_3361_);
                    v___x_3366_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3367_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames_spec__5_spec__11___redArg___closed__2);
                    v___x_3368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_x_3305_, v_ks_3364_, v_vs_3365_, v___x_3366_, v___x_3367_);
                    leanh::lean_dec_ref(v_vs_3365_);
                    leanh::lean_dec_ref(v_ks_3364_);
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
    mut v_keys_3377_: *mut leanh::LeanObject,
    mut v_vals_3378_: *mut leanh::LeanObject,
    mut v_i_3379_: *mut leanh::LeanObject,
    mut v_entries_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v_k_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u64 = 0;
    let mut v_h_3386_: usize = 0;
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: usize = 0;
    let mut v_h_3392_: usize = 0;
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3381_ = lean_array_get_size(v_keys_3377_);
                v___x_3382_ = lean_nat_dec_lt(v_i_3379_, v___x_3381_);
                if v___x_3382_ == 0 {
                    leanh::lean_dec(v_i_3379_);
                    return v_entries_3380_;
                } else {
                    v_k_3383_ = lean_array_fget_borrowed(v_keys_3377_, v_i_3379_);
                    v_v_3384_ = lean_array_fget_borrowed(v_vals_3378_, v_i_3379_);
                    v___x_3385_ = l_Lean_instHashableMVarId_hash(v_k_3383_);
                    v_h_3386_ = lean_uint64_to_usize(v___x_3385_);
                    v___x_3387_ = 5usize;
                    v___x_3388_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3389_ = 1usize;
                    v___x_3390_ = lean_usize_sub(v_depth_3376_, v___x_3389_);
                    v___x_3391_ = lean_usize_mul(v___x_3387_, v___x_3390_);
                    v_h_3392_ = lean_usize_shift_right(v_h_3386_, v___x_3391_);
                    v___x_3393_ = lean_nat_add(v_i_3379_, v___x_3388_);
                    leanh::lean_dec(v_i_3379_);
                    leanh::lean_inc(v_v_3384_);
                    leanh::lean_inc(v_k_3383_);
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
    mut v_depth_3396_: *mut leanh::LeanObject,
    mut v_keys_3397_: *mut leanh::LeanObject,
    mut v_vals_3398_: *mut leanh::LeanObject,
    mut v_i_3399_: *mut leanh::LeanObject,
    mut v_entries_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3401_: usize = 0;
    let mut v_res_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3401_ = leanh::lean_unbox_usize(v_depth_3396_);
    leanh::lean_dec(v_depth_3396_);
    v_res_3402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_3401_, v_keys_3397_, v_vals_3398_, v_i_3399_, v_entries_3400_);
    leanh::lean_dec_ref(v_vals_3398_);
    leanh::lean_dec_ref(v_keys_3397_);
    return v_res_3402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_3403_: *mut leanh::LeanObject,
    mut v_x_3404_: *mut leanh::LeanObject,
    mut v_x_3405_: *mut leanh::LeanObject,
    mut v_x_3406_: *mut leanh::LeanObject,
    mut v_x_3407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1508__boxed_3408_: usize = 0;
    let mut v_x_1509__boxed_3409_: usize = 0;
    let mut v_res_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1508__boxed_3408_ = leanh::lean_unbox_usize(v_x_3404_);
    leanh::lean_dec(v_x_3404_);
    v_x_1509__boxed_3409_ = leanh::lean_unbox_usize(v_x_3405_);
    leanh::lean_dec(v_x_3405_);
    v_res_3410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3403_, v_x_1508__boxed_3408_, v_x_1509__boxed_3409_, v_x_3406_, v_x_3407_);
    return v_res_3410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(
    mut v_x_3411_: *mut leanh::LeanObject,
    mut v_x_3412_: *mut leanh::LeanObject,
    mut v_x_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: u64 = 0;
    let mut v___x_3415_: usize = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_instHashableMVarId_hash(v_x_3412_);
    v___x_3415_ = lean_uint64_to_usize(v___x_3414_);
    v___x_3416_ = 1usize;
    v___x_3417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3411_, v___x_3415_, v___x_3416_, v_x_3412_, v_x_3413_);
    return v___x_3417_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
    mut v_mvarId_3418_: *mut leanh::LeanObject,
    mut v_val_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v_depth_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = lean_st_ref_take(v___y_3420_);
                v_mctx_3423_ = leanh::lean_ctor_get(v___x_3422_, 0);
                v_cache_3424_ = leanh::lean_ctor_get(v___x_3422_, 1);
                v_zetaDeltaFVarIds_3425_ = leanh::lean_ctor_get(v___x_3422_, 2);
                v_postponed_3426_ = leanh::lean_ctor_get(v___x_3422_, 3);
                v_diag_3427_ = leanh::lean_ctor_get(v___x_3422_, 4);
                v_isSharedCheck_3455_ = (!leanh::lean_is_exclusive(v___x_3422_)) as u8;
                if v_isSharedCheck_3455_ == 0 {
                    v___x_3429_ = v___x_3422_;
                    v_isShared_3430_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3427_);
                    leanh::lean_inc(v_postponed_3426_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3425_);
                    leanh::lean_inc(v_cache_3424_);
                    leanh::lean_inc(v_mctx_3423_);
                    leanh::lean_dec(v___x_3422_);
                    v___x_3429_ = leanh::lean_box(0);
                    v_isShared_3430_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3431_ = leanh::lean_ctor_get(v_mctx_3423_, 0);
                v_levelAssignDepth_3432_ = leanh::lean_ctor_get(v_mctx_3423_, 1);
                v_lmvarCounter_3433_ = leanh::lean_ctor_get(v_mctx_3423_, 2);
                v_mvarCounter_3434_ = leanh::lean_ctor_get(v_mctx_3423_, 3);
                v_lDecls_3435_ = leanh::lean_ctor_get(v_mctx_3423_, 4);
                v_decls_3436_ = leanh::lean_ctor_get(v_mctx_3423_, 5);
                v_userNames_3437_ = leanh::lean_ctor_get(v_mctx_3423_, 6);
                v_lAssignment_3438_ = leanh::lean_ctor_get(v_mctx_3423_, 7);
                v_eAssignment_3439_ = leanh::lean_ctor_get(v_mctx_3423_, 8);
                v_dAssignment_3440_ = leanh::lean_ctor_get(v_mctx_3423_, 9);
                v_isSharedCheck_3454_ = (!leanh::lean_is_exclusive(v_mctx_3423_)) as u8;
                if v_isSharedCheck_3454_ == 0 {
                    v___x_3442_ = v_mctx_3423_;
                    v_isShared_3443_ = v_isSharedCheck_3454_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3440_);
                    leanh::lean_inc(v_eAssignment_3439_);
                    leanh::lean_inc(v_lAssignment_3438_);
                    leanh::lean_inc(v_userNames_3437_);
                    leanh::lean_inc(v_decls_3436_);
                    leanh::lean_inc(v_lDecls_3435_);
                    leanh::lean_inc(v_mvarCounter_3434_);
                    leanh::lean_inc(v_lmvarCounter_3433_);
                    leanh::lean_inc(v_levelAssignDepth_3432_);
                    leanh::lean_inc(v_depth_3431_);
                    leanh::lean_dec(v_mctx_3423_);
                    v___x_3442_ = leanh::lean_box(0);
                    v_isShared_3443_ = v_isSharedCheck_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(v_eAssignment_3439_, v_mvarId_3418_, v_val_3419_);
                if v_isShared_3443_ == 0 {
                    leanh::lean_ctor_set(v___x_3442_, 8, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_depth_3431_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3453_,
                        1,
                        v_levelAssignDepth_3432_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_lmvarCounter_3433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_mvarCounter_3434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_lDecls_3435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 5, v_decls_3436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 6, v_userNames_3437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 7, v_lAssignment_3438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 8, v___x_3444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 9, v_dAssignment_3440_);
                    v___x_3446_ = v_reuseFailAlloc_3453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3430_ == 0 {
                    leanh::lean_ctor_set(v___x_3429_, 0, v___x_3446_);
                    v___x_3448_ = v___x_3429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_cache_3424_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3452_,
                        2,
                        v_zetaDeltaFVarIds_3425_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_postponed_3426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_diag_3427_);
                    v___x_3448_ = v_reuseFailAlloc_3452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3449_ = lean_st_ref_set(v___y_3420_, v___x_3448_);
                v___x_3450_ = leanh::lean_box(0);
                v___x_3451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                return v___x_3451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg___boxed(
    mut v_mvarId_3456_: *mut leanh::LeanObject,
    mut v_val_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
        v_mvarId_3456_,
        v_val_3457_,
        v___y_3458_,
    );
    leanh::lean_dec(v___y_3458_);
    return v_res_3460_;
}
pub unsafe fn l_Lean_MVarId_exposeNames___lam__0(
    mut v_mvarId_3461_: *mut leanh::LeanObject,
    mut v___x_3462_: *mut leanh::LeanObject,
    mut v___y_3463_: *mut leanh::LeanObject,
    mut v___y_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_unused_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_a_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut v_a_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3513_: u8 = 0;
    let mut v_a_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_a_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3525_: u8 = 0;
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3461_);
                v___x_3468_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3461_,
                    v___x_3462_,
                    v___y_3463_,
                    v___y_3464_,
                    v___y_3465_,
                    v___y_3466_,
                );
                if leanh::lean_obj_tag(v___x_3468_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3468_, 1);
                    v___x_3469_ = l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
                    if leanh::lean_obj_tag(v___x_3469_) == 0 {
                        v_a_3470_ = leanh::lean_ctor_get(v___x_3469_, 0);
                        leanh::lean_inc(v_a_3470_);
                        leanh::lean_dec_ref_known(v___x_3469_, 1);
                        leanh::lean_inc(v_mvarId_3461_);
                        v___x_3471_ = l_Lean_MVarId_getType(
                            v_mvarId_3461_,
                            v___y_3463_,
                            v___y_3464_,
                            v___y_3465_,
                            v___y_3466_,
                        );
                        if leanh::lean_obj_tag(v___x_3471_) == 0 {
                            v_a_3472_ = leanh::lean_ctor_get(v___x_3471_, 0);
                            leanh::lean_inc(v_a_3472_);
                            leanh::lean_dec_ref_known(v___x_3471_, 1);
                            leanh::lean_inc(v_mvarId_3461_);
                            v___x_3473_ = l_Lean_MVarId_getTag(
                                v_mvarId_3461_,
                                v___y_3463_,
                                v___y_3464_,
                                v___y_3465_,
                                v___y_3466_,
                            );
                            if leanh::lean_obj_tag(v___x_3473_) == 0 {
                                v_a_3474_ = leanh::lean_ctor_get(v___x_3473_, 0);
                                leanh::lean_inc(v_a_3474_);
                                leanh::lean_dec_ref_known(v___x_3473_, 1);
                                v_localInstances_3475_ =
                                    leanh::lean_ctor_get(v___y_3463_, 3);
                                leanh::lean_inc_ref(v_localInstances_3475_);
                                v___x_3476_ = 2;
                                v___x_3477_ = leanh::lean_unsigned_to_nat(0);
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
                                leanh::lean_dec_ref(v___y_3463_);
                                if leanh::lean_obj_tag(v___x_3478_) == 0 {
                                    v_a_3479_ = leanh::lean_ctor_get(v___x_3478_, 0);
                                    leanh::lean_inc_n(v_a_3479_, 2);
                                    leanh::lean_dec_ref_known(v___x_3478_, 1);
                                    v___x_3480_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(v_mvarId_3461_, v_a_3479_, v___y_3464_);
                                    v_isSharedCheck_3488_ =
                                        (!leanh::lean_is_exclusive(v___x_3480_)) as u8;
                                    if v_isSharedCheck_3488_ == 0 {
                                        v_unused_3489_ =
                                            leanh::lean_ctor_get(v___x_3480_, 0);
                                        leanh::lean_dec(v_unused_3489_);
                                        v___x_3482_ = v___x_3480_;
                                        v_isShared_3483_ = v_isSharedCheck_3488_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3480_);
                                        v___x_3482_ = leanh::lean_box(0);
                                        v_isShared_3483_ = v_isSharedCheck_3488_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_mvarId_3461_);
                                    v_a_3490_ = leanh::lean_ctor_get(v___x_3478_, 0);
                                    v_isSharedCheck_3497_ =
                                        (!leanh::lean_is_exclusive(v___x_3478_)) as u8;
                                    if v_isSharedCheck_3497_ == 0 {
                                        v___x_3492_ = v___x_3478_;
                                        v_isShared_3493_ = v_isSharedCheck_3497_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3490_);
                                        leanh::lean_dec(v___x_3478_);
                                        v___x_3492_ = leanh::lean_box(0);
                                        v_isShared_3493_ = v_isSharedCheck_3497_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_3472_);
                                leanh::lean_dec(v_a_3470_);
                                leanh::lean_dec_ref(v___y_3463_);
                                leanh::lean_dec(v_mvarId_3461_);
                                v_a_3498_ = leanh::lean_ctor_get(v___x_3473_, 0);
                                v_isSharedCheck_3505_ =
                                    (!leanh::lean_is_exclusive(v___x_3473_)) as u8;
                                if v_isSharedCheck_3505_ == 0 {
                                    v___x_3500_ = v___x_3473_;
                                    v_isShared_3501_ = v_isSharedCheck_3505_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3498_);
                                    leanh::lean_dec(v___x_3473_);
                                    v___x_3500_ = leanh::lean_box(0);
                                    v_isShared_3501_ = v_isSharedCheck_3505_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3470_);
                            leanh::lean_dec_ref(v___y_3463_);
                            leanh::lean_dec(v_mvarId_3461_);
                            v_a_3506_ = leanh::lean_ctor_get(v___x_3471_, 0);
                            v_isSharedCheck_3513_ =
                                (!leanh::lean_is_exclusive(v___x_3471_)) as u8;
                            if v_isSharedCheck_3513_ == 0 {
                                v___x_3508_ = v___x_3471_;
                                v_isShared_3509_ = v_isSharedCheck_3513_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3506_);
                                leanh::lean_dec(v___x_3471_);
                                v___x_3508_ = leanh::lean_box(0);
                                v_isShared_3509_ = v_isSharedCheck_3513_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3463_);
                        leanh::lean_dec(v_mvarId_3461_);
                        v_a_3514_ = leanh::lean_ctor_get(v___x_3469_, 0);
                        v_isSharedCheck_3521_ =
                            (!leanh::lean_is_exclusive(v___x_3469_)) as u8;
                        if v_isSharedCheck_3521_ == 0 {
                            v___x_3516_ = v___x_3469_;
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3514_);
                            leanh::lean_dec(v___x_3469_);
                            v___x_3516_ = leanh::lean_box(0);
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3463_);
                    leanh::lean_dec(v_mvarId_3461_);
                    v_a_3522_ = leanh::lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3529_ = (!leanh::lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3529_ == 0 {
                        v___x_3524_ = v___x_3468_;
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3522_);
                        leanh::lean_dec(v___x_3468_);
                        v___x_3524_ = leanh::lean_box(0);
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3484_ = l_Lean_Expr_mvarId_x21(v_a_3479_);
                leanh::lean_dec(v_a_3479_);
                if v_isShared_3483_ == 0 {
                    leanh::lean_ctor_set(v___x_3482_, 0, v___x_3484_);
                    v___x_3486_ = v___x_3482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
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
                    v_reuseFailAlloc_3496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
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
                    v_reuseFailAlloc_3504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
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
                    v_reuseFailAlloc_3512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
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
                    v_reuseFailAlloc_3520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
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
                    v_reuseFailAlloc_3528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
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
    mut v_mvarId_3530_: *mut leanh::LeanObject,
    mut v___x_3531_: *mut leanh::LeanObject,
    mut v___y_3532_: *mut leanh::LeanObject,
    mut v___y_3533_: *mut leanh::LeanObject,
    mut v___y_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3537_ = l_Lean_MVarId_exposeNames___lam__0(
        v_mvarId_3530_,
        v___x_3531_,
        v___y_3532_,
        v___y_3533_,
        v___y_3534_,
        v___y_3535_,
    );
    leanh::lean_dec(v___y_3535_);
    leanh::lean_dec_ref(v___y_3534_);
    leanh::lean_dec(v___y_3533_);
    return v_res_3537_;
}
pub unsafe fn l_Lean_MVarId_exposeNames(
    mut v_mvarId_3541_: *mut leanh::LeanObject,
    mut v_a_3542_: *mut leanh::LeanObject,
    mut v_a_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
    mut v_a_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_MVarId_exposeNames___closed__1;
    leanh::lean_inc(v_mvarId_3541_);
    v___f_3548_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_exposeNames___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_3548_, 0, v_mvarId_3541_);
    leanh::lean_closure_set(v___f_3548_, 1, v___x_3547_);
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
    mut v_mvarId_3550_: *mut leanh::LeanObject,
    mut v_a_3551_: *mut leanh::LeanObject,
    mut v_a_3552_: *mut leanh::LeanObject,
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ =
        l_Lean_MVarId_exposeNames(v_mvarId_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
    leanh::lean_dec(v_a_3554_);
    leanh::lean_dec_ref(v_a_3553_);
    leanh::lean_dec(v_a_3552_);
    leanh::lean_dec_ref(v_a_3551_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0(
    mut v_mvarId_3557_: *mut leanh::LeanObject,
    mut v_val_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___redArg(
        v_mvarId_3557_,
        v_val_3558_,
        v___y_3560_,
    );
    return v___x_3564_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0___boxed(
    mut v_mvarId_3565_: *mut leanh::LeanObject,
    mut v_val_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0(
        v_mvarId_3565_,
        v_val_3566_,
        v___y_3567_,
        v___y_3568_,
        v___y_3569_,
        v___y_3570_,
    );
    leanh::lean_dec(v___y_3570_);
    leanh::lean_dec_ref(v___y_3569_);
    leanh::lean_dec(v___y_3568_);
    leanh::lean_dec_ref(v___y_3567_);
    return v_res_3572_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0(
    mut v_00_u03b2_3573_: *mut leanh::LeanObject,
    mut v_x_3574_: *mut leanh::LeanObject,
    mut v_x_3575_: *mut leanh::LeanObject,
    mut v_x_3576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0___redArg(v_x_3574_, v_x_3575_, v_x_3576_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3578_: *mut leanh::LeanObject,
    mut v_x_3579_: *mut leanh::LeanObject,
    mut v_x_3580_: usize,
    mut v_x_3581_: usize,
    mut v_x_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___redArg(v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_, v_x_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3585_: *mut leanh::LeanObject,
    mut v_x_3586_: *mut leanh::LeanObject,
    mut v_x_3587_: *mut leanh::LeanObject,
    mut v_x_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1908__boxed_3591_: usize = 0;
    let mut v_x_1909__boxed_3592_: usize = 0;
    let mut v_res_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1908__boxed_3591_ = leanh::lean_unbox_usize(v_x_3587_);
    leanh::lean_dec(v_x_3587_);
    v_x_1909__boxed_3592_ = leanh::lean_unbox_usize(v_x_3588_);
    leanh::lean_dec(v_x_3588_);
    v_res_3593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2(v_00_u03b2_3585_, v_x_3586_, v_x_1908__boxed_3591_, v_x_1909__boxed_3592_, v_x_3589_, v_x_3590_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_3594_: *mut leanh::LeanObject,
    mut v_n_3595_: *mut leanh::LeanObject,
    mut v_k_3596_: *mut leanh::LeanObject,
    mut v_v_3597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3___redArg(v_n_3595_, v_k_3596_, v_v_3597_);
    return v___x_3598_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_3599_: *mut leanh::LeanObject,
    mut v_depth_3600_: usize,
    mut v_keys_3601_: *mut leanh::LeanObject,
    mut v_vals_3602_: *mut leanh::LeanObject,
    mut v_heq_3603_: *mut leanh::LeanObject,
    mut v_i_3604_: *mut leanh::LeanObject,
    mut v_entries_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_3600_, v_keys_3601_, v_vals_3602_, v_i_3604_, v_entries_3605_);
    return v___x_3606_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_3607_: *mut leanh::LeanObject,
    mut v_depth_3608_: *mut leanh::LeanObject,
    mut v_keys_3609_: *mut leanh::LeanObject,
    mut v_vals_3610_: *mut leanh::LeanObject,
    mut v_heq_3611_: *mut leanh::LeanObject,
    mut v_i_3612_: *mut leanh::LeanObject,
    mut v_entries_3613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3614_: usize = 0;
    let mut v_res_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3614_ = leanh::lean_unbox_usize(v_depth_3608_);
    leanh::lean_dec(v_depth_3608_);
    v_res_3615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_3607_, v_depth_boxed_3614_, v_keys_3609_, v_vals_3610_, v_heq_3611_, v_i_3612_, v_entries_3613_);
    leanh::lean_dec_ref(v_vals_3610_);
    leanh::lean_dec_ref(v_keys_3609_);
    return v_res_3615_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3616_: *mut leanh::LeanObject,
    mut v_x_3617_: *mut leanh::LeanObject,
    mut v_x_3618_: *mut leanh::LeanObject,
    mut v_x_3619_: *mut leanh::LeanObject,
    mut v_x_3620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_exposeNames_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_3617_, v_x_3618_, v_x_3619_, v_x_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg(
    mut v_lctx_3622_: *mut leanh::LeanObject,
    mut v_localInsts_3623_: *mut leanh::LeanObject,
    mut v_x_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v___y_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_a_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    leanh::lean_box(0),
                    v_lctx_3622_,
                    v_localInsts_3623_,
                    v_x_3624_,
                    v___y_3625_,
                    v___y_3626_,
                    v___y_3627_,
                    v___y_3628_,
                );
                if leanh::lean_obj_tag(v___x_3630_) == 0 {
                    v_a_3631_ = leanh::lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3638_ = (!leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3638_ == 0 {
                        v___x_3633_ = v___x_3630_;
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3631_);
                        leanh::lean_dec(v___x_3630_);
                        v___x_3633_ = leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3639_ = leanh::lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3646_ = (!leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3641_ = v___x_3630_;
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3639_);
                        leanh::lean_dec(v___x_3630_);
                        v___x_3641_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
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
                    v_reuseFailAlloc_3645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
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
    mut v_lctx_3647_: *mut leanh::LeanObject,
    mut v_localInsts_3648_: *mut leanh::LeanObject,
    mut v_x_3649_: *mut leanh::LeanObject,
    mut v___y_3650_: *mut leanh::LeanObject,
    mut v___y_3651_: *mut leanh::LeanObject,
    mut v___y_3652_: *mut leanh::LeanObject,
    mut v___y_3653_: *mut leanh::LeanObject,
    mut v___y_3654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3655_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___redArg(
        v_lctx_3647_,
        v_localInsts_3648_,
        v_x_3649_,
        v___y_3650_,
        v___y_3651_,
        v___y_3652_,
        v___y_3653_,
    );
    leanh::lean_dec(v___y_3653_);
    leanh::lean_dec_ref(v___y_3652_);
    leanh::lean_dec(v___y_3651_);
    leanh::lean_dec_ref(v___y_3650_);
    return v_res_3655_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0(
    mut v_00_u03b1_3656_: *mut leanh::LeanObject,
    mut v_lctx_3657_: *mut leanh::LeanObject,
    mut v_localInsts_3658_: *mut leanh::LeanObject,
    mut v_x_3659_: *mut leanh::LeanObject,
    mut v___y_3660_: *mut leanh::LeanObject,
    mut v___y_3661_: *mut leanh::LeanObject,
    mut v___y_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3666_: *mut leanh::LeanObject,
    mut v_lctx_3667_: *mut leanh::LeanObject,
    mut v_localInsts_3668_: *mut leanh::LeanObject,
    mut v_x_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
    mut v___y_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3673_);
    leanh::lean_dec_ref(v___y_3672_);
    leanh::lean_dec(v___y_3671_);
    leanh::lean_dec_ref(v___y_3670_);
    return v_res_3675_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(
    mut v_k_3676_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3677_: u8,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3683_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_3677_,
                    v_k_3676_,
                    v___y_3678_,
                    v___y_3679_,
                    v___y_3680_,
                    v___y_3681_,
                );
                if leanh::lean_obj_tag(v___x_3683_) == 0 {
                    v_a_3684_ = leanh::lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3691_ = (!leanh::lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v___x_3686_ = v___x_3683_;
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3684_);
                        leanh::lean_dec(v___x_3683_);
                        v___x_3686_ = leanh::lean_box(0);
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3692_ = leanh::lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3699_ = (!leanh::lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3699_ == 0 {
                        v___x_3694_ = v___x_3683_;
                        v_isShared_3695_ = v_isSharedCheck_3699_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3692_);
                        leanh::lean_dec(v___x_3683_);
                        v___x_3694_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
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
                    v_reuseFailAlloc_3698_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
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
    mut v_k_3700_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3707_: u8 = 0;
    let mut v_res_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3707_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3701_) as u8);
    v_res_3708_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(
        v_k_3700_,
        v_allowLevelAssignments_boxed_3707_,
        v___y_3702_,
        v___y_3703_,
        v___y_3704_,
        v___y_3705_,
    );
    leanh::lean_dec(v___y_3705_);
    leanh::lean_dec_ref(v___y_3704_);
    leanh::lean_dec(v___y_3703_);
    leanh::lean_dec_ref(v___y_3702_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1(
    mut v_00_u03b1_3709_: *mut leanh::LeanObject,
    mut v_k_3710_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3711_: u8,
    mut v___y_3712_: *mut leanh::LeanObject,
    mut v___y_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3718_: *mut leanh::LeanObject,
    mut v_k_3719_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3720_: *mut leanh::LeanObject,
    mut v___y_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3726_: u8 = 0;
    let mut v_res_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3726_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3720_) as u8);
    v_res_3727_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1(
        v_00_u03b1_3718_,
        v_k_3719_,
        v_allowLevelAssignments_boxed_3726_,
        v___y_3721_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    leanh::lean_dec(v___y_3724_);
    leanh::lean_dec_ref(v___y_3723_);
    leanh::lean_dec(v___y_3722_);
    leanh::lean_dec_ref(v___y_3721_);
    return v_res_3727_;
}
pub unsafe fn l_Lean_Meta_withExposedNames___redArg(
    mut v_k_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3734_ =
                    l___private_Lean_Meta_Tactic_ExposeNames_0__Lean_Meta_getLCtxWithExposedNames(
                        v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
                    );
                if leanh::lean_obj_tag(v___x_3734_) == 0 {
                    v_a_3735_ = leanh::lean_ctor_get(v___x_3734_, 0);
                    leanh::lean_inc(v_a_3735_);
                    leanh::lean_dec_ref_known(v___x_3734_, 1);
                    v_localInstances_3736_ = leanh::lean_ctor_get(v_a_3729_, 3);
                    leanh::lean_inc_ref(v_localInstances_3736_);
                    v___x_3737_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_withLCtx___at___00Lean_Meta_withExposedNames_spec__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    leanh::lean_closure_set(v___x_3737_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_3737_, 1, v_a_3735_);
                    leanh::lean_closure_set(v___x_3737_, 2, v_localInstances_3736_);
                    leanh::lean_closure_set(v___x_3737_, 3, v_k_3728_);
                    v___x_3738_ = 0;
                    v___x_3739_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_withExposedNames_spec__1___redArg(v___x_3737_, v___x_3738_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
                    return v___x_3739_;
                } else {
                    leanh::lean_dec_ref(v_k_3728_);
                    v_a_3740_ = leanh::lean_ctor_get(v___x_3734_, 0);
                    v_isSharedCheck_3747_ = (!leanh::lean_is_exclusive(v___x_3734_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3734_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3740_);
                        leanh::lean_dec(v___x_3734_);
                        v___x_3742_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
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
    mut v_k_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_Lean_Meta_withExposedNames___redArg(
        v_k_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_,
    );
    leanh::lean_dec(v_a_3752_);
    leanh::lean_dec_ref(v_a_3751_);
    leanh::lean_dec(v_a_3750_);
    leanh::lean_dec_ref(v_a_3749_);
    return v_res_3754_;
}
pub unsafe fn l_Lean_Meta_withExposedNames(
    mut v_00_u03b1_3755_: *mut leanh::LeanObject,
    mut v_k_3756_: *mut leanh::LeanObject,
    mut v_a_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Meta_withExposedNames___redArg(
        v_k_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_,
    );
    return v___x_3762_;
}
pub unsafe fn l_Lean_Meta_withExposedNames___boxed(
    mut v_00_u03b1_3763_: *mut leanh::LeanObject,
    mut v_k_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
    mut v_a_3766_: *mut leanh::LeanObject,
    mut v_a_3767_: *mut leanh::LeanObject,
    mut v_a_3768_: *mut leanh::LeanObject,
    mut v_a_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3770_ = l_Lean_Meta_withExposedNames(
        v_00_u03b1_3763_,
        v_k_3764_,
        v_a_3765_,
        v_a_3766_,
        v_a_3767_,
        v_a_3768_,
    );
    leanh::lean_dec(v_a_3768_);
    leanh::lean_dec_ref(v_a_3767_);
    leanh::lean_dec(v_a_3766_);
    leanh::lean_dec_ref(v_a_3765_);
    return v_res_3770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_ExposeNames(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_ExposeNames(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_ExposeNames(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_ExposeNames(builtin);
}