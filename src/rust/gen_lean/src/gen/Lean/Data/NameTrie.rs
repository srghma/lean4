// Lean compiler output
// Module: Lean.Data.NameTrie
// Imports: Lean.Data.PrefixTree Init.Data.Ord.String
use crate::ffi::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul,
    lean_panic_fn_borrowed, lean_string_compare, lean_string_dec_eq, lean_string_dec_lt,
};
use crate::r#gen::Init::Data::Ord::String::{
    initialize_Init_Data_Ord_String, runtime_initialize_Init_Data_Ord_String,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PrefixTree::{
    initialize_Lean_Data_PrefixTree,
    l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop,
    l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find,
    l_Lean_PrefixTreeNode_empty, runtime_initialize_Lean_Data_PrefixTree,
};
pub static l_Lean_instBEqNamePart___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqNamePart_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqNamePart___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqNamePart___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqNamePart: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqNamePart___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedNamePart_default___closed__0_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_instInhabitedNamePart_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedNamePart_default___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedNamePart_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedNamePart_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedNamePart: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToStringNamePart___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToStringNamePart___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToStringNamePart___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringNamePart___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToStringNamePart: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringNamePart___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_NameTrie_empty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_NamePart_cmp___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameTrie_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameTrie_empty___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_NameTrie_empty___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_NameTrie_empty___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedNameTrie___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedNameTrie___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_NameTrie_foldM___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_NameTrie_foldM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_NameTrie_matchingToArray___redArg___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_NameTrie_matchingToArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameTrie_matchingToArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_NamePart_ctorIdx(
    mut v_x_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_875_) == 0 {
        let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_876_ = leanh::lean_unsigned_to_nat(0);
        return v___x_876_;
    } else {
        let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_877_ = leanh::lean_unsigned_to_nat(1);
        return v___x_877_;
    }
}
pub unsafe fn l_Lean_NamePart_ctorIdx___boxed(
    mut v_x_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_NamePart_ctorIdx(v_x_878_);
    leanh::lean_dec_ref(v_x_878_);
    return v_res_879_;
}
pub unsafe fn l_Lean_NamePart_ctorElim___redArg(
    mut v_t_880_: *mut leanh::LeanObject,
    mut v_k_881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_880_) == 0 {
        let mut v_s_882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_882_ = leanh::lean_ctor_get(v_t_880_, 0);
        leanh::lean_inc_ref(v_s_882_);
        leanh::lean_dec_ref_known(v_t_880_, 1);
        v___x_883_ = leanh::lean_apply_1(v_k_881_, v_s_882_);
        return v___x_883_;
    } else {
        let mut v_n_884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_884_ = leanh::lean_ctor_get(v_t_880_, 0);
        leanh::lean_inc(v_n_884_);
        leanh::lean_dec_ref_known(v_t_880_, 1);
        v___x_885_ = leanh::lean_apply_1(v_k_881_, v_n_884_);
        return v___x_885_;
    }
}
pub unsafe fn l_Lean_NamePart_ctorElim(
    mut v_motive_886_: *mut leanh::LeanObject,
    mut v_ctorIdx_887_: *mut leanh::LeanObject,
    mut v_t_888_: *mut leanh::LeanObject,
    mut v_h_889_: *mut leanh::LeanObject,
    mut v_k_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_NamePart_ctorElim___redArg(v_t_888_, v_k_890_);
    return v___x_891_;
}
pub unsafe fn l_Lean_NamePart_ctorElim___boxed(
    mut v_motive_892_: *mut leanh::LeanObject,
    mut v_ctorIdx_893_: *mut leanh::LeanObject,
    mut v_t_894_: *mut leanh::LeanObject,
    mut v_h_895_: *mut leanh::LeanObject,
    mut v_k_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_897_ =
        l_Lean_NamePart_ctorElim(v_motive_892_, v_ctorIdx_893_, v_t_894_, v_h_895_, v_k_896_);
    leanh::lean_dec(v_ctorIdx_893_);
    return v_res_897_;
}
pub unsafe fn l_Lean_NamePart_str_elim___redArg(
    mut v_t_898_: *mut leanh::LeanObject,
    mut v_str_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_NamePart_ctorElim___redArg(v_t_898_, v_str_899_);
    return v___x_900_;
}
pub unsafe fn l_Lean_NamePart_str_elim(
    mut v_motive_901_: *mut leanh::LeanObject,
    mut v_t_902_: *mut leanh::LeanObject,
    mut v_h_903_: *mut leanh::LeanObject,
    mut v_str_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ = l_Lean_NamePart_ctorElim___redArg(v_t_902_, v_str_904_);
    return v___x_905_;
}
pub unsafe fn l_Lean_NamePart_num_elim___redArg(
    mut v_t_906_: *mut leanh::LeanObject,
    mut v_num_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_908_ = l_Lean_NamePart_ctorElim___redArg(v_t_906_, v_num_907_);
    return v___x_908_;
}
pub unsafe fn l_Lean_NamePart_num_elim(
    mut v_motive_909_: *mut leanh::LeanObject,
    mut v_t_910_: *mut leanh::LeanObject,
    mut v_h_911_: *mut leanh::LeanObject,
    mut v_num_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_NamePart_ctorElim___redArg(v_t_910_, v_num_912_);
    return v___x_913_;
}
pub unsafe fn l_Lean_instBEqNamePart_beq(
    mut v_x_914_: *mut leanh::LeanObject,
    mut v_x_915_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_914_) == 0 {
        if leanh::lean_obj_tag(v_x_915_) == 0 {
            let mut v_s_916_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_917_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_918_: u8 = 0;
            v_s_916_ = leanh::lean_ctor_get(v_x_914_, 0);
            v_s_917_ = leanh::lean_ctor_get(v_x_915_, 0);
            v___x_918_ = lean_string_dec_eq(v_s_916_, v_s_917_);
            return v___x_918_;
        } else {
            let mut v___x_919_: u8 = 0;
            v___x_919_ = 0;
            return v___x_919_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_915_) == 1 {
            let mut v_n_920_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_921_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_922_: u8 = 0;
            v_n_920_ = leanh::lean_ctor_get(v_x_914_, 0);
            v_n_921_ = leanh::lean_ctor_get(v_x_915_, 0);
            v___x_922_ = lean_nat_dec_eq(v_n_920_, v_n_921_);
            return v___x_922_;
        } else {
            let mut v___x_923_: u8 = 0;
            v___x_923_ = 0;
            return v___x_923_;
        }
    }
}
pub unsafe fn l_Lean_instBEqNamePart_beq___boxed(
    mut v_x_924_: *mut leanh::LeanObject,
    mut v_x_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_926_: u8 = 0;
    let mut v_r_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_instBEqNamePart_beq(v_x_924_, v_x_925_);
    leanh::lean_dec_ref(v_x_925_);
    leanh::lean_dec_ref(v_x_924_);
    v_r_927_ = leanh::lean_box((v_res_926_) as usize);
    return v_r_927_;
}
pub unsafe fn l_Lean_instToStringNamePart___lam__0(
    mut v_x_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_935_) == 0 {
        let mut v_s_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_936_ = leanh::lean_ctor_get(v_x_935_, 0);
        leanh::lean_inc_ref(v_s_936_);
        leanh::lean_dec_ref_known(v_x_935_, 1);
        return v_s_936_;
    } else {
        let mut v_n_937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_937_ = leanh::lean_ctor_get(v_x_935_, 0);
        leanh::lean_inc(v_n_937_);
        leanh::lean_dec_ref_known(v_x_935_, 1);
        v___x_938_ = l_Nat_reprFast(v_n_937_);
        return v___x_938_;
    }
}
pub unsafe fn l_Lean_NamePart_cmp(
    mut v_x_941_: *mut leanh::LeanObject,
    mut v_x_942_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_941_) == 0 {
        if leanh::lean_obj_tag(v_x_942_) == 0 {
            let mut v_s_943_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_944_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_945_: u8 = 0;
            v_s_943_ = leanh::lean_ctor_get(v_x_941_, 0);
            v_s_944_ = leanh::lean_ctor_get(v_x_942_, 0);
            v___x_945_ = lean_string_compare(v_s_943_, v_s_944_);
            return v___x_945_;
        } else {
            let mut v___x_946_: u8 = 0;
            v___x_946_ = 2;
            return v___x_946_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_942_) == 0 {
            let mut v___x_947_: u8 = 0;
            v___x_947_ = 0;
            return v___x_947_;
        } else {
            let mut v_n_948_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_949_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_950_: u8 = 0;
            v_n_948_ = leanh::lean_ctor_get(v_x_941_, 0);
            v_n_949_ = leanh::lean_ctor_get(v_x_942_, 0);
            v___x_950_ = lean_nat_dec_lt(v_n_948_, v_n_949_);
            if v___x_950_ == 0 {
                let mut v___x_951_: u8 = 0;
                v___x_951_ = lean_nat_dec_eq(v_n_948_, v_n_949_);
                if v___x_951_ == 0 {
                    let mut v___x_952_: u8 = 0;
                    v___x_952_ = 2;
                    return v___x_952_;
                } else {
                    let mut v___x_953_: u8 = 0;
                    v___x_953_ = 1;
                    return v___x_953_;
                }
            } else {
                let mut v___x_954_: u8 = 0;
                v___x_954_ = 0;
                return v___x_954_;
            }
        }
    }
}
pub unsafe fn l_Lean_NamePart_cmp___boxed(
    mut v_x_955_: *mut leanh::LeanObject,
    mut v_x_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_957_: u8 = 0;
    let mut v_r_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_Lean_NamePart_cmp(v_x_955_, v_x_956_);
    leanh::lean_dec_ref(v_x_956_);
    leanh::lean_dec_ref(v_x_955_);
    v_r_958_ = leanh::lean_box((v_res_957_) as usize);
    return v_r_958_;
}
pub unsafe fn l_Lean_NamePart_lt(
    mut v_x_959_: *mut leanh::LeanObject,
    mut v_x_960_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_959_) == 0 {
        if leanh::lean_obj_tag(v_x_960_) == 0 {
            let mut v_s_961_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_962_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_963_: u8 = 0;
            v_s_961_ = leanh::lean_ctor_get(v_x_959_, 0);
            v_s_962_ = leanh::lean_ctor_get(v_x_960_, 0);
            v___x_963_ = lean_string_dec_lt(v_s_961_, v_s_962_);
            return v___x_963_;
        } else {
            let mut v___x_964_: u8 = 0;
            v___x_964_ = 0;
            return v___x_964_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_960_) == 0 {
            let mut v___x_965_: u8 = 0;
            v___x_965_ = 1;
            return v___x_965_;
        } else {
            let mut v_n_966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_968_: u8 = 0;
            v_n_966_ = leanh::lean_ctor_get(v_x_959_, 0);
            v_n_967_ = leanh::lean_ctor_get(v_x_960_, 0);
            v___x_968_ = lean_nat_dec_lt(v_n_966_, v_n_967_);
            return v___x_968_;
        }
    }
}
pub unsafe fn l_Lean_NamePart_lt___boxed(
    mut v_x_969_: *mut leanh::LeanObject,
    mut v_x_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_971_: u8 = 0;
    let mut v_r_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Lean_NamePart_lt(v_x_969_, v_x_970_);
    leanh::lean_dec_ref(v_x_970_);
    leanh::lean_dec_ref(v_x_969_);
    v_r_972_ = leanh::lean_box((v_res_971_) as usize);
    return v_r_972_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(
    mut v_x_973_: *mut leanh::LeanObject,
    mut v_x_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_973_) {
                0 => {
                    return v_x_974_;
                }
                1 => {
                    v_pre_975_ = leanh::lean_ctor_get(v_x_973_, 0);
                    v_str_976_ = leanh::lean_ctor_get(v_x_973_, 1);
                    leanh::lean_inc_ref(v_str_976_);
                    v___x_977_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_977_, 0, v_str_976_);
                    v___x_978_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
                    leanh::lean_ctor_set(v___x_978_, 1, v_x_974_);
                    v_x_973_ = v_pre_975_;
                    v_x_974_ = v___x_978_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_pre_980_ = leanh::lean_ctor_get(v_x_973_, 0);
                    v_i_981_ = leanh::lean_ctor_get(v_x_973_, 1);
                    leanh::lean_inc(v_i_981_);
                    v___x_982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_982_, 0, v_i_981_);
                    v___x_983_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_983_, 0, v___x_982_);
                    leanh::lean_ctor_set(v___x_983_, 1, v_x_974_);
                    v_x_973_ = v_pre_980_;
                    v_x_974_ = v___x_983_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(
    mut v_x_985_: *mut leanh::LeanObject,
    mut v_x_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_987_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_985_, v_x_986_);
    leanh::lean_dec(v_x_985_);
    return v_res_987_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey(
    mut v_n_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = leanh::lean_box(0);
    v___x_990_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_988_, v___x_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(
    mut v_n_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_991_);
    leanh::lean_dec(v_n_991_);
    return v_res_992_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(
    mut v_t_993_: *mut leanh::LeanObject,
    mut v_k_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_993_) == 0 {
                    v_k_995_ = leanh::lean_ctor_get(v_t_993_, 1);
                    v_v_996_ = leanh::lean_ctor_get(v_t_993_, 2);
                    v_l_997_ = leanh::lean_ctor_get(v_t_993_, 3);
                    v_r_998_ = leanh::lean_ctor_get(v_t_993_, 4);
                    v___x_999_ = l_Lean_NamePart_cmp(v_k_994_, v_k_995_);
                    match v___x_999_ {
                        0 => {
                            v_t_993_ = v_l_997_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_996_);
                            v___x_1001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1001_, 0, v_v_996_);
                            return v___x_1001_;
                        }
                        _ => {
                            v_t_993_ = v_r_998_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1003_ = leanh::lean_box(0);
                    return v___x_1003_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(
    mut v_t_1004_: *mut leanh::LeanObject,
    mut v_k_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_1004_, v_k_1005_);
    leanh::lean_dec_ref(v_k_1005_);
    leanh::lean_dec(v_t_1004_);
    return v_res_1006_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = leanh::lean_box(1);
    v___x_1009_ = lean_panic_fn_borrowed(v___x_1008_, v_msg_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2;
    v___x_1014_ = leanh::lean_unsigned_to_nat(35);
    v___x_1015_ = leanh::lean_unsigned_to_nat(182);
    v___x_1016_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1;
    v___x_1017_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0;
    v___x_1018_ = l_mkPanicMessageWithDecl(
        v___x_1017_,
        v___x_1016_,
        v___x_1015_,
        v___x_1014_,
        v___x_1013_,
    );
    return v___x_1018_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2;
    v___x_1020_ = leanh::lean_unsigned_to_nat(21);
    v___x_1021_ = leanh::lean_unsigned_to_nat(183);
    v___x_1022_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1;
    v___x_1023_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0;
    v___x_1024_ = l_mkPanicMessageWithDecl(
        v___x_1023_,
        v___x_1022_,
        v___x_1021_,
        v___x_1020_,
        v___x_1019_,
    );
    return v___x_1024_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6;
    v___x_1028_ = leanh::lean_unsigned_to_nat(35);
    v___x_1029_ = leanh::lean_unsigned_to_nat(276);
    v___x_1030_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5;
    v___x_1031_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0;
    v___x_1032_ = l_mkPanicMessageWithDecl(
        v___x_1031_,
        v___x_1030_,
        v___x_1029_,
        v___x_1028_,
        v___x_1027_,
    );
    return v___x_1032_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6;
    v___x_1034_ = leanh::lean_unsigned_to_nat(21);
    v___x_1035_ = leanh::lean_unsigned_to_nat(277);
    v___x_1036_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5;
    v___x_1037_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0;
    v___x_1038_ = l_mkPanicMessageWithDecl(
        v___x_1037_,
        v___x_1036_,
        v___x_1035_,
        v___x_1034_,
        v___x_1033_,
    );
    return v___x_1038_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(
    mut v_k_1039_: *mut leanh::LeanObject,
    mut v_v_1040_: *mut leanh::LeanObject,
    mut v_t_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1050_: u8 = 0;
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: u8 = 0;
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v_size_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_unused_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v_unused_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_unused_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_size_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v_unused_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1175_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1184_: u8 = 0;
    let mut v_unused_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v_k_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_unused_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_unused_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: u8 = 0;
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v_size_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_unused_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_unused_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v_size_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v_unused_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v_k_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_unused_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_unused_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_unused_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1041_) == 0 {
                    v_size_1042_ = leanh::lean_ctor_get(v_t_1041_, 0);
                    v_k_1043_ = leanh::lean_ctor_get(v_t_1041_, 1);
                    v_v_1044_ = leanh::lean_ctor_get(v_t_1041_, 2);
                    v_l_1045_ = leanh::lean_ctor_get(v_t_1041_, 3);
                    v_r_1046_ = leanh::lean_ctor_get(v_t_1041_, 4);
                    v_isSharedCheck_1402_ = (!leanh::lean_is_exclusive(v_t_1041_)) as u8;
                    if v_isSharedCheck_1402_ == 0 {
                        v___x_1048_ = v_t_1041_;
                        v_isShared_1049_ = v_isSharedCheck_1402_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1046_);
                        leanh::lean_inc(v_l_1045_);
                        leanh::lean_inc(v_v_1044_);
                        leanh::lean_inc(v_k_1043_);
                        leanh::lean_inc(v_size_1042_);
                        leanh::lean_dec(v_t_1041_);
                        v___x_1048_ = leanh::lean_box(0);
                        v_isShared_1049_ = v_isSharedCheck_1402_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1403_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1404_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
                    leanh::lean_ctor_set(v___x_1404_, 1, v_k_1039_);
                    leanh::lean_ctor_set(v___x_1404_, 2, v_v_1040_);
                    leanh::lean_ctor_set(v___x_1404_, 3, v_t_1041_);
                    leanh::lean_ctor_set(v___x_1404_, 4, v_t_1041_);
                    return v___x_1404_;
                }
            }
            1 => {
                v___x_1050_ = l_Lean_NamePart_cmp(v_k_1039_, v_k_1043_);
                match v___x_1050_ {
                    0 => {
                        leanh::lean_dec(v_size_1042_);
                        v___x_1051_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1039_, v_v_1040_, v_l_1045_);
                        if leanh::lean_obj_tag(v_r_1046_) == 0 {
                            if leanh::lean_obj_tag(v___x_1051_) == 0 {
                                v_size_1052_ = leanh::lean_ctor_get(v_r_1046_, 0);
                                v_size_1053_ = leanh::lean_ctor_get(v___x_1051_, 0);
                                leanh::lean_inc(v_size_1053_);
                                v_k_1054_ = leanh::lean_ctor_get(v___x_1051_, 1);
                                leanh::lean_inc(v_k_1054_);
                                v_v_1055_ = leanh::lean_ctor_get(v___x_1051_, 2);
                                leanh::lean_inc(v_v_1055_);
                                v_l_1056_ = leanh::lean_ctor_get(v___x_1051_, 3);
                                leanh::lean_inc(v_l_1056_);
                                v_r_1057_ = leanh::lean_ctor_get(v___x_1051_, 4);
                                leanh::lean_inc(v_r_1057_);
                                v___x_1058_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1059_ = lean_nat_mul(v___x_1058_, v_size_1052_);
                                v___x_1060_ = lean_nat_dec_lt(v___x_1059_, v_size_1053_);
                                leanh::lean_dec(v___x_1059_);
                                if v___x_1060_ == 0 {
                                    leanh::lean_dec(v_r_1057_);
                                    leanh::lean_dec(v_l_1056_);
                                    leanh::lean_dec(v_v_1055_);
                                    leanh::lean_dec(v_k_1054_);
                                    v___x_1061_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1062_ = lean_nat_add(v___x_1061_, v_size_1053_);
                                    leanh::lean_dec(v_size_1053_);
                                    v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1052_);
                                    leanh::lean_dec(v___x_1062_);
                                    if v_isShared_1049_ == 0 {
                                        leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                        leanh::lean_ctor_set(v___x_1048_, 0, v___x_1063_);
                                        v___x_1065_ = v___x_1048_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1066_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            0,
                                            v___x_1063_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            1,
                                            v_k_1043_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            2,
                                            v_v_1044_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            3,
                                            v___x_1051_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            4,
                                            v_r_1046_,
                                        );
                                        v___x_1065_ = v_reuseFailAlloc_1066_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_1138_ =
                                        (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1138_ == 0 {
                                        v_unused_1139_ =
                                            leanh::lean_ctor_get(v___x_1051_, 4);
                                        leanh::lean_dec(v_unused_1139_);
                                        v_unused_1140_ =
                                            leanh::lean_ctor_get(v___x_1051_, 3);
                                        leanh::lean_dec(v_unused_1140_);
                                        v_unused_1141_ =
                                            leanh::lean_ctor_get(v___x_1051_, 2);
                                        leanh::lean_dec(v_unused_1141_);
                                        v_unused_1142_ =
                                            leanh::lean_ctor_get(v___x_1051_, 1);
                                        leanh::lean_dec(v_unused_1142_);
                                        v_unused_1143_ =
                                            leanh::lean_ctor_get(v___x_1051_, 0);
                                        leanh::lean_dec(v_unused_1143_);
                                        v___x_1068_ = v___x_1051_;
                                        v_isShared_1069_ = v_isSharedCheck_1138_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1051_);
                                        v___x_1068_ = leanh::lean_box(0);
                                        v_isShared_1069_ = v_isSharedCheck_1138_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1144_ = leanh::lean_ctor_get(v_r_1046_, 0);
                                v___x_1145_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1146_ = lean_nat_add(v___x_1145_, v_size_1144_);
                                if v_isShared_1049_ == 0 {
                                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1146_);
                                    v___x_1148_ = v___x_1048_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1149_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        0,
                                        v___x_1146_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        1,
                                        v_k_1043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        2,
                                        v_v_1044_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        3,
                                        v___x_1051_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        4,
                                        v_r_1046_,
                                    );
                                    v___x_1148_ = v_reuseFailAlloc_1149_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_1051_) == 0 {
                                v_l_1150_ = leanh::lean_ctor_get(v___x_1051_, 3);
                                leanh::lean_inc(v_l_1150_);
                                if leanh::lean_obj_tag(v_l_1150_) == 0 {
                                    v_r_1151_ = leanh::lean_ctor_get(v___x_1051_, 4);
                                    leanh::lean_inc(v_r_1151_);
                                    if leanh::lean_obj_tag(v_r_1151_) == 0 {
                                        v_size_1152_ = leanh::lean_ctor_get(v___x_1051_, 0);
                                        v_k_1153_ = leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1154_ = leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1168_ =
                                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1168_ == 0 {
                                            v_unused_1169_ =
                                                leanh::lean_ctor_get(v___x_1051_, 4);
                                            leanh::lean_dec(v_unused_1169_);
                                            v_unused_1170_ =
                                                leanh::lean_ctor_get(v___x_1051_, 3);
                                            leanh::lean_dec(v_unused_1170_);
                                            v___x_1156_ = v___x_1051_;
                                            v_isShared_1157_ = v_isSharedCheck_1168_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1154_);
                                            leanh::lean_inc(v_k_1153_);
                                            leanh::lean_inc(v_size_1152_);
                                            leanh::lean_dec(v___x_1051_);
                                            v___x_1156_ = leanh::lean_box(0);
                                            v_isShared_1157_ = v_isSharedCheck_1168_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1171_ = leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1172_ = leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1184_ =
                                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1184_ == 0 {
                                            v_unused_1185_ =
                                                leanh::lean_ctor_get(v___x_1051_, 4);
                                            leanh::lean_dec(v_unused_1185_);
                                            v_unused_1186_ =
                                                leanh::lean_ctor_get(v___x_1051_, 3);
                                            leanh::lean_dec(v_unused_1186_);
                                            v_unused_1187_ =
                                                leanh::lean_ctor_get(v___x_1051_, 0);
                                            leanh::lean_dec(v_unused_1187_);
                                            v___x_1174_ = v___x_1051_;
                                            v_isShared_1175_ = v_isSharedCheck_1184_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1172_);
                                            leanh::lean_inc(v_k_1171_);
                                            leanh::lean_dec(v___x_1051_);
                                            v___x_1174_ = leanh::lean_box(0);
                                            v_isShared_1175_ = v_isSharedCheck_1184_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1188_ = leanh::lean_ctor_get(v___x_1051_, 4);
                                    leanh::lean_inc(v_r_1188_);
                                    if leanh::lean_obj_tag(v_r_1188_) == 0 {
                                        v_k_1189_ = leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1190_ = leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1214_ =
                                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1214_ == 0 {
                                            v_unused_1215_ =
                                                leanh::lean_ctor_get(v___x_1051_, 4);
                                            leanh::lean_dec(v_unused_1215_);
                                            v_unused_1216_ =
                                                leanh::lean_ctor_get(v___x_1051_, 3);
                                            leanh::lean_dec(v_unused_1216_);
                                            v_unused_1217_ =
                                                leanh::lean_ctor_get(v___x_1051_, 0);
                                            leanh::lean_dec(v_unused_1217_);
                                            v___x_1192_ = v___x_1051_;
                                            v_isShared_1193_ = v_isSharedCheck_1214_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1190_);
                                            leanh::lean_inc(v_k_1189_);
                                            leanh::lean_dec(v___x_1051_);
                                            v___x_1192_ = leanh::lean_box(0);
                                            v_isShared_1193_ = v_isSharedCheck_1214_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1218_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1049_ == 0 {
                                            leanh::lean_ctor_set(v___x_1048_, 4, v_r_1188_);
                                            leanh::lean_ctor_set(
                                                v___x_1048_,
                                                3,
                                                v___x_1051_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_1048_,
                                                0,
                                                v___x_1218_,
                                            );
                                            v___x_1220_ = v___x_1048_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1221_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                0,
                                                v___x_1218_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                1,
                                                v_k_1043_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                2,
                                                v_v_1044_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                3,
                                                v___x_1051_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                4,
                                                v_r_1188_,
                                            );
                                            v___x_1220_ = v_reuseFailAlloc_1221_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_1222_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1049_ == 0 {
                                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1051_);
                                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1222_);
                                    v___x_1224_ = v___x_1048_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1225_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        0,
                                        v___x_1222_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        1,
                                        v_k_1043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        2,
                                        v_v_1044_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        3,
                                        v___x_1051_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        4,
                                        v___x_1051_,
                                    );
                                    v___x_1224_ = v_reuseFailAlloc_1225_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_1044_);
                        leanh::lean_dec(v_k_1043_);
                        if v_isShared_1049_ == 0 {
                            leanh::lean_ctor_set(v___x_1048_, 2, v_v_1040_);
                            leanh::lean_ctor_set(v___x_1048_, 1, v_k_1039_);
                            v___x_1227_ = v___x_1048_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_1228_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_size_1042_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1039_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1040_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_l_1045_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1046_);
                            v___x_1227_ = v_reuseFailAlloc_1228_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_1042_);
                        v___x_1229_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1039_, v_v_1040_, v_r_1046_);
                        if leanh::lean_obj_tag(v_l_1045_) == 0 {
                            if leanh::lean_obj_tag(v___x_1229_) == 0 {
                                v_size_1230_ = leanh::lean_ctor_get(v_l_1045_, 0);
                                v_size_1231_ = leanh::lean_ctor_get(v___x_1229_, 0);
                                leanh::lean_inc(v_size_1231_);
                                v_k_1232_ = leanh::lean_ctor_get(v___x_1229_, 1);
                                leanh::lean_inc(v_k_1232_);
                                v_v_1233_ = leanh::lean_ctor_get(v___x_1229_, 2);
                                leanh::lean_inc(v_v_1233_);
                                v_l_1234_ = leanh::lean_ctor_get(v___x_1229_, 3);
                                leanh::lean_inc(v_l_1234_);
                                v_r_1235_ = leanh::lean_ctor_get(v___x_1229_, 4);
                                leanh::lean_inc(v_r_1235_);
                                v___x_1236_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1237_ = lean_nat_mul(v___x_1236_, v_size_1230_);
                                v___x_1238_ = lean_nat_dec_lt(v___x_1237_, v_size_1231_);
                                leanh::lean_dec(v___x_1237_);
                                if v___x_1238_ == 0 {
                                    leanh::lean_dec(v_r_1235_);
                                    leanh::lean_dec(v_l_1234_);
                                    leanh::lean_dec(v_v_1233_);
                                    leanh::lean_dec(v_k_1232_);
                                    v___x_1239_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1240_ = lean_nat_add(v___x_1239_, v_size_1230_);
                                    v___x_1241_ = lean_nat_add(v___x_1240_, v_size_1231_);
                                    leanh::lean_dec(v_size_1231_);
                                    leanh::lean_dec(v___x_1240_);
                                    if v_isShared_1049_ == 0 {
                                        leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                        leanh::lean_ctor_set(v___x_1048_, 0, v___x_1241_);
                                        v___x_1243_ = v___x_1048_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1244_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            0,
                                            v___x_1241_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            1,
                                            v_k_1043_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            2,
                                            v_v_1044_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            3,
                                            v_l_1045_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            4,
                                            v___x_1229_,
                                        );
                                        v___x_1243_ = v_reuseFailAlloc_1244_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_1314_ =
                                        (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                    if v_isSharedCheck_1314_ == 0 {
                                        v_unused_1315_ =
                                            leanh::lean_ctor_get(v___x_1229_, 4);
                                        leanh::lean_dec(v_unused_1315_);
                                        v_unused_1316_ =
                                            leanh::lean_ctor_get(v___x_1229_, 3);
                                        leanh::lean_dec(v_unused_1316_);
                                        v_unused_1317_ =
                                            leanh::lean_ctor_get(v___x_1229_, 2);
                                        leanh::lean_dec(v_unused_1317_);
                                        v_unused_1318_ =
                                            leanh::lean_ctor_get(v___x_1229_, 1);
                                        leanh::lean_dec(v_unused_1318_);
                                        v_unused_1319_ =
                                            leanh::lean_ctor_get(v___x_1229_, 0);
                                        leanh::lean_dec(v_unused_1319_);
                                        v___x_1246_ = v___x_1229_;
                                        v_isShared_1247_ = v_isSharedCheck_1314_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1229_);
                                        v___x_1246_ = leanh::lean_box(0);
                                        v_isShared_1247_ = v_isSharedCheck_1314_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1320_ = leanh::lean_ctor_get(v_l_1045_, 0);
                                v___x_1321_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1320_);
                                if v_isShared_1049_ == 0 {
                                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1322_);
                                    v___x_1324_ = v___x_1048_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1325_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        0,
                                        v___x_1322_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        1,
                                        v_k_1043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        2,
                                        v_v_1044_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        3,
                                        v_l_1045_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        4,
                                        v___x_1229_,
                                    );
                                    v___x_1324_ = v_reuseFailAlloc_1325_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_1229_) == 0 {
                                v_l_1326_ = leanh::lean_ctor_get(v___x_1229_, 3);
                                leanh::lean_inc(v_l_1326_);
                                if leanh::lean_obj_tag(v_l_1326_) == 0 {
                                    v_r_1327_ = leanh::lean_ctor_get(v___x_1229_, 4);
                                    leanh::lean_inc(v_r_1327_);
                                    if leanh::lean_obj_tag(v_r_1327_) == 0 {
                                        v_size_1328_ = leanh::lean_ctor_get(v___x_1229_, 0);
                                        v_k_1329_ = leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1330_ = leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1344_ =
                                            (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1344_ == 0 {
                                            v_unused_1345_ =
                                                leanh::lean_ctor_get(v___x_1229_, 4);
                                            leanh::lean_dec(v_unused_1345_);
                                            v_unused_1346_ =
                                                leanh::lean_ctor_get(v___x_1229_, 3);
                                            leanh::lean_dec(v_unused_1346_);
                                            v___x_1332_ = v___x_1229_;
                                            v_isShared_1333_ = v_isSharedCheck_1344_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1330_);
                                            leanh::lean_inc(v_k_1329_);
                                            leanh::lean_inc(v_size_1328_);
                                            leanh::lean_dec(v___x_1229_);
                                            v___x_1332_ = leanh::lean_box(0);
                                            v_isShared_1333_ = v_isSharedCheck_1344_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_1347_ = leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1348_ = leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1372_ =
                                            (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1372_ == 0 {
                                            v_unused_1373_ =
                                                leanh::lean_ctor_get(v___x_1229_, 4);
                                            leanh::lean_dec(v_unused_1373_);
                                            v_unused_1374_ =
                                                leanh::lean_ctor_get(v___x_1229_, 3);
                                            leanh::lean_dec(v_unused_1374_);
                                            v_unused_1375_ =
                                                leanh::lean_ctor_get(v___x_1229_, 0);
                                            leanh::lean_dec(v_unused_1375_);
                                            v___x_1350_ = v___x_1229_;
                                            v_isShared_1351_ = v_isSharedCheck_1372_;
                                            state = 43;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1348_);
                                            leanh::lean_inc(v_k_1347_);
                                            leanh::lean_dec(v___x_1229_);
                                            v___x_1350_ = leanh::lean_box(0);
                                            v_isShared_1351_ = v_isSharedCheck_1372_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1376_ = leanh::lean_ctor_get(v___x_1229_, 4);
                                    leanh::lean_inc(v_r_1376_);
                                    if leanh::lean_obj_tag(v_r_1376_) == 0 {
                                        v_k_1377_ = leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1378_ = leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1390_ =
                                            (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1390_ == 0 {
                                            v_unused_1391_ =
                                                leanh::lean_ctor_get(v___x_1229_, 4);
                                            leanh::lean_dec(v_unused_1391_);
                                            v_unused_1392_ =
                                                leanh::lean_ctor_get(v___x_1229_, 3);
                                            leanh::lean_dec(v_unused_1392_);
                                            v_unused_1393_ =
                                                leanh::lean_ctor_get(v___x_1229_, 0);
                                            leanh::lean_dec(v_unused_1393_);
                                            v___x_1380_ = v___x_1229_;
                                            v_isShared_1381_ = v_isSharedCheck_1390_;
                                            state = 48;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1378_);
                                            leanh::lean_inc(v_k_1377_);
                                            leanh::lean_dec(v___x_1229_);
                                            v___x_1380_ = leanh::lean_box(0);
                                            v_isShared_1381_ = v_isSharedCheck_1390_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_1394_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1049_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_1048_,
                                                4,
                                                v___x_1229_,
                                            );
                                            leanh::lean_ctor_set(v___x_1048_, 3, v_r_1376_);
                                            leanh::lean_ctor_set(
                                                v___x_1048_,
                                                0,
                                                v___x_1394_,
                                            );
                                            v___x_1396_ = v___x_1048_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1397_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                0,
                                                v___x_1394_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                1,
                                                v_k_1043_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                2,
                                                v_v_1044_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                3,
                                                v_r_1376_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                4,
                                                v___x_1229_,
                                            );
                                            v___x_1396_ = v_reuseFailAlloc_1397_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_1398_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1049_ == 0 {
                                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1229_);
                                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1398_);
                                    v___x_1400_ = v___x_1048_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1401_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        0,
                                        v___x_1398_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        1,
                                        v_k_1043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        2,
                                        v_v_1044_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        3,
                                        v___x_1229_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        4,
                                        v___x_1229_,
                                    );
                                    v___x_1400_ = v_reuseFailAlloc_1401_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1065_;
            }
            3 => {
                if leanh::lean_obj_tag(v_l_1056_) == 0 {
                    if leanh::lean_obj_tag(v_r_1057_) == 0 {
                        v_size_1070_ = leanh::lean_ctor_get(v_l_1056_, 0);
                        v_size_1071_ = leanh::lean_ctor_get(v_r_1057_, 0);
                        v_k_1072_ = leanh::lean_ctor_get(v_r_1057_, 1);
                        v_v_1073_ = leanh::lean_ctor_get(v_r_1057_, 2);
                        v_l_1074_ = leanh::lean_ctor_get(v_r_1057_, 3);
                        v_r_1075_ = leanh::lean_ctor_get(v_r_1057_, 4);
                        v___x_1076_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1077_ = lean_nat_mul(v___x_1076_, v_size_1070_);
                        v___x_1078_ = lean_nat_dec_lt(v_size_1071_, v___x_1077_);
                        leanh::lean_dec(v___x_1077_);
                        if v___x_1078_ == 0 {
                            leanh::lean_inc(v_r_1075_);
                            leanh::lean_inc(v_l_1074_);
                            leanh::lean_inc(v_v_1073_);
                            leanh::lean_inc(v_k_1072_);
                            v_isSharedCheck_1108_ =
                                (!leanh::lean_is_exclusive(v_r_1057_)) as u8;
                            if v_isSharedCheck_1108_ == 0 {
                                v_unused_1109_ = leanh::lean_ctor_get(v_r_1057_, 4);
                                leanh::lean_dec(v_unused_1109_);
                                v_unused_1110_ = leanh::lean_ctor_get(v_r_1057_, 3);
                                leanh::lean_dec(v_unused_1110_);
                                v_unused_1111_ = leanh::lean_ctor_get(v_r_1057_, 2);
                                leanh::lean_dec(v_unused_1111_);
                                v_unused_1112_ = leanh::lean_ctor_get(v_r_1057_, 1);
                                leanh::lean_dec(v_unused_1112_);
                                v_unused_1113_ = leanh::lean_ctor_get(v_r_1057_, 0);
                                leanh::lean_dec(v_unused_1113_);
                                v___x_1080_ = v_r_1057_;
                                v_isShared_1081_ = v_isSharedCheck_1108_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_1057_);
                                v___x_1080_ = leanh::lean_box(0);
                                v_isShared_1081_ = v_isSharedCheck_1108_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1048_);
                            v___x_1114_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1115_ = lean_nat_add(v___x_1114_, v_size_1053_);
                            leanh::lean_dec(v_size_1053_);
                            v___x_1116_ = lean_nat_add(v___x_1115_, v_size_1052_);
                            leanh::lean_dec(v___x_1115_);
                            v___x_1117_ = lean_nat_add(v___x_1114_, v_size_1052_);
                            v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1071_);
                            leanh::lean_dec(v___x_1117_);
                            leanh::lean_inc_ref(v_r_1046_);
                            if v_isShared_1069_ == 0 {
                                leanh::lean_ctor_set(v___x_1068_, 4, v_r_1046_);
                                leanh::lean_ctor_set(v___x_1068_, 3, v_r_1057_);
                                leanh::lean_ctor_set(v___x_1068_, 2, v_v_1044_);
                                leanh::lean_ctor_set(v___x_1068_, 1, v_k_1043_);
                                leanh::lean_ctor_set(v___x_1068_, 0, v___x_1118_);
                                v___x_1120_ = v___x_1068_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1133_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1118_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1043_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1044_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_r_1057_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_r_1046_);
                                v___x_1120_ = v_reuseFailAlloc_1133_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_1056_, 5);
                        leanh::lean_del_object(v___x_1068_);
                        leanh::lean_dec(v_v_1055_);
                        leanh::lean_dec(v_k_1054_);
                        leanh::lean_dec(v_size_1053_);
                        leanh::lean_dec_ref_known(v_r_1046_, 5);
                        leanh::lean_del_object(v___x_1048_);
                        leanh::lean_dec(v_v_1044_);
                        leanh::lean_dec(v_k_1043_);
                        v___x_1134_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
                        v___x_1135_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1134_);
                        return v___x_1135_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1068_);
                    leanh::lean_dec(v_r_1057_);
                    leanh::lean_dec(v_v_1055_);
                    leanh::lean_dec(v_k_1054_);
                    leanh::lean_dec(v_size_1053_);
                    leanh::lean_dec_ref_known(v_r_1046_, 5);
                    leanh::lean_del_object(v___x_1048_);
                    leanh::lean_dec(v_v_1044_);
                    leanh::lean_dec(v_k_1043_);
                    v___x_1136_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
                    v___x_1137_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1136_);
                    return v___x_1137_;
                }
            }
            4 => {
                v___x_1082_ = leanh::lean_unsigned_to_nat(1);
                v___x_1083_ = lean_nat_add(v___x_1082_, v_size_1053_);
                leanh::lean_dec(v_size_1053_);
                v___x_1084_ = lean_nat_add(v___x_1083_, v_size_1052_);
                leanh::lean_dec(v___x_1083_);
                v___x_1096_ = lean_nat_add(v___x_1082_, v_size_1070_);
                if leanh::lean_obj_tag(v_l_1074_) == 0 {
                    v_size_1106_ = leanh::lean_ctor_get(v_l_1074_, 0);
                    leanh::lean_inc(v_size_1106_);
                    v___y_1098_ = v_size_1106_;
                    state = 8;
                    continue;
                } else {
                    v___x_1107_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1098_ = v___x_1107_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1089_ = lean_nat_add(v___y_1087_, v___y_1088_);
                leanh::lean_dec(v___y_1088_);
                leanh::lean_dec(v___y_1087_);
                if v_isShared_1081_ == 0 {
                    leanh::lean_ctor_set(v___x_1080_, 4, v_r_1046_);
                    leanh::lean_ctor_set(v___x_1080_, 3, v_r_1075_);
                    leanh::lean_ctor_set(v___x_1080_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1080_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1080_, 0, v___x_1089_);
                    v___x_1091_ = v___x_1080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_r_1075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_r_1046_);
                    v___x_1091_ = v_reuseFailAlloc_1095_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1069_ == 0 {
                    leanh::lean_ctor_set(v___x_1068_, 4, v___x_1091_);
                    leanh::lean_ctor_set(v___x_1068_, 3, v___y_1086_);
                    leanh::lean_ctor_set(v___x_1068_, 2, v_v_1073_);
                    leanh::lean_ctor_set(v___x_1068_, 1, v_k_1072_);
                    leanh::lean_ctor_set(v___x_1068_, 0, v___x_1084_);
                    v___x_1093_ = v___x_1068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_k_1072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_v_1073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___y_1086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 4, v___x_1091_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1093_;
            }
            8 => {
                v___x_1099_ = lean_nat_add(v___x_1096_, v___y_1098_);
                leanh::lean_dec(v___y_1098_);
                leanh::lean_dec(v___x_1096_);
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v_l_1074_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v_l_1056_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1055_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1054_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1099_);
                    v___x_1101_ = v___x_1048_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_1054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_1055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_l_1056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_l_1074_);
                    v___x_1101_ = v_reuseFailAlloc_1105_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1102_ = lean_nat_add(v___x_1082_, v_size_1052_);
                if leanh::lean_obj_tag(v_r_1075_) == 0 {
                    v_size_1103_ = leanh::lean_ctor_get(v_r_1075_, 0);
                    leanh::lean_inc(v_size_1103_);
                    v___y_1086_ = v___x_1101_;
                    v___y_1087_ = v___x_1102_;
                    v___y_1088_ = v_size_1103_;
                    state = 5;
                    continue;
                } else {
                    v___x_1104_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1086_ = v___x_1101_;
                    v___y_1087_ = v___x_1102_;
                    v___y_1088_ = v___x_1104_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1127_ = (!leanh::lean_is_exclusive(v_r_1046_)) as u8;
                if v_isSharedCheck_1127_ == 0 {
                    v_unused_1128_ = leanh::lean_ctor_get(v_r_1046_, 4);
                    leanh::lean_dec(v_unused_1128_);
                    v_unused_1129_ = leanh::lean_ctor_get(v_r_1046_, 3);
                    leanh::lean_dec(v_unused_1129_);
                    v_unused_1130_ = leanh::lean_ctor_get(v_r_1046_, 2);
                    leanh::lean_dec(v_unused_1130_);
                    v_unused_1131_ = leanh::lean_ctor_get(v_r_1046_, 1);
                    leanh::lean_dec(v_unused_1131_);
                    v_unused_1132_ = leanh::lean_ctor_get(v_r_1046_, 0);
                    leanh::lean_dec(v_unused_1132_);
                    v___x_1122_ = v_r_1046_;
                    v_isShared_1123_ = v_isSharedCheck_1127_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_1046_);
                    v___x_1122_ = leanh::lean_box(0);
                    v_isShared_1123_ = v_isSharedCheck_1127_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1123_ == 0 {
                    leanh::lean_ctor_set(v___x_1122_, 4, v___x_1120_);
                    leanh::lean_ctor_set(v___x_1122_, 3, v_l_1056_);
                    leanh::lean_ctor_set(v___x_1122_, 2, v_v_1055_);
                    leanh::lean_ctor_set(v___x_1122_, 1, v_k_1054_);
                    leanh::lean_ctor_set(v___x_1122_, 0, v___x_1116_);
                    v___x_1125_ = v___x_1122_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_l_1056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 4, v___x_1120_);
                    v___x_1125_ = v_reuseFailAlloc_1126_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1125_;
            }
            13 => {
                return v___x_1148_;
            }
            14 => {
                v_size_1158_ = leanh::lean_ctor_get(v_r_1151_, 0);
                v___x_1159_ = leanh::lean_unsigned_to_nat(1);
                v___x_1160_ = lean_nat_add(v___x_1159_, v_size_1152_);
                leanh::lean_dec(v_size_1152_);
                v___x_1161_ = lean_nat_add(v___x_1159_, v_size_1158_);
                if v_isShared_1157_ == 0 {
                    leanh::lean_ctor_set(v___x_1156_, 4, v_r_1046_);
                    leanh::lean_ctor_set(v___x_1156_, 3, v_r_1151_);
                    leanh::lean_ctor_set(v___x_1156_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1156_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1156_, 0, v___x_1161_);
                    v___x_1163_ = v___x_1156_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_r_1151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_r_1046_);
                    v___x_1163_ = v_reuseFailAlloc_1167_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1163_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1154_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1153_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1160_);
                    v___x_1165_ = v___x_1048_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 4, v___x_1163_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1165_;
            }
            17 => {
                v___x_1176_ = leanh::lean_unsigned_to_nat(3);
                v___x_1177_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1175_ == 0 {
                    leanh::lean_ctor_set(v___x_1174_, 3, v_r_1151_);
                    leanh::lean_ctor_set(v___x_1174_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1174_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1174_, 0, v___x_1177_);
                    v___x_1179_ = v___x_1174_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_r_1151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_r_1151_);
                    v___x_1179_ = v_reuseFailAlloc_1183_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1179_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1172_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1171_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1176_);
                    v___x_1181_ = v___x_1048_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1182_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_1171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_1172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 4, v___x_1179_);
                    v___x_1181_ = v_reuseFailAlloc_1182_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1181_;
            }
            20 => {
                v_k_1194_ = leanh::lean_ctor_get(v_r_1188_, 1);
                v_v_1195_ = leanh::lean_ctor_get(v_r_1188_, 2);
                v_isSharedCheck_1210_ = (!leanh::lean_is_exclusive(v_r_1188_)) as u8;
                if v_isSharedCheck_1210_ == 0 {
                    v_unused_1211_ = leanh::lean_ctor_get(v_r_1188_, 4);
                    leanh::lean_dec(v_unused_1211_);
                    v_unused_1212_ = leanh::lean_ctor_get(v_r_1188_, 3);
                    leanh::lean_dec(v_unused_1212_);
                    v_unused_1213_ = leanh::lean_ctor_get(v_r_1188_, 0);
                    leanh::lean_dec(v_unused_1213_);
                    v___x_1197_ = v_r_1188_;
                    v_isShared_1198_ = v_isSharedCheck_1210_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1195_);
                    leanh::lean_inc(v_k_1194_);
                    leanh::lean_dec(v_r_1188_);
                    v___x_1197_ = leanh::lean_box(0);
                    v_isShared_1198_ = v_isSharedCheck_1210_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1199_ = leanh::lean_unsigned_to_nat(3);
                v___x_1200_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1198_ == 0 {
                    leanh::lean_ctor_set(v___x_1197_, 4, v_l_1150_);
                    leanh::lean_ctor_set(v___x_1197_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v___x_1197_, 2, v_v_1190_);
                    leanh::lean_ctor_set(v___x_1197_, 1, v_k_1189_);
                    leanh::lean_ctor_set(v___x_1197_, 0, v___x_1200_);
                    v___x_1202_ = v___x_1197_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_l_1150_);
                    v___x_1202_ = v_reuseFailAlloc_1209_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1193_ == 0 {
                    leanh::lean_ctor_set(v___x_1192_, 4, v_l_1150_);
                    leanh::lean_ctor_set(v___x_1192_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1192_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1192_, 0, v___x_1200_);
                    v___x_1204_ = v___x_1192_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1208_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_l_1150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_l_1150_);
                    v___x_1204_ = v_reuseFailAlloc_1208_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1204_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1202_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1195_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1194_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1199_);
                    v___x_1206_ = v___x_1048_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___x_1202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 4, v___x_1204_);
                    v___x_1206_ = v_reuseFailAlloc_1207_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1206_;
            }
            25 => {
                return v___x_1220_;
            }
            26 => {
                return v___x_1224_;
            }
            27 => {
                return v___x_1227_;
            }
            28 => {
                return v___x_1243_;
            }
            29 => {
                if leanh::lean_obj_tag(v_l_1234_) == 0 {
                    if leanh::lean_obj_tag(v_r_1235_) == 0 {
                        v_size_1248_ = leanh::lean_ctor_get(v_l_1234_, 0);
                        v_k_1249_ = leanh::lean_ctor_get(v_l_1234_, 1);
                        v_v_1250_ = leanh::lean_ctor_get(v_l_1234_, 2);
                        v_l_1251_ = leanh::lean_ctor_get(v_l_1234_, 3);
                        v_r_1252_ = leanh::lean_ctor_get(v_l_1234_, 4);
                        v_size_1253_ = leanh::lean_ctor_get(v_r_1235_, 0);
                        v___x_1254_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1255_ = lean_nat_mul(v___x_1254_, v_size_1253_);
                        v___x_1256_ = lean_nat_dec_lt(v_size_1248_, v___x_1255_);
                        leanh::lean_dec(v___x_1255_);
                        if v___x_1256_ == 0 {
                            leanh::lean_inc(v_r_1252_);
                            leanh::lean_inc(v_l_1251_);
                            leanh::lean_inc(v_v_1250_);
                            leanh::lean_inc(v_k_1249_);
                            v_isSharedCheck_1285_ =
                                (!leanh::lean_is_exclusive(v_l_1234_)) as u8;
                            if v_isSharedCheck_1285_ == 0 {
                                v_unused_1286_ = leanh::lean_ctor_get(v_l_1234_, 4);
                                leanh::lean_dec(v_unused_1286_);
                                v_unused_1287_ = leanh::lean_ctor_get(v_l_1234_, 3);
                                leanh::lean_dec(v_unused_1287_);
                                v_unused_1288_ = leanh::lean_ctor_get(v_l_1234_, 2);
                                leanh::lean_dec(v_unused_1288_);
                                v_unused_1289_ = leanh::lean_ctor_get(v_l_1234_, 1);
                                leanh::lean_dec(v_unused_1289_);
                                v_unused_1290_ = leanh::lean_ctor_get(v_l_1234_, 0);
                                leanh::lean_dec(v_unused_1290_);
                                v___x_1258_ = v_l_1234_;
                                v_isShared_1259_ = v_isSharedCheck_1285_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1234_);
                                v___x_1258_ = leanh::lean_box(0);
                                v_isShared_1259_ = v_isSharedCheck_1285_;
                                state = 30;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1048_);
                            v___x_1291_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1230_);
                            v___x_1293_ = lean_nat_add(v___x_1292_, v_size_1231_);
                            leanh::lean_dec(v_size_1231_);
                            v___x_1294_ = lean_nat_add(v___x_1292_, v_size_1248_);
                            leanh::lean_dec(v___x_1292_);
                            leanh::lean_inc_ref(v_l_1045_);
                            if v_isShared_1247_ == 0 {
                                leanh::lean_ctor_set(v___x_1246_, 4, v_l_1234_);
                                leanh::lean_ctor_set(v___x_1246_, 3, v_l_1045_);
                                leanh::lean_ctor_set(v___x_1246_, 2, v_v_1044_);
                                leanh::lean_ctor_set(v___x_1246_, 1, v_k_1043_);
                                leanh::lean_ctor_set(v___x_1246_, 0, v___x_1294_);
                                v___x_1296_ = v___x_1246_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_1309_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1294_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1043_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1044_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_l_1045_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_l_1234_);
                                v___x_1296_ = v_reuseFailAlloc_1309_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_1234_, 5);
                        leanh::lean_del_object(v___x_1246_);
                        leanh::lean_dec(v_v_1233_);
                        leanh::lean_dec(v_k_1232_);
                        leanh::lean_dec(v_size_1231_);
                        leanh::lean_dec_ref_known(v_l_1045_, 5);
                        leanh::lean_del_object(v___x_1048_);
                        leanh::lean_dec(v_v_1044_);
                        leanh::lean_dec(v_k_1043_);
                        v___x_1310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
                        v___x_1311_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1310_);
                        return v___x_1311_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1246_);
                    leanh::lean_dec(v_r_1235_);
                    leanh::lean_dec(v_v_1233_);
                    leanh::lean_dec(v_k_1232_);
                    leanh::lean_dec(v_size_1231_);
                    leanh::lean_dec_ref_known(v_l_1045_, 5);
                    leanh::lean_del_object(v___x_1048_);
                    leanh::lean_dec(v_v_1044_);
                    leanh::lean_dec(v_k_1043_);
                    v___x_1312_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
                    v___x_1313_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1312_);
                    return v___x_1313_;
                }
            }
            30 => {
                v___x_1260_ = leanh::lean_unsigned_to_nat(1);
                v___x_1261_ = lean_nat_add(v___x_1260_, v_size_1230_);
                v___x_1262_ = lean_nat_add(v___x_1261_, v_size_1231_);
                leanh::lean_dec(v_size_1231_);
                if leanh::lean_obj_tag(v_l_1251_) == 0 {
                    v_size_1283_ = leanh::lean_ctor_get(v_l_1251_, 0);
                    leanh::lean_inc(v_size_1283_);
                    v___y_1275_ = v_size_1283_;
                    state = 34;
                    continue;
                } else {
                    v___x_1284_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1275_ = v___x_1284_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1267_ = lean_nat_add(v___y_1265_, v___y_1266_);
                leanh::lean_dec(v___y_1266_);
                leanh::lean_dec(v___y_1265_);
                if v_isShared_1259_ == 0 {
                    leanh::lean_ctor_set(v___x_1258_, 4, v_r_1235_);
                    leanh::lean_ctor_set(v___x_1258_, 3, v_r_1252_);
                    leanh::lean_ctor_set(v___x_1258_, 2, v_v_1233_);
                    leanh::lean_ctor_set(v___x_1258_, 1, v_k_1232_);
                    leanh::lean_ctor_set(v___x_1258_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1258_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_r_1252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_r_1235_);
                    v___x_1269_ = v_reuseFailAlloc_1273_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1247_ == 0 {
                    leanh::lean_ctor_set(v___x_1246_, 4, v___x_1269_);
                    leanh::lean_ctor_set(v___x_1246_, 3, v___y_1264_);
                    leanh::lean_ctor_set(v___x_1246_, 2, v_v_1250_);
                    leanh::lean_ctor_set(v___x_1246_, 1, v_k_1249_);
                    leanh::lean_ctor_set(v___x_1246_, 0, v___x_1262_);
                    v___x_1271_ = v___x_1246_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_1249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_1250_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___y_1264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___x_1269_);
                    v___x_1271_ = v_reuseFailAlloc_1272_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1271_;
            }
            34 => {
                v___x_1276_ = lean_nat_add(v___x_1261_, v___y_1275_);
                leanh::lean_dec(v___y_1275_);
                leanh::lean_dec(v___x_1261_);
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v_l_1251_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1276_);
                    v___x_1278_ = v___x_1048_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_l_1045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_l_1251_);
                    v___x_1278_ = v_reuseFailAlloc_1282_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1279_ = lean_nat_add(v___x_1260_, v_size_1253_);
                if leanh::lean_obj_tag(v_r_1252_) == 0 {
                    v_size_1280_ = leanh::lean_ctor_get(v_r_1252_, 0);
                    leanh::lean_inc(v_size_1280_);
                    v___y_1264_ = v___x_1278_;
                    v___y_1265_ = v___x_1279_;
                    v___y_1266_ = v_size_1280_;
                    state = 31;
                    continue;
                } else {
                    v___x_1281_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1264_ = v___x_1278_;
                    v___y_1265_ = v___x_1279_;
                    v___y_1266_ = v___x_1281_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_1303_ = (!leanh::lean_is_exclusive(v_l_1045_)) as u8;
                if v_isSharedCheck_1303_ == 0 {
                    v_unused_1304_ = leanh::lean_ctor_get(v_l_1045_, 4);
                    leanh::lean_dec(v_unused_1304_);
                    v_unused_1305_ = leanh::lean_ctor_get(v_l_1045_, 3);
                    leanh::lean_dec(v_unused_1305_);
                    v_unused_1306_ = leanh::lean_ctor_get(v_l_1045_, 2);
                    leanh::lean_dec(v_unused_1306_);
                    v_unused_1307_ = leanh::lean_ctor_get(v_l_1045_, 1);
                    leanh::lean_dec(v_unused_1307_);
                    v_unused_1308_ = leanh::lean_ctor_get(v_l_1045_, 0);
                    leanh::lean_dec(v_unused_1308_);
                    v___x_1298_ = v_l_1045_;
                    v_isShared_1299_ = v_isSharedCheck_1303_;
                    state = 37;
                    continue;
                } else {
                    leanh::lean_dec(v_l_1045_);
                    v___x_1298_ = leanh::lean_box(0);
                    v_isShared_1299_ = v_isSharedCheck_1303_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1299_ == 0 {
                    leanh::lean_ctor_set(v___x_1298_, 4, v_r_1235_);
                    leanh::lean_ctor_set(v___x_1298_, 3, v___x_1296_);
                    leanh::lean_ctor_set(v___x_1298_, 2, v_v_1233_);
                    leanh::lean_ctor_set(v___x_1298_, 1, v_k_1232_);
                    leanh::lean_ctor_set(v___x_1298_, 0, v___x_1293_);
                    v___x_1301_ = v___x_1298_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___x_1296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1235_);
                    v___x_1301_ = v_reuseFailAlloc_1302_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1301_;
            }
            39 => {
                return v___x_1324_;
            }
            40 => {
                v_size_1334_ = leanh::lean_ctor_get(v_l_1326_, 0);
                v___x_1335_ = leanh::lean_unsigned_to_nat(1);
                v___x_1336_ = lean_nat_add(v___x_1335_, v_size_1328_);
                leanh::lean_dec(v_size_1328_);
                v___x_1337_ = lean_nat_add(v___x_1335_, v_size_1334_);
                if v_isShared_1333_ == 0 {
                    leanh::lean_ctor_set(v___x_1332_, 4, v_l_1326_);
                    leanh::lean_ctor_set(v___x_1332_, 3, v_l_1045_);
                    leanh::lean_ctor_set(v___x_1332_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1332_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1332_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1332_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_l_1045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_l_1326_);
                    v___x_1339_ = v_reuseFailAlloc_1343_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v_r_1327_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1339_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1330_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1329_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1336_);
                    v___x_1341_ = v___x_1048_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1339_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1327_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1341_;
            }
            43 => {
                v_k_1352_ = leanh::lean_ctor_get(v_l_1326_, 1);
                v_v_1353_ = leanh::lean_ctor_get(v_l_1326_, 2);
                v_isSharedCheck_1368_ = (!leanh::lean_is_exclusive(v_l_1326_)) as u8;
                if v_isSharedCheck_1368_ == 0 {
                    v_unused_1369_ = leanh::lean_ctor_get(v_l_1326_, 4);
                    leanh::lean_dec(v_unused_1369_);
                    v_unused_1370_ = leanh::lean_ctor_get(v_l_1326_, 3);
                    leanh::lean_dec(v_unused_1370_);
                    v_unused_1371_ = leanh::lean_ctor_get(v_l_1326_, 0);
                    leanh::lean_dec(v_unused_1371_);
                    v___x_1355_ = v_l_1326_;
                    v_isShared_1356_ = v_isSharedCheck_1368_;
                    state = 44;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1353_);
                    leanh::lean_inc(v_k_1352_);
                    leanh::lean_dec(v_l_1326_);
                    v___x_1355_ = leanh::lean_box(0);
                    v_isShared_1356_ = v_isSharedCheck_1368_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_1357_ = leanh::lean_unsigned_to_nat(3);
                v___x_1358_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1356_ == 0 {
                    leanh::lean_ctor_set(v___x_1355_, 4, v_r_1327_);
                    leanh::lean_ctor_set(v___x_1355_, 3, v_r_1327_);
                    leanh::lean_ctor_set(v___x_1355_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1355_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1355_, 0, v___x_1358_);
                    v___x_1360_ = v___x_1355_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_r_1327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_r_1327_);
                    v___x_1360_ = v_reuseFailAlloc_1367_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1351_ == 0 {
                    leanh::lean_ctor_set(v___x_1350_, 3, v_r_1327_);
                    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1358_);
                    v___x_1362_ = v___x_1350_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1327_);
                    v___x_1362_ = v_reuseFailAlloc_1366_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v___x_1362_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1360_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1353_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1352_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1357_);
                    v___x_1364_ = v___x_1048_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1365_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 4, v___x_1362_);
                    v___x_1364_ = v_reuseFailAlloc_1365_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1364_;
            }
            48 => {
                v___x_1382_ = leanh::lean_unsigned_to_nat(3);
                v___x_1383_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1381_ == 0 {
                    leanh::lean_ctor_set(v___x_1380_, 4, v_l_1326_);
                    leanh::lean_ctor_set(v___x_1380_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v___x_1380_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v___x_1380_, 0, v___x_1383_);
                    v___x_1385_ = v___x_1380_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_l_1326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_l_1326_);
                    v___x_1385_ = v_reuseFailAlloc_1389_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_1049_ == 0 {
                    leanh::lean_ctor_set(v___x_1048_, 4, v_r_1376_);
                    leanh::lean_ctor_set(v___x_1048_, 3, v___x_1385_);
                    leanh::lean_ctor_set(v___x_1048_, 2, v_v_1378_);
                    leanh::lean_ctor_set(v___x_1048_, 1, v_k_1377_);
                    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1382_);
                    v___x_1387_ = v___x_1048_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___x_1385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_r_1376_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_1387_;
            }
            51 => {
                return v___x_1396_;
            }
            52 => {
                return v___x_1400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(
    mut v_val_1405_: *mut leanh::LeanObject,
    mut v_k_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v_t_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_k_1406_) == 0 {
                    v___x_1407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1407_, 0, v_val_1405_);
                    v___x_1408_ = leanh::lean_box(1);
                    v___x_1409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1409_, 0, v___x_1407_);
                    leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
                    return v___x_1409_;
                } else {
                    v_head_1410_ = leanh::lean_ctor_get(v_k_1406_, 0);
                    v_tail_1411_ = leanh::lean_ctor_get(v_k_1406_, 1);
                    v_isSharedCheck_1422_ = (!leanh::lean_is_exclusive(v_k_1406_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1413_ = v_k_1406_;
                        v_isShared_1414_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1411_);
                        leanh::lean_inc(v_head_1410_);
                        leanh::lean_dec(v_k_1406_);
                        v___x_1413_ = leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_t_1415_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1405_, v_tail_1411_);
                v___x_1416_ = leanh::lean_box(0);
                v___x_1417_ = leanh::lean_box(1);
                v___x_1418_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_1410_, v_t_1415_, v___x_1417_);
                if v_isShared_1414_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1413_, 0);
                    leanh::lean_ctor_set(v___x_1413_, 1, v___x_1418_);
                    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1416_);
                    v___x_1420_ = v___x_1413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(
    mut v_val_1423_: *mut leanh::LeanObject,
    mut v_x_1424_: *mut leanh::LeanObject,
    mut v_x_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_unused_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v_head_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1425_) == 0 {
                    v_a_1426_ = leanh::lean_ctor_get(v_x_1424_, 1);
                    v_isSharedCheck_1434_ = (!leanh::lean_is_exclusive(v_x_1424_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v_unused_1435_ = leanh::lean_ctor_get(v_x_1424_, 0);
                        leanh::lean_dec(v_unused_1435_);
                        v___x_1428_ = v_x_1424_;
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1426_);
                        leanh::lean_dec(v_x_1424_);
                        v___x_1428_ = leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1436_ = leanh::lean_ctor_get(v_x_1424_, 0);
                    v_a_1437_ = leanh::lean_ctor_get(v_x_1424_, 1);
                    v_isSharedCheck_1453_ = (!leanh::lean_is_exclusive(v_x_1424_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1439_ = v_x_1424_;
                        v_isShared_1440_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1437_);
                        leanh::lean_inc(v_a_1436_);
                        leanh::lean_dec(v_x_1424_);
                        v___x_1439_ = leanh::lean_box(0);
                        v_isShared_1440_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1430_, 0, v_val_1423_);
                if v_isShared_1429_ == 0 {
                    leanh::lean_ctor_set(v___x_1428_, 0, v___x_1430_);
                    v___x_1432_ = v___x_1428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_a_1426_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1432_;
            }
            3 => {
                v_head_1441_ = leanh::lean_ctor_get(v_x_1425_, 0);
                leanh::lean_inc(v_head_1441_);
                v_tail_1442_ = leanh::lean_ctor_get(v_x_1425_, 1);
                leanh::lean_inc(v_tail_1442_);
                leanh::lean_dec_ref_known(v_x_1425_, 2);
                v___x_1449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1437_, v_head_1441_);
                if leanh::lean_obj_tag(v___x_1449_) == 0 {
                    v___x_1450_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1423_, v_tail_1442_);
                    v___y_1444_ = v___x_1450_;
                    state = 4;
                    continue;
                } else {
                    v_val_1451_ = leanh::lean_ctor_get(v___x_1449_, 0);
                    leanh::lean_inc(v_val_1451_);
                    leanh::lean_dec_ref_known(v___x_1449_, 1);
                    v___x_1452_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_1423_, v_val_1451_, v_tail_1442_);
                    v___y_1444_ = v___x_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_1441_, v___y_1444_, v_a_1437_);
                if v_isShared_1440_ == 0 {
                    leanh::lean_ctor_set(v___x_1439_, 1, v___x_1445_);
                    v___x_1447_ = v___x_1439_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1445_);
                    v___x_1447_ = v_reuseFailAlloc_1448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1447_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameTrie_insert___redArg(
    mut v_t_1454_: *mut leanh::LeanObject,
    mut v_n_1455_: *mut leanh::LeanObject,
    mut v_b_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_1455_);
    v___x_1458_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_1456_, v_t_1454_, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn l_Lean_NameTrie_insert___redArg___boxed(
    mut v_t_1459_: *mut leanh::LeanObject,
    mut v_n_1460_: *mut leanh::LeanObject,
    mut v_b_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Lean_NameTrie_insert___redArg(v_t_1459_, v_n_1460_, v_b_1461_);
    leanh::lean_dec(v_n_1460_);
    return v_res_1462_;
}
pub unsafe fn l_Lean_NameTrie_insert(
    mut v_00_u03b2_1463_: *mut leanh::LeanObject,
    mut v_t_1464_: *mut leanh::LeanObject,
    mut v_n_1465_: *mut leanh::LeanObject,
    mut v_b_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Lean_NameTrie_insert___redArg(v_t_1464_, v_n_1465_, v_b_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lean_NameTrie_insert___boxed(
    mut v_00_u03b2_1468_: *mut leanh::LeanObject,
    mut v_t_1469_: *mut leanh::LeanObject,
    mut v_n_1470_: *mut leanh::LeanObject,
    mut v_b_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_NameTrie_insert(v_00_u03b2_1468_, v_t_1469_, v_n_1470_, v_b_1471_);
    leanh::lean_dec(v_n_1470_);
    return v_res_1472_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(
    mut v_00_u03b2_1473_: *mut leanh::LeanObject,
    mut v_val_1474_: *mut leanh::LeanObject,
    mut v_x_1475_: *mut leanh::LeanObject,
    mut v_x_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_1474_, v_x_1475_, v_x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1478_: *mut leanh::LeanObject,
    mut v_msg_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(
    mut v_00_u03b2_1481_: *mut leanh::LeanObject,
    mut v_k_1482_: *mut leanh::LeanObject,
    mut v_v_1483_: *mut leanh::LeanObject,
    mut v_t_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1482_, v_v_1483_, v_t_1484_);
    return v___x_1485_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(
    mut v_00_u03b4_1486_: *mut leanh::LeanObject,
    mut v_t_1487_: *mut leanh::LeanObject,
    mut v_k_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_1487_, v_k_1488_);
    return v___x_1489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(
    mut v_00_u03b4_1490_: *mut leanh::LeanObject,
    mut v_t_1491_: *mut leanh::LeanObject,
    mut v_k_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_1490_, v_t_1491_, v_k_1492_);
    leanh::lean_dec_ref(v_k_1492_);
    leanh::lean_dec(v_t_1491_);
    return v_res_1493_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(
    mut v_00_u03b2_1494_: *mut leanh::LeanObject,
    mut v_val_1495_: *mut leanh::LeanObject,
    mut v_k_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1495_, v_k_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_NameTrie_empty___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1500_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1499_,
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_NameTrie_empty(
    mut v_00_u03b2_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_empty___closed__1_once),
        _init_l_Lean_NameTrie_empty___closed__1,
    );
    return v___x_1502_;
}
pub unsafe fn _init_l_Lean_instInhabitedNameTrie___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lean_NameTrie_empty(leanh::lean_box(0));
    return v___x_1503_;
}
pub unsafe fn l_Lean_instInhabitedNameTrie(
    mut v_00_u03b2_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0_once),
        _init_l_Lean_instInhabitedNameTrie___closed__0,
    );
    return v___x_1505_;
}
pub unsafe fn l_Lean_instEmptyCollectionNameTrie(
    mut v_00_u03b2_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0_once),
        _init_l_Lean_instInhabitedNameTrie___closed__0,
    );
    return v___x_1507_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(
    mut v_x_1508_: *mut leanh::LeanObject,
    mut v_x_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1509_) == 0 {
                    v_a_1510_ = leanh::lean_ctor_get(v_x_1508_, 0);
                    leanh::lean_inc(v_a_1510_);
                    leanh::lean_dec_ref(v_x_1508_);
                    return v_a_1510_;
                } else {
                    v_a_1511_ = leanh::lean_ctor_get(v_x_1508_, 1);
                    leanh::lean_inc(v_a_1511_);
                    leanh::lean_dec_ref(v_x_1508_);
                    v_head_1512_ = leanh::lean_ctor_get(v_x_1509_, 0);
                    v_tail_1513_ = leanh::lean_ctor_get(v_x_1509_, 1);
                    v___x_1514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1511_, v_head_1512_);
                    leanh::lean_dec(v_a_1511_);
                    if leanh::lean_obj_tag(v___x_1514_) == 0 {
                        v___x_1515_ = leanh::lean_box(0);
                        return v___x_1515_;
                    } else {
                        v_val_1516_ = leanh::lean_ctor_get(v___x_1514_, 0);
                        leanh::lean_inc(v_val_1516_);
                        leanh::lean_dec_ref_known(v___x_1514_, 1);
                        v_x_1508_ = v_val_1516_;
                        v_x_1509_ = v_tail_1513_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(
    mut v_x_1518_: *mut leanh::LeanObject,
    mut v_x_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_1518_, v_x_1519_);
    leanh::lean_dec(v_x_1519_);
    return v_res_1520_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___redArg(
    mut v_t_1521_: *mut leanh::LeanObject,
    mut v_k_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1522_);
    v___x_1524_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_1521_, v___x_1523_);
    leanh::lean_dec(v___x_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___redArg___boxed(
    mut v_t_1525_: *mut leanh::LeanObject,
    mut v_k_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ = l_Lean_NameTrie_find_x3f___redArg(v_t_1525_, v_k_1526_);
    leanh::lean_dec(v_k_1526_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f(
    mut v_00_u03b2_1528_: *mut leanh::LeanObject,
    mut v_t_1529_: *mut leanh::LeanObject,
    mut v_k_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_NameTrie_find_x3f___redArg(v_t_1529_, v_k_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___boxed(
    mut v_00_u03b2_1532_: *mut leanh::LeanObject,
    mut v_t_1533_: *mut leanh::LeanObject,
    mut v_k_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_1532_, v_t_1533_, v_k_1534_);
    leanh::lean_dec(v_k_1534_);
    return v_res_1535_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(
    mut v_00_u03b2_1536_: *mut leanh::LeanObject,
    mut v_x_1537_: *mut leanh::LeanObject,
    mut v_x_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_1537_, v_x_1538_);
    return v___x_1539_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(
    mut v_00_u03b2_1540_: *mut leanh::LeanObject,
    mut v_x_1541_: *mut leanh::LeanObject,
    mut v_x_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_1540_, v_x_1541_, v_x_1542_);
    leanh::lean_dec(v_x_1542_);
    return v_res_1543_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___redArg(
    mut v_t_1544_: *mut leanh::LeanObject,
    mut v_k_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1547_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1545_);
    v___x_1548_ = leanh::lean_box(0);
    v___x_1549_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1546_,
            v___x_1548_,
            v_t_1544_,
            v___x_1547_,
        );
    return v___x_1549_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(
    mut v_t_1550_: *mut leanh::LeanObject,
    mut v_k_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_1550_, v_k_1551_);
    leanh::lean_dec(v_k_1551_);
    return v_res_1552_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f(
    mut v_00_u03b2_1553_: *mut leanh::LeanObject,
    mut v_t_1554_: *mut leanh::LeanObject,
    mut v_k_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1557_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1555_);
    v___x_1558_ = leanh::lean_box(0);
    v___x_1559_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1556_,
            v___x_1558_,
            v_t_1554_,
            v___x_1557_,
        );
    return v___x_1559_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___boxed(
    mut v_00_u03b2_1560_: *mut leanh::LeanObject,
    mut v_t_1561_: *mut leanh::LeanObject,
    mut v_k_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_1560_, v_t_1561_, v_k_1562_);
    leanh::lean_dec(v_k_1562_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM___redArg(
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_t_1565_: *mut leanh::LeanObject,
    mut v_k_1566_: *mut leanh::LeanObject,
    mut v_init_1567_: *mut leanh::LeanObject,
    mut v_f_1568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1570_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1566_);
    leanh::lean_inc(v_init_1567_);
    v___x_1571_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1564_,
        v___x_1569_,
        v_init_1567_,
        v_f_1568_,
        v___x_1570_,
        v_t_1565_,
        v_init_1567_,
    );
    return v___x_1571_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM___redArg___boxed(
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_t_1573_: *mut leanh::LeanObject,
    mut v_k_1574_: *mut leanh::LeanObject,
    mut v_init_1575_: *mut leanh::LeanObject,
    mut v_f_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Lean_NameTrie_foldMatchingM___redArg(
        v_inst_1572_,
        v_t_1573_,
        v_k_1574_,
        v_init_1575_,
        v_f_1576_,
    );
    leanh::lean_dec(v_k_1574_);
    return v_res_1577_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM(
    mut v_m_1578_: *mut leanh::LeanObject,
    mut v_00_u03b2_1579_: *mut leanh::LeanObject,
    mut v_00_u03c3_1580_: *mut leanh::LeanObject,
    mut v_inst_1581_: *mut leanh::LeanObject,
    mut v_t_1582_: *mut leanh::LeanObject,
    mut v_k_1583_: *mut leanh::LeanObject,
    mut v_init_1584_: *mut leanh::LeanObject,
    mut v_f_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1587_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1583_);
    leanh::lean_inc(v_init_1584_);
    v___x_1588_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1581_,
        v___x_1586_,
        v_init_1584_,
        v_f_1585_,
        v___x_1587_,
        v_t_1582_,
        v_init_1584_,
    );
    return v___x_1588_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM___boxed(
    mut v_m_1589_: *mut leanh::LeanObject,
    mut v_00_u03b2_1590_: *mut leanh::LeanObject,
    mut v_00_u03c3_1591_: *mut leanh::LeanObject,
    mut v_inst_1592_: *mut leanh::LeanObject,
    mut v_t_1593_: *mut leanh::LeanObject,
    mut v_k_1594_: *mut leanh::LeanObject,
    mut v_init_1595_: *mut leanh::LeanObject,
    mut v_f_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_Lean_NameTrie_foldMatchingM(
        v_m_1589_,
        v_00_u03b2_1590_,
        v_00_u03c3_1591_,
        v_inst_1592_,
        v_t_1593_,
        v_k_1594_,
        v_init_1595_,
        v_f_1596_,
    );
    leanh::lean_dec(v_k_1594_);
    return v_res_1597_;
}
pub unsafe fn _init_l_Lean_NameTrie_foldM___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = leanh::lean_box(0);
    v___x_1599_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_NameTrie_foldM___redArg(
    mut v_inst_1600_: *mut leanh::LeanObject,
    mut v_t_1601_: *mut leanh::LeanObject,
    mut v_init_1602_: *mut leanh::LeanObject,
    mut v_f_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1605_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    leanh::lean_inc(v_init_1602_);
    v___x_1606_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1600_,
        v___x_1604_,
        v_init_1602_,
        v_f_1603_,
        v___x_1605_,
        v_t_1601_,
        v_init_1602_,
    );
    return v___x_1606_;
}
pub unsafe fn l_Lean_NameTrie_foldM(
    mut v_m_1607_: *mut leanh::LeanObject,
    mut v_00_u03b2_1608_: *mut leanh::LeanObject,
    mut v_00_u03c3_1609_: *mut leanh::LeanObject,
    mut v_inst_1610_: *mut leanh::LeanObject,
    mut v_t_1611_: *mut leanh::LeanObject,
    mut v_init_1612_: *mut leanh::LeanObject,
    mut v_f_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1615_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    leanh::lean_inc(v_init_1612_);
    v___x_1616_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1610_,
        v___x_1614_,
        v_init_1612_,
        v_f_1613_,
        v___x_1615_,
        v_t_1611_,
        v_init_1612_,
    );
    return v___x_1616_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM___redArg___lam__0(
    mut v_f_1617_: *mut leanh::LeanObject,
    mut v_b_1618_: *mut leanh::LeanObject,
    mut v_x_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = leanh::lean_apply_1(v_f_1617_, v_b_1618_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM___redArg(
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_t_1622_: *mut leanh::LeanObject,
    mut v_k_1623_: *mut leanh::LeanObject,
    mut v_f_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1625_ = leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1625_, 0, v_f_1624_);
    v___x_1626_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1627_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1623_);
    v___x_1628_ = leanh::lean_box(0);
    v___x_1629_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1621_,
        v___x_1626_,
        v___x_1628_,
        v___f_1625_,
        v___x_1627_,
        v_t_1622_,
        v___x_1628_,
    );
    return v___x_1629_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM___redArg___boxed(
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_t_1631_: *mut leanh::LeanObject,
    mut v_k_1632_: *mut leanh::LeanObject,
    mut v_f_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ =
        l_Lean_NameTrie_forMatchingM___redArg(v_inst_1630_, v_t_1631_, v_k_1632_, v_f_1633_);
    leanh::lean_dec(v_k_1632_);
    return v_res_1634_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM(
    mut v_m_1635_: *mut leanh::LeanObject,
    mut v_00_u03b2_1636_: *mut leanh::LeanObject,
    mut v_inst_1637_: *mut leanh::LeanObject,
    mut v_t_1638_: *mut leanh::LeanObject,
    mut v_k_1639_: *mut leanh::LeanObject,
    mut v_f_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1641_ = leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1641_, 0, v_f_1640_);
    v___x_1642_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1643_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1639_);
    v___x_1644_ = leanh::lean_box(0);
    v___x_1645_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1637_,
        v___x_1642_,
        v___x_1644_,
        v___f_1641_,
        v___x_1643_,
        v_t_1638_,
        v___x_1644_,
    );
    return v___x_1645_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM___boxed(
    mut v_m_1646_: *mut leanh::LeanObject,
    mut v_00_u03b2_1647_: *mut leanh::LeanObject,
    mut v_inst_1648_: *mut leanh::LeanObject,
    mut v_t_1649_: *mut leanh::LeanObject,
    mut v_k_1650_: *mut leanh::LeanObject,
    mut v_f_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_NameTrie_forMatchingM(
        v_m_1646_,
        v_00_u03b2_1647_,
        v_inst_1648_,
        v_t_1649_,
        v_k_1650_,
        v_f_1651_,
    );
    leanh::lean_dec(v_k_1650_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_NameTrie_forM___redArg(
    mut v_inst_1653_: *mut leanh::LeanObject,
    mut v_t_1654_: *mut leanh::LeanObject,
    mut v_f_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1656_ = leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1656_, 0, v_f_1655_);
    v___x_1657_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1658_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1659_ = leanh::lean_box(0);
    v___x_1660_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1653_,
        v___x_1657_,
        v___x_1659_,
        v___f_1656_,
        v___x_1658_,
        v_t_1654_,
        v___x_1659_,
    );
    return v___x_1660_;
}
pub unsafe fn l_Lean_NameTrie_forM(
    mut v_m_1661_: *mut leanh::LeanObject,
    mut v_00_u03b2_1662_: *mut leanh::LeanObject,
    mut v_inst_1663_: *mut leanh::LeanObject,
    mut v_t_1664_: *mut leanh::LeanObject,
    mut v_f_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1666_ = leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1666_, 0, v_f_1665_);
    v___x_1667_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1669_ = leanh::lean_box(0);
    v___x_1670_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1663_,
        v___x_1667_,
        v___x_1669_,
        v___f_1666_,
        v___x_1668_,
        v_t_1664_,
        v___x_1669_,
    );
    return v___x_1670_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(
    mut v_a_1671_: *mut leanh::LeanObject,
    mut v_a_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1673_ = leanh::lean_ctor_get(v_a_1671_, 0);
    if leanh::lean_obj_tag(v_a_1673_) == 0 {
        let mut v_a_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1674_ = leanh::lean_ctor_get(v_a_1671_, 1);
        leanh::lean_inc(v_a_1674_);
        leanh::lean_dec_ref(v_a_1671_);
        v___x_1675_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_1672_, v_a_1674_);
        return v___x_1675_;
    } else {
        let mut v_a_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_a_1673_);
        v_a_1676_ = leanh::lean_ctor_get(v_a_1671_, 1);
        leanh::lean_inc(v_a_1676_);
        leanh::lean_dec_ref(v_a_1671_);
        v_val_1677_ = leanh::lean_ctor_get(v_a_1673_, 0);
        leanh::lean_inc(v_val_1677_);
        leanh::lean_dec_ref_known(v_a_1673_, 1);
        v___x_1678_ = lean_array_push(v_a_1672_, v_val_1677_);
        v___x_1679_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_1678_, v_a_1676_);
        return v___x_1679_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(
    mut v_init_1680_: *mut leanh::LeanObject,
    mut v_x_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1681_) == 0 {
                    v_v_1682_ = leanh::lean_ctor_get(v_x_1681_, 2);
                    leanh::lean_inc(v_v_1682_);
                    v_l_1683_ = leanh::lean_ctor_get(v_x_1681_, 3);
                    leanh::lean_inc(v_l_1683_);
                    v_r_1684_ = leanh::lean_ctor_get(v_x_1681_, 4);
                    leanh::lean_inc(v_r_1684_);
                    leanh::lean_dec_ref_known(v_x_1681_, 5);
                    v___x_1685_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_1680_, v_l_1683_);
                    v___x_1686_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_v_1682_, v___x_1685_);
                    v_init_1680_ = v___x_1686_;
                    v_x_1681_ = v_r_1684_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1680_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(
    mut v_init_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v_a_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1689_) == 0 {
                    v___x_1692_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_1690_, v_a_1691_);
                    return v___x_1692_;
                } else {
                    v_head_1693_ = leanh::lean_ctor_get(v_a_1689_, 0);
                    v_tail_1694_ = leanh::lean_ctor_get(v_a_1689_, 1);
                    v_a_1695_ = leanh::lean_ctor_get(v_a_1690_, 1);
                    leanh::lean_inc(v_a_1695_);
                    leanh::lean_dec_ref(v_a_1690_);
                    v___x_1696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1695_, v_head_1693_);
                    leanh::lean_dec(v_a_1695_);
                    if leanh::lean_obj_tag(v___x_1696_) == 0 {
                        leanh::lean_dec_ref(v_a_1691_);
                        leanh::lean_inc_ref(v_init_1688_);
                        return v_init_1688_;
                    } else {
                        v_val_1697_ = leanh::lean_ctor_get(v___x_1696_, 0);
                        leanh::lean_inc(v_val_1697_);
                        leanh::lean_dec_ref_known(v___x_1696_, 1);
                        v_a_1689_ = v_tail_1694_;
                        v_a_1690_ = v_val_1697_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(
    mut v_init_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
    mut v_a_1701_: *mut leanh::LeanObject,
    mut v_a_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
    leanh::lean_dec(v_a_1700_);
    leanh::lean_dec_ref(v_init_1699_);
    return v_res_1703_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___redArg(
    mut v_t_1706_: *mut leanh::LeanObject,
    mut v_k_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_NameTrie_matchingToArray___redArg___closed__0;
    v___x_1709_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1707_);
    v___x_1710_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_1708_, v___x_1709_, v_t_1706_, v___x_1708_);
    leanh::lean_dec(v___x_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___redArg___boxed(
    mut v_t_1711_: *mut leanh::LeanObject,
    mut v_k_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_1711_, v_k_1712_);
    leanh::lean_dec(v_k_1712_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray(
    mut v_00_u03b2_1714_: *mut leanh::LeanObject,
    mut v_t_1715_: *mut leanh::LeanObject,
    mut v_k_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_1715_, v_k_1716_);
    return v___x_1717_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___boxed(
    mut v_00_u03b2_1718_: *mut leanh::LeanObject,
    mut v_t_1719_: *mut leanh::LeanObject,
    mut v_k_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_1718_, v_t_1719_, v_k_1720_);
    leanh::lean_dec(v_k_1720_);
    return v_res_1721_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(
    mut v_00_u03b2_1722_: *mut leanh::LeanObject,
    mut v_init_1723_: *mut leanh::LeanObject,
    mut v_a_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_a_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
    return v___x_1727_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(
    mut v_00_u03b2_1728_: *mut leanh::LeanObject,
    mut v_init_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
    mut v_a_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_1728_, v_init_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
    leanh::lean_dec(v_a_1730_);
    leanh::lean_dec_ref(v_init_1729_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(
    mut v_00_u03b2_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
    mut v_a_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_1735_, v_a_1736_);
    return v___x_1737_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1738_: *mut leanh::LeanObject,
    mut v_init_1739_: *mut leanh::LeanObject,
    mut v_x_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_1739_, v_x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Lean_NameTrie_toArray___redArg(
    mut v_t_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Lean_NameTrie_matchingToArray___redArg___closed__0;
    v___x_1744_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1745_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_1743_, v___x_1744_, v_t_1742_, v___x_1743_);
    return v___x_1745_;
}
pub unsafe fn l_Lean_NameTrie_toArray(
    mut v_00_u03b2_1746_: *mut leanh::LeanObject,
    mut v_t_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_NameTrie_toArray___redArg(v_t_1747_);
    return v___x_1748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_NameTrie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_PrefixTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_NameTrie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_NameTrie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_PrefixTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameTrie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_NameTrie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_NameTrie(builtin);
}