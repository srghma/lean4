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
pub static l_Lean_instBEqNamePart___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqNamePart_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqNamePart___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqNamePart___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqNamePart: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqNamePart___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedNamePart_default___closed__0_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instInhabitedNamePart_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedNamePart_default___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedNamePart_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNamePart_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNamePart: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNamePart_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToStringNamePart___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToStringNamePart___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToStringNamePart___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringNamePart___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instToStringNamePart: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringNamePart___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_NameTrie_empty___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_NamePart_cmp___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameTrie_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameTrie_empty___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_NameTrie_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_NameTrie_empty___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedNameTrie___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedNameTrie___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_NameTrie_foldM___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_NameTrie_foldM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_NameTrie_matchingToArray___redArg___closed__0_value:
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
static mut l_Lean_NameTrie_matchingToArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameTrie_matchingToArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_NamePart_ctorIdx(
    mut v_x_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_875_) == 0 {
        let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_876_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_876_;
    } else {
        let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_877_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_877_;
    }
}
pub unsafe fn l_Lean_NamePart_ctorIdx___boxed(
    mut v_x_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_NamePart_ctorIdx(v_x_878_);
    crate::leanh::lean_dec_ref(v_x_878_);
    return v_res_879_;
}
pub unsafe fn l_Lean_NamePart_ctorElim___redArg(
    mut v_t_880_: *mut crate::leanh::LeanObject,
    mut v_k_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_880_) == 0 {
        let mut v_s_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_882_ = crate::leanh::lean_ctor_get(v_t_880_, 0);
        crate::leanh::lean_inc_ref(v_s_882_);
        crate::leanh::lean_dec_ref_known(v_t_880_, 1);
        v___x_883_ = crate::leanh::lean_apply_1(v_k_881_, v_s_882_);
        return v___x_883_;
    } else {
        let mut v_n_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_n_884_ = crate::leanh::lean_ctor_get(v_t_880_, 0);
        crate::leanh::lean_inc(v_n_884_);
        crate::leanh::lean_dec_ref_known(v_t_880_, 1);
        v___x_885_ = crate::leanh::lean_apply_1(v_k_881_, v_n_884_);
        return v___x_885_;
    }
}
pub unsafe fn l_Lean_NamePart_ctorElim(
    mut v_motive_886_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_887_: *mut crate::leanh::LeanObject,
    mut v_t_888_: *mut crate::leanh::LeanObject,
    mut v_h_889_: *mut crate::leanh::LeanObject,
    mut v_k_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_NamePart_ctorElim___redArg(v_t_888_, v_k_890_);
    return v___x_891_;
}
pub unsafe fn l_Lean_NamePart_ctorElim___boxed(
    mut v_motive_892_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_893_: *mut crate::leanh::LeanObject,
    mut v_t_894_: *mut crate::leanh::LeanObject,
    mut v_h_895_: *mut crate::leanh::LeanObject,
    mut v_k_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_897_ =
        l_Lean_NamePart_ctorElim(v_motive_892_, v_ctorIdx_893_, v_t_894_, v_h_895_, v_k_896_);
    crate::leanh::lean_dec(v_ctorIdx_893_);
    return v_res_897_;
}
pub unsafe fn l_Lean_NamePart_str_elim___redArg(
    mut v_t_898_: *mut crate::leanh::LeanObject,
    mut v_str_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_NamePart_ctorElim___redArg(v_t_898_, v_str_899_);
    return v___x_900_;
}
pub unsafe fn l_Lean_NamePart_str_elim(
    mut v_motive_901_: *mut crate::leanh::LeanObject,
    mut v_t_902_: *mut crate::leanh::LeanObject,
    mut v_h_903_: *mut crate::leanh::LeanObject,
    mut v_str_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ = l_Lean_NamePart_ctorElim___redArg(v_t_902_, v_str_904_);
    return v___x_905_;
}
pub unsafe fn l_Lean_NamePart_num_elim___redArg(
    mut v_t_906_: *mut crate::leanh::LeanObject,
    mut v_num_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_908_ = l_Lean_NamePart_ctorElim___redArg(v_t_906_, v_num_907_);
    return v___x_908_;
}
pub unsafe fn l_Lean_NamePart_num_elim(
    mut v_motive_909_: *mut crate::leanh::LeanObject,
    mut v_t_910_: *mut crate::leanh::LeanObject,
    mut v_h_911_: *mut crate::leanh::LeanObject,
    mut v_num_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_NamePart_ctorElim___redArg(v_t_910_, v_num_912_);
    return v___x_913_;
}
pub unsafe fn l_Lean_instBEqNamePart_beq(
    mut v_x_914_: *mut crate::leanh::LeanObject,
    mut v_x_915_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_914_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_915_) == 0 {
            let mut v_s_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_918_: u8 = 0;
            v_s_916_ = crate::leanh::lean_ctor_get(v_x_914_, 0);
            v_s_917_ = crate::leanh::lean_ctor_get(v_x_915_, 0);
            v___x_918_ = lean_string_dec_eq(v_s_916_, v_s_917_);
            return v___x_918_;
        } else {
            let mut v___x_919_: u8 = 0;
            v___x_919_ = 0;
            return v___x_919_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_915_) == 1 {
            let mut v_n_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_922_: u8 = 0;
            v_n_920_ = crate::leanh::lean_ctor_get(v_x_914_, 0);
            v_n_921_ = crate::leanh::lean_ctor_get(v_x_915_, 0);
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
    mut v_x_924_: *mut crate::leanh::LeanObject,
    mut v_x_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_926_: u8 = 0;
    let mut v_r_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_instBEqNamePart_beq(v_x_924_, v_x_925_);
    crate::leanh::lean_dec_ref(v_x_925_);
    crate::leanh::lean_dec_ref(v_x_924_);
    v_r_927_ = crate::leanh::lean_box((v_res_926_) as usize);
    return v_r_927_;
}
pub unsafe fn l_Lean_instToStringNamePart___lam__0(
    mut v_x_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_935_) == 0 {
        let mut v_s_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_936_ = crate::leanh::lean_ctor_get(v_x_935_, 0);
        crate::leanh::lean_inc_ref(v_s_936_);
        crate::leanh::lean_dec_ref_known(v_x_935_, 1);
        return v_s_936_;
    } else {
        let mut v_n_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_n_937_ = crate::leanh::lean_ctor_get(v_x_935_, 0);
        crate::leanh::lean_inc(v_n_937_);
        crate::leanh::lean_dec_ref_known(v_x_935_, 1);
        v___x_938_ = l_Nat_reprFast(v_n_937_);
        return v___x_938_;
    }
}
pub unsafe fn l_Lean_NamePart_cmp(
    mut v_x_941_: *mut crate::leanh::LeanObject,
    mut v_x_942_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_941_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_942_) == 0 {
            let mut v_s_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_945_: u8 = 0;
            v_s_943_ = crate::leanh::lean_ctor_get(v_x_941_, 0);
            v_s_944_ = crate::leanh::lean_ctor_get(v_x_942_, 0);
            v___x_945_ = lean_string_compare(v_s_943_, v_s_944_);
            return v___x_945_;
        } else {
            let mut v___x_946_: u8 = 0;
            v___x_946_ = 2;
            return v___x_946_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_942_) == 0 {
            let mut v___x_947_: u8 = 0;
            v___x_947_ = 0;
            return v___x_947_;
        } else {
            let mut v_n_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_950_: u8 = 0;
            v_n_948_ = crate::leanh::lean_ctor_get(v_x_941_, 0);
            v_n_949_ = crate::leanh::lean_ctor_get(v_x_942_, 0);
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
    mut v_x_955_: *mut crate::leanh::LeanObject,
    mut v_x_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_957_: u8 = 0;
    let mut v_r_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_Lean_NamePart_cmp(v_x_955_, v_x_956_);
    crate::leanh::lean_dec_ref(v_x_956_);
    crate::leanh::lean_dec_ref(v_x_955_);
    v_r_958_ = crate::leanh::lean_box((v_res_957_) as usize);
    return v_r_958_;
}
pub unsafe fn l_Lean_NamePart_lt(
    mut v_x_959_: *mut crate::leanh::LeanObject,
    mut v_x_960_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_959_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_960_) == 0 {
            let mut v_s_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_963_: u8 = 0;
            v_s_961_ = crate::leanh::lean_ctor_get(v_x_959_, 0);
            v_s_962_ = crate::leanh::lean_ctor_get(v_x_960_, 0);
            v___x_963_ = lean_string_dec_lt(v_s_961_, v_s_962_);
            return v___x_963_;
        } else {
            let mut v___x_964_: u8 = 0;
            v___x_964_ = 0;
            return v___x_964_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_960_) == 0 {
            let mut v___x_965_: u8 = 0;
            v___x_965_ = 1;
            return v___x_965_;
        } else {
            let mut v_n_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_968_: u8 = 0;
            v_n_966_ = crate::leanh::lean_ctor_get(v_x_959_, 0);
            v_n_967_ = crate::leanh::lean_ctor_get(v_x_960_, 0);
            v___x_968_ = lean_nat_dec_lt(v_n_966_, v_n_967_);
            return v___x_968_;
        }
    }
}
pub unsafe fn l_Lean_NamePart_lt___boxed(
    mut v_x_969_: *mut crate::leanh::LeanObject,
    mut v_x_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_971_: u8 = 0;
    let mut v_r_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Lean_NamePart_lt(v_x_969_, v_x_970_);
    crate::leanh::lean_dec_ref(v_x_970_);
    crate::leanh::lean_dec_ref(v_x_969_);
    v_r_972_ = crate::leanh::lean_box((v_res_971_) as usize);
    return v_r_972_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(
    mut v_x_973_: *mut crate::leanh::LeanObject,
    mut v_x_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_973_) {
                0 => {
                    return v_x_974_;
                }
                1 => {
                    v_pre_975_ = crate::leanh::lean_ctor_get(v_x_973_, 0);
                    v_str_976_ = crate::leanh::lean_ctor_get(v_x_973_, 1);
                    crate::leanh::lean_inc_ref(v_str_976_);
                    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_977_, 0, v_str_976_);
                    v___x_978_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
                    crate::leanh::lean_ctor_set(v___x_978_, 1, v_x_974_);
                    v_x_973_ = v_pre_975_;
                    v_x_974_ = v___x_978_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_pre_980_ = crate::leanh::lean_ctor_get(v_x_973_, 0);
                    v_i_981_ = crate::leanh::lean_ctor_get(v_x_973_, 1);
                    crate::leanh::lean_inc(v_i_981_);
                    v___x_982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_982_, 0, v_i_981_);
                    v___x_983_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_983_, 0, v___x_982_);
                    crate::leanh::lean_ctor_set(v___x_983_, 1, v_x_974_);
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
    mut v_x_985_: *mut crate::leanh::LeanObject,
    mut v_x_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_987_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_985_, v_x_986_);
    crate::leanh::lean_dec(v_x_985_);
    return v_res_987_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey(
    mut v_n_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = crate::leanh::lean_box(0);
    v___x_990_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_988_, v___x_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(
    mut v_n_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_991_);
    crate::leanh::lean_dec(v_n_991_);
    return v_res_992_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(
    mut v_t_993_: *mut crate::leanh::LeanObject,
    mut v_k_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_993_) == 0 {
                    v_k_995_ = crate::leanh::lean_ctor_get(v_t_993_, 1);
                    v_v_996_ = crate::leanh::lean_ctor_get(v_t_993_, 2);
                    v_l_997_ = crate::leanh::lean_ctor_get(v_t_993_, 3);
                    v_r_998_ = crate::leanh::lean_ctor_get(v_t_993_, 4);
                    v___x_999_ = l_Lean_NamePart_cmp(v_k_994_, v_k_995_);
                    match v___x_999_ {
                        0 => {
                            v_t_993_ = v_l_997_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_996_);
                            v___x_1001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1001_, 0, v_v_996_);
                            return v___x_1001_;
                        }
                        _ => {
                            v_t_993_ = v_r_998_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1003_ = crate::leanh::lean_box(0);
                    return v___x_1003_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(
    mut v_t_1004_: *mut crate::leanh::LeanObject,
    mut v_k_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_1004_, v_k_1005_);
    crate::leanh::lean_dec_ref(v_k_1005_);
    crate::leanh::lean_dec(v_t_1004_);
    return v_res_1006_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = crate::leanh::lean_box(1);
    v___x_1009_ = lean_panic_fn_borrowed(v___x_1008_, v_msg_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2;
    v___x_1014_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1015_ = crate::leanh::lean_unsigned_to_nat(182);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2;
    v___x_1020_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1021_ = crate::leanh::lean_unsigned_to_nat(183);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6;
    v___x_1028_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1029_ = crate::leanh::lean_unsigned_to_nat(276);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6;
    v___x_1034_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1035_ = crate::leanh::lean_unsigned_to_nat(277);
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
    mut v_k_1039_: *mut crate::leanh::LeanObject,
    mut v_v_1040_: *mut crate::leanh::LeanObject,
    mut v_t_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1050_: u8 = 0;
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: u8 = 0;
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v_size_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_unused_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v_unused_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_unused_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_size_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v_unused_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1184_: u8 = 0;
    let mut v_unused_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v_k_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_unused_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_unused_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v_size_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_unused_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_unused_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v_size_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v_unused_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v_k_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_unused_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_unused_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_unused_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1041_) == 0 {
                    v_size_1042_ = crate::leanh::lean_ctor_get(v_t_1041_, 0);
                    v_k_1043_ = crate::leanh::lean_ctor_get(v_t_1041_, 1);
                    v_v_1044_ = crate::leanh::lean_ctor_get(v_t_1041_, 2);
                    v_l_1045_ = crate::leanh::lean_ctor_get(v_t_1041_, 3);
                    v_r_1046_ = crate::leanh::lean_ctor_get(v_t_1041_, 4);
                    v_isSharedCheck_1402_ = (!crate::leanh::lean_is_exclusive(v_t_1041_)) as u8;
                    if v_isSharedCheck_1402_ == 0 {
                        v___x_1048_ = v_t_1041_;
                        v_isShared_1049_ = v_isSharedCheck_1402_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1046_);
                        crate::leanh::lean_inc(v_l_1045_);
                        crate::leanh::lean_inc(v_v_1044_);
                        crate::leanh::lean_inc(v_k_1043_);
                        crate::leanh::lean_inc(v_size_1042_);
                        crate::leanh::lean_dec(v_t_1041_);
                        v___x_1048_ = crate::leanh::lean_box(0);
                        v_isShared_1049_ = v_isSharedCheck_1402_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1403_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1404_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 1, v_k_1039_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 2, v_v_1040_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 3, v_t_1041_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 4, v_t_1041_);
                    return v___x_1404_;
                }
            }
            1 => {
                v___x_1050_ = l_Lean_NamePart_cmp(v_k_1039_, v_k_1043_);
                match v___x_1050_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1042_);
                        v___x_1051_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1039_, v_v_1040_, v_l_1045_);
                        if crate::leanh::lean_obj_tag(v_r_1046_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                                v_size_1052_ = crate::leanh::lean_ctor_get(v_r_1046_, 0);
                                v_size_1053_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                crate::leanh::lean_inc(v_size_1053_);
                                v_k_1054_ = crate::leanh::lean_ctor_get(v___x_1051_, 1);
                                crate::leanh::lean_inc(v_k_1054_);
                                v_v_1055_ = crate::leanh::lean_ctor_get(v___x_1051_, 2);
                                crate::leanh::lean_inc(v_v_1055_);
                                v_l_1056_ = crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                crate::leanh::lean_inc(v_l_1056_);
                                v_r_1057_ = crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                crate::leanh::lean_inc(v_r_1057_);
                                v___x_1058_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1059_ = lean_nat_mul(v___x_1058_, v_size_1052_);
                                v___x_1060_ = lean_nat_dec_lt(v___x_1059_, v_size_1053_);
                                crate::leanh::lean_dec(v___x_1059_);
                                if v___x_1060_ == 0 {
                                    crate::leanh::lean_dec(v_r_1057_);
                                    crate::leanh::lean_dec(v_l_1056_);
                                    crate::leanh::lean_dec(v_v_1055_);
                                    crate::leanh::lean_dec(v_k_1054_);
                                    v___x_1061_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1062_ = lean_nat_add(v___x_1061_, v_size_1053_);
                                    crate::leanh::lean_dec(v_size_1053_);
                                    v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1052_);
                                    crate::leanh::lean_dec(v___x_1062_);
                                    if v_isShared_1049_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                        crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1063_);
                                        v___x_1065_ = v___x_1048_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1066_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            0,
                                            v___x_1063_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            1,
                                            v_k_1043_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            2,
                                            v_v_1044_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1066_,
                                            3,
                                            v___x_1051_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                                        (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1138_ == 0 {
                                        v_unused_1139_ =
                                            crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                        crate::leanh::lean_dec(v_unused_1139_);
                                        v_unused_1140_ =
                                            crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                        crate::leanh::lean_dec(v_unused_1140_);
                                        v_unused_1141_ =
                                            crate::leanh::lean_ctor_get(v___x_1051_, 2);
                                        crate::leanh::lean_dec(v_unused_1141_);
                                        v_unused_1142_ =
                                            crate::leanh::lean_ctor_get(v___x_1051_, 1);
                                        crate::leanh::lean_dec(v_unused_1142_);
                                        v_unused_1143_ =
                                            crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                        crate::leanh::lean_dec(v_unused_1143_);
                                        v___x_1068_ = v___x_1051_;
                                        v_isShared_1069_ = v_isSharedCheck_1138_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1051_);
                                        v___x_1068_ = crate::leanh::lean_box(0);
                                        v_isShared_1069_ = v_isSharedCheck_1138_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1144_ = crate::leanh::lean_ctor_get(v_r_1046_, 0);
                                v___x_1145_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1146_ = lean_nat_add(v___x_1145_, v_size_1144_);
                                if v_isShared_1049_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1146_);
                                    v___x_1148_ = v___x_1048_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1149_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        0,
                                        v___x_1146_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        1,
                                        v_k_1043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        2,
                                        v_v_1044_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1149_,
                                        3,
                                        v___x_1051_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                                v_l_1150_ = crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                crate::leanh::lean_inc(v_l_1150_);
                                if crate::leanh::lean_obj_tag(v_l_1150_) == 0 {
                                    v_r_1151_ = crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                    crate::leanh::lean_inc(v_r_1151_);
                                    if crate::leanh::lean_obj_tag(v_r_1151_) == 0 {
                                        v_size_1152_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                        v_k_1153_ = crate::leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1154_ = crate::leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1168_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1168_ == 0 {
                                            v_unused_1169_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                            crate::leanh::lean_dec(v_unused_1169_);
                                            v_unused_1170_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                            crate::leanh::lean_dec(v_unused_1170_);
                                            v___x_1156_ = v___x_1051_;
                                            v_isShared_1157_ = v_isSharedCheck_1168_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1154_);
                                            crate::leanh::lean_inc(v_k_1153_);
                                            crate::leanh::lean_inc(v_size_1152_);
                                            crate::leanh::lean_dec(v___x_1051_);
                                            v___x_1156_ = crate::leanh::lean_box(0);
                                            v_isShared_1157_ = v_isSharedCheck_1168_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1171_ = crate::leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1172_ = crate::leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1184_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1184_ == 0 {
                                            v_unused_1185_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                            crate::leanh::lean_dec(v_unused_1185_);
                                            v_unused_1186_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                            crate::leanh::lean_dec(v_unused_1186_);
                                            v_unused_1187_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                            crate::leanh::lean_dec(v_unused_1187_);
                                            v___x_1174_ = v___x_1051_;
                                            v_isShared_1175_ = v_isSharedCheck_1184_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1172_);
                                            crate::leanh::lean_inc(v_k_1171_);
                                            crate::leanh::lean_dec(v___x_1051_);
                                            v___x_1174_ = crate::leanh::lean_box(0);
                                            v_isShared_1175_ = v_isSharedCheck_1184_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1188_ = crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                    crate::leanh::lean_inc(v_r_1188_);
                                    if crate::leanh::lean_obj_tag(v_r_1188_) == 0 {
                                        v_k_1189_ = crate::leanh::lean_ctor_get(v___x_1051_, 1);
                                        v_v_1190_ = crate::leanh::lean_ctor_get(v___x_1051_, 2);
                                        v_isSharedCheck_1214_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1214_ == 0 {
                                            v_unused_1215_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 4);
                                            crate::leanh::lean_dec(v_unused_1215_);
                                            v_unused_1216_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 3);
                                            crate::leanh::lean_dec(v_unused_1216_);
                                            v_unused_1217_ =
                                                crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                            crate::leanh::lean_dec(v_unused_1217_);
                                            v___x_1192_ = v___x_1051_;
                                            v_isShared_1193_ = v_isSharedCheck_1214_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1190_);
                                            crate::leanh::lean_inc(v_k_1189_);
                                            crate::leanh::lean_dec(v___x_1051_);
                                            v___x_1192_ = crate::leanh::lean_box(0);
                                            v_isShared_1193_ = v_isSharedCheck_1214_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1218_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1049_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_1048_, 4, v_r_1188_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1048_,
                                                3,
                                                v___x_1051_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1048_,
                                                0,
                                                v___x_1218_,
                                            );
                                            v___x_1220_ = v___x_1048_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1221_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                0,
                                                v___x_1218_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                1,
                                                v_k_1043_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                2,
                                                v_v_1044_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1221_,
                                                3,
                                                v___x_1051_,
                                            );
                                            crate::leanh::lean_ctor_set(
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
                                v___x_1222_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1049_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1051_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1051_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1222_);
                                    v___x_1224_ = v___x_1048_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1225_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        0,
                                        v___x_1222_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        1,
                                        v_k_1043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        2,
                                        v_v_1044_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1225_,
                                        3,
                                        v___x_1051_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_1044_);
                        crate::leanh::lean_dec(v_k_1043_);
                        if v_isShared_1049_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1040_);
                            crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1039_);
                            v___x_1227_ = v___x_1048_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_1228_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_size_1042_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1039_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1040_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_l_1045_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1046_);
                            v___x_1227_ = v_reuseFailAlloc_1228_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1042_);
                        v___x_1229_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1039_, v_v_1040_, v_r_1046_);
                        if crate::leanh::lean_obj_tag(v_l_1045_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_1229_) == 0 {
                                v_size_1230_ = crate::leanh::lean_ctor_get(v_l_1045_, 0);
                                v_size_1231_ = crate::leanh::lean_ctor_get(v___x_1229_, 0);
                                crate::leanh::lean_inc(v_size_1231_);
                                v_k_1232_ = crate::leanh::lean_ctor_get(v___x_1229_, 1);
                                crate::leanh::lean_inc(v_k_1232_);
                                v_v_1233_ = crate::leanh::lean_ctor_get(v___x_1229_, 2);
                                crate::leanh::lean_inc(v_v_1233_);
                                v_l_1234_ = crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                crate::leanh::lean_inc(v_l_1234_);
                                v_r_1235_ = crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                crate::leanh::lean_inc(v_r_1235_);
                                v___x_1236_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1237_ = lean_nat_mul(v___x_1236_, v_size_1230_);
                                v___x_1238_ = lean_nat_dec_lt(v___x_1237_, v_size_1231_);
                                crate::leanh::lean_dec(v___x_1237_);
                                if v___x_1238_ == 0 {
                                    crate::leanh::lean_dec(v_r_1235_);
                                    crate::leanh::lean_dec(v_l_1234_);
                                    crate::leanh::lean_dec(v_v_1233_);
                                    crate::leanh::lean_dec(v_k_1232_);
                                    v___x_1239_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1240_ = lean_nat_add(v___x_1239_, v_size_1230_);
                                    v___x_1241_ = lean_nat_add(v___x_1240_, v_size_1231_);
                                    crate::leanh::lean_dec(v_size_1231_);
                                    crate::leanh::lean_dec(v___x_1240_);
                                    if v_isShared_1049_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                        crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1241_);
                                        v___x_1243_ = v___x_1048_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1244_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            0,
                                            v___x_1241_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            1,
                                            v_k_1043_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            2,
                                            v_v_1044_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1244_,
                                            3,
                                            v_l_1045_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                                        (!crate::leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                    if v_isSharedCheck_1314_ == 0 {
                                        v_unused_1315_ =
                                            crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                        crate::leanh::lean_dec(v_unused_1315_);
                                        v_unused_1316_ =
                                            crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                        crate::leanh::lean_dec(v_unused_1316_);
                                        v_unused_1317_ =
                                            crate::leanh::lean_ctor_get(v___x_1229_, 2);
                                        crate::leanh::lean_dec(v_unused_1317_);
                                        v_unused_1318_ =
                                            crate::leanh::lean_ctor_get(v___x_1229_, 1);
                                        crate::leanh::lean_dec(v_unused_1318_);
                                        v_unused_1319_ =
                                            crate::leanh::lean_ctor_get(v___x_1229_, 0);
                                        crate::leanh::lean_dec(v_unused_1319_);
                                        v___x_1246_ = v___x_1229_;
                                        v_isShared_1247_ = v_isSharedCheck_1314_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1229_);
                                        v___x_1246_ = crate::leanh::lean_box(0);
                                        v_isShared_1247_ = v_isSharedCheck_1314_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1320_ = crate::leanh::lean_ctor_get(v_l_1045_, 0);
                                v___x_1321_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1320_);
                                if v_isShared_1049_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1322_);
                                    v___x_1324_ = v___x_1048_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1325_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        0,
                                        v___x_1322_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        1,
                                        v_k_1043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        2,
                                        v_v_1044_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1325_,
                                        3,
                                        v_l_1045_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            if crate::leanh::lean_obj_tag(v___x_1229_) == 0 {
                                v_l_1326_ = crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                crate::leanh::lean_inc(v_l_1326_);
                                if crate::leanh::lean_obj_tag(v_l_1326_) == 0 {
                                    v_r_1327_ = crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                    crate::leanh::lean_inc(v_r_1327_);
                                    if crate::leanh::lean_obj_tag(v_r_1327_) == 0 {
                                        v_size_1328_ = crate::leanh::lean_ctor_get(v___x_1229_, 0);
                                        v_k_1329_ = crate::leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1330_ = crate::leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1344_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1344_ == 0 {
                                            v_unused_1345_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                            crate::leanh::lean_dec(v_unused_1345_);
                                            v_unused_1346_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                            crate::leanh::lean_dec(v_unused_1346_);
                                            v___x_1332_ = v___x_1229_;
                                            v_isShared_1333_ = v_isSharedCheck_1344_;
                                            state = 40;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1330_);
                                            crate::leanh::lean_inc(v_k_1329_);
                                            crate::leanh::lean_inc(v_size_1328_);
                                            crate::leanh::lean_dec(v___x_1229_);
                                            v___x_1332_ = crate::leanh::lean_box(0);
                                            v_isShared_1333_ = v_isSharedCheck_1344_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_1347_ = crate::leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1348_ = crate::leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1372_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1372_ == 0 {
                                            v_unused_1373_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                            crate::leanh::lean_dec(v_unused_1373_);
                                            v_unused_1374_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                            crate::leanh::lean_dec(v_unused_1374_);
                                            v_unused_1375_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 0);
                                            crate::leanh::lean_dec(v_unused_1375_);
                                            v___x_1350_ = v___x_1229_;
                                            v_isShared_1351_ = v_isSharedCheck_1372_;
                                            state = 43;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1348_);
                                            crate::leanh::lean_inc(v_k_1347_);
                                            crate::leanh::lean_dec(v___x_1229_);
                                            v___x_1350_ = crate::leanh::lean_box(0);
                                            v_isShared_1351_ = v_isSharedCheck_1372_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1376_ = crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                    crate::leanh::lean_inc(v_r_1376_);
                                    if crate::leanh::lean_obj_tag(v_r_1376_) == 0 {
                                        v_k_1377_ = crate::leanh::lean_ctor_get(v___x_1229_, 1);
                                        v_v_1378_ = crate::leanh::lean_ctor_get(v___x_1229_, 2);
                                        v_isSharedCheck_1390_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1229_)) as u8;
                                        if v_isSharedCheck_1390_ == 0 {
                                            v_unused_1391_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 4);
                                            crate::leanh::lean_dec(v_unused_1391_);
                                            v_unused_1392_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 3);
                                            crate::leanh::lean_dec(v_unused_1392_);
                                            v_unused_1393_ =
                                                crate::leanh::lean_ctor_get(v___x_1229_, 0);
                                            crate::leanh::lean_dec(v_unused_1393_);
                                            v___x_1380_ = v___x_1229_;
                                            v_isShared_1381_ = v_isSharedCheck_1390_;
                                            state = 48;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1378_);
                                            crate::leanh::lean_inc(v_k_1377_);
                                            crate::leanh::lean_dec(v___x_1229_);
                                            v___x_1380_ = crate::leanh::lean_box(0);
                                            v_isShared_1381_ = v_isSharedCheck_1390_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_1394_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1049_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_1048_,
                                                4,
                                                v___x_1229_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_1048_, 3, v_r_1376_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1048_,
                                                0,
                                                v___x_1394_,
                                            );
                                            v___x_1396_ = v___x_1048_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1397_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                0,
                                                v___x_1394_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                1,
                                                v_k_1043_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                2,
                                                v_v_1044_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1397_,
                                                3,
                                                v_r_1376_,
                                            );
                                            crate::leanh::lean_ctor_set(
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
                                v___x_1398_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1049_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1229_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1229_);
                                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1398_);
                                    v___x_1400_ = v___x_1048_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1401_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        0,
                                        v___x_1398_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        1,
                                        v_k_1043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        2,
                                        v_v_1044_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1401_,
                                        3,
                                        v___x_1229_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                if crate::leanh::lean_obj_tag(v_l_1056_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1057_) == 0 {
                        v_size_1070_ = crate::leanh::lean_ctor_get(v_l_1056_, 0);
                        v_size_1071_ = crate::leanh::lean_ctor_get(v_r_1057_, 0);
                        v_k_1072_ = crate::leanh::lean_ctor_get(v_r_1057_, 1);
                        v_v_1073_ = crate::leanh::lean_ctor_get(v_r_1057_, 2);
                        v_l_1074_ = crate::leanh::lean_ctor_get(v_r_1057_, 3);
                        v_r_1075_ = crate::leanh::lean_ctor_get(v_r_1057_, 4);
                        v___x_1076_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1077_ = lean_nat_mul(v___x_1076_, v_size_1070_);
                        v___x_1078_ = lean_nat_dec_lt(v_size_1071_, v___x_1077_);
                        crate::leanh::lean_dec(v___x_1077_);
                        if v___x_1078_ == 0 {
                            crate::leanh::lean_inc(v_r_1075_);
                            crate::leanh::lean_inc(v_l_1074_);
                            crate::leanh::lean_inc(v_v_1073_);
                            crate::leanh::lean_inc(v_k_1072_);
                            v_isSharedCheck_1108_ =
                                (!crate::leanh::lean_is_exclusive(v_r_1057_)) as u8;
                            if v_isSharedCheck_1108_ == 0 {
                                v_unused_1109_ = crate::leanh::lean_ctor_get(v_r_1057_, 4);
                                crate::leanh::lean_dec(v_unused_1109_);
                                v_unused_1110_ = crate::leanh::lean_ctor_get(v_r_1057_, 3);
                                crate::leanh::lean_dec(v_unused_1110_);
                                v_unused_1111_ = crate::leanh::lean_ctor_get(v_r_1057_, 2);
                                crate::leanh::lean_dec(v_unused_1111_);
                                v_unused_1112_ = crate::leanh::lean_ctor_get(v_r_1057_, 1);
                                crate::leanh::lean_dec(v_unused_1112_);
                                v_unused_1113_ = crate::leanh::lean_ctor_get(v_r_1057_, 0);
                                crate::leanh::lean_dec(v_unused_1113_);
                                v___x_1080_ = v_r_1057_;
                                v_isShared_1081_ = v_isSharedCheck_1108_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_1057_);
                                v___x_1080_ = crate::leanh::lean_box(0);
                                v_isShared_1081_ = v_isSharedCheck_1108_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1048_);
                            v___x_1114_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1115_ = lean_nat_add(v___x_1114_, v_size_1053_);
                            crate::leanh::lean_dec(v_size_1053_);
                            v___x_1116_ = lean_nat_add(v___x_1115_, v_size_1052_);
                            crate::leanh::lean_dec(v___x_1115_);
                            v___x_1117_ = lean_nat_add(v___x_1114_, v_size_1052_);
                            v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1071_);
                            crate::leanh::lean_dec(v___x_1117_);
                            crate::leanh::lean_inc_ref(v_r_1046_);
                            if v_isShared_1069_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1068_, 4, v_r_1046_);
                                crate::leanh::lean_ctor_set(v___x_1068_, 3, v_r_1057_);
                                crate::leanh::lean_ctor_set(v___x_1068_, 2, v_v_1044_);
                                crate::leanh::lean_ctor_set(v___x_1068_, 1, v_k_1043_);
                                crate::leanh::lean_ctor_set(v___x_1068_, 0, v___x_1118_);
                                v___x_1120_ = v___x_1068_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1133_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1118_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1043_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1044_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_r_1057_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_r_1046_);
                                v___x_1120_ = v_reuseFailAlloc_1133_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_1056_, 5);
                        crate::leanh::lean_del_object(v___x_1068_);
                        crate::leanh::lean_dec(v_v_1055_);
                        crate::leanh::lean_dec(v_k_1054_);
                        crate::leanh::lean_dec(v_size_1053_);
                        crate::leanh::lean_dec_ref_known(v_r_1046_, 5);
                        crate::leanh::lean_del_object(v___x_1048_);
                        crate::leanh::lean_dec(v_v_1044_);
                        crate::leanh::lean_dec(v_k_1043_);
                        v___x_1134_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
                        v___x_1135_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1134_);
                        return v___x_1135_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1068_);
                    crate::leanh::lean_dec(v_r_1057_);
                    crate::leanh::lean_dec(v_v_1055_);
                    crate::leanh::lean_dec(v_k_1054_);
                    crate::leanh::lean_dec(v_size_1053_);
                    crate::leanh::lean_dec_ref_known(v_r_1046_, 5);
                    crate::leanh::lean_del_object(v___x_1048_);
                    crate::leanh::lean_dec(v_v_1044_);
                    crate::leanh::lean_dec(v_k_1043_);
                    v___x_1136_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
                    v___x_1137_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1136_);
                    return v___x_1137_;
                }
            }
            4 => {
                v___x_1082_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1083_ = lean_nat_add(v___x_1082_, v_size_1053_);
                crate::leanh::lean_dec(v_size_1053_);
                v___x_1084_ = lean_nat_add(v___x_1083_, v_size_1052_);
                crate::leanh::lean_dec(v___x_1083_);
                v___x_1096_ = lean_nat_add(v___x_1082_, v_size_1070_);
                if crate::leanh::lean_obj_tag(v_l_1074_) == 0 {
                    v_size_1106_ = crate::leanh::lean_ctor_get(v_l_1074_, 0);
                    crate::leanh::lean_inc(v_size_1106_);
                    v___y_1098_ = v_size_1106_;
                    state = 8;
                    continue;
                } else {
                    v___x_1107_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1098_ = v___x_1107_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1089_ = lean_nat_add(v___y_1087_, v___y_1088_);
                crate::leanh::lean_dec(v___y_1088_);
                crate::leanh::lean_dec(v___y_1087_);
                if v_isShared_1081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1080_, 4, v_r_1046_);
                    crate::leanh::lean_ctor_set(v___x_1080_, 3, v_r_1075_);
                    crate::leanh::lean_ctor_set(v___x_1080_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1080_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1089_);
                    v___x_1091_ = v___x_1080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_r_1075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_r_1046_);
                    v___x_1091_ = v_reuseFailAlloc_1095_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1069_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1068_, 4, v___x_1091_);
                    crate::leanh::lean_ctor_set(v___x_1068_, 3, v___y_1086_);
                    crate::leanh::lean_ctor_set(v___x_1068_, 2, v_v_1073_);
                    crate::leanh::lean_ctor_set(v___x_1068_, 1, v_k_1072_);
                    crate::leanh::lean_ctor_set(v___x_1068_, 0, v___x_1084_);
                    v___x_1093_ = v___x_1068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_k_1072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_v_1073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___y_1086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 4, v___x_1091_);
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
                crate::leanh::lean_dec(v___y_1098_);
                crate::leanh::lean_dec(v___x_1096_);
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v_l_1074_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v_l_1056_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1055_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1054_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1099_);
                    v___x_1101_ = v___x_1048_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_1054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_1055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_l_1056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_l_1074_);
                    v___x_1101_ = v_reuseFailAlloc_1105_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1102_ = lean_nat_add(v___x_1082_, v_size_1052_);
                if crate::leanh::lean_obj_tag(v_r_1075_) == 0 {
                    v_size_1103_ = crate::leanh::lean_ctor_get(v_r_1075_, 0);
                    crate::leanh::lean_inc(v_size_1103_);
                    v___y_1086_ = v___x_1101_;
                    v___y_1087_ = v___x_1102_;
                    v___y_1088_ = v_size_1103_;
                    state = 5;
                    continue;
                } else {
                    v___x_1104_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1086_ = v___x_1101_;
                    v___y_1087_ = v___x_1102_;
                    v___y_1088_ = v___x_1104_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1127_ = (!crate::leanh::lean_is_exclusive(v_r_1046_)) as u8;
                if v_isSharedCheck_1127_ == 0 {
                    v_unused_1128_ = crate::leanh::lean_ctor_get(v_r_1046_, 4);
                    crate::leanh::lean_dec(v_unused_1128_);
                    v_unused_1129_ = crate::leanh::lean_ctor_get(v_r_1046_, 3);
                    crate::leanh::lean_dec(v_unused_1129_);
                    v_unused_1130_ = crate::leanh::lean_ctor_get(v_r_1046_, 2);
                    crate::leanh::lean_dec(v_unused_1130_);
                    v_unused_1131_ = crate::leanh::lean_ctor_get(v_r_1046_, 1);
                    crate::leanh::lean_dec(v_unused_1131_);
                    v_unused_1132_ = crate::leanh::lean_ctor_get(v_r_1046_, 0);
                    crate::leanh::lean_dec(v_unused_1132_);
                    v___x_1122_ = v_r_1046_;
                    v_isShared_1123_ = v_isSharedCheck_1127_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1046_);
                    v___x_1122_ = crate::leanh::lean_box(0);
                    v_isShared_1123_ = v_isSharedCheck_1127_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1122_, 4, v___x_1120_);
                    crate::leanh::lean_ctor_set(v___x_1122_, 3, v_l_1056_);
                    crate::leanh::lean_ctor_set(v___x_1122_, 2, v_v_1055_);
                    crate::leanh::lean_ctor_set(v___x_1122_, 1, v_k_1054_);
                    crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1116_);
                    v___x_1125_ = v___x_1122_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_l_1056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 4, v___x_1120_);
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
                v_size_1158_ = crate::leanh::lean_ctor_get(v_r_1151_, 0);
                v___x_1159_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1160_ = lean_nat_add(v___x_1159_, v_size_1152_);
                crate::leanh::lean_dec(v_size_1152_);
                v___x_1161_ = lean_nat_add(v___x_1159_, v_size_1158_);
                if v_isShared_1157_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1156_, 4, v_r_1046_);
                    crate::leanh::lean_ctor_set(v___x_1156_, 3, v_r_1151_);
                    crate::leanh::lean_ctor_set(v___x_1156_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1156_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1161_);
                    v___x_1163_ = v___x_1156_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_r_1151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_r_1046_);
                    v___x_1163_ = v_reuseFailAlloc_1167_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1163_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1154_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1153_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1160_);
                    v___x_1165_ = v___x_1048_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 4, v___x_1163_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1165_;
            }
            17 => {
                v___x_1176_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1177_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1174_, 3, v_r_1151_);
                    crate::leanh::lean_ctor_set(v___x_1174_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1174_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1174_, 0, v___x_1177_);
                    v___x_1179_ = v___x_1174_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_r_1151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_r_1151_);
                    v___x_1179_ = v_reuseFailAlloc_1183_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1179_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1172_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1171_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1176_);
                    v___x_1181_ = v___x_1048_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1182_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_1171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1182_, 4, v___x_1179_);
                    v___x_1181_ = v_reuseFailAlloc_1182_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1181_;
            }
            20 => {
                v_k_1194_ = crate::leanh::lean_ctor_get(v_r_1188_, 1);
                v_v_1195_ = crate::leanh::lean_ctor_get(v_r_1188_, 2);
                v_isSharedCheck_1210_ = (!crate::leanh::lean_is_exclusive(v_r_1188_)) as u8;
                if v_isSharedCheck_1210_ == 0 {
                    v_unused_1211_ = crate::leanh::lean_ctor_get(v_r_1188_, 4);
                    crate::leanh::lean_dec(v_unused_1211_);
                    v_unused_1212_ = crate::leanh::lean_ctor_get(v_r_1188_, 3);
                    crate::leanh::lean_dec(v_unused_1212_);
                    v_unused_1213_ = crate::leanh::lean_ctor_get(v_r_1188_, 0);
                    crate::leanh::lean_dec(v_unused_1213_);
                    v___x_1197_ = v_r_1188_;
                    v_isShared_1198_ = v_isSharedCheck_1210_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1195_);
                    crate::leanh::lean_inc(v_k_1194_);
                    crate::leanh::lean_dec(v_r_1188_);
                    v___x_1197_ = crate::leanh::lean_box(0);
                    v_isShared_1198_ = v_isSharedCheck_1210_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1199_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1200_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1197_, 4, v_l_1150_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 2, v_v_1190_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 1, v_k_1189_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1200_);
                    v___x_1202_ = v___x_1197_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_l_1150_);
                    v___x_1202_ = v_reuseFailAlloc_1209_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1192_, 4, v_l_1150_);
                    crate::leanh::lean_ctor_set(v___x_1192_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1192_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1200_);
                    v___x_1204_ = v___x_1192_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1208_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_l_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_l_1150_);
                    v___x_1204_ = v_reuseFailAlloc_1208_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1204_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1202_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1195_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1194_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1199_);
                    v___x_1206_ = v___x_1048_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___x_1202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 4, v___x_1204_);
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
                if crate::leanh::lean_obj_tag(v_l_1234_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1235_) == 0 {
                        v_size_1248_ = crate::leanh::lean_ctor_get(v_l_1234_, 0);
                        v_k_1249_ = crate::leanh::lean_ctor_get(v_l_1234_, 1);
                        v_v_1250_ = crate::leanh::lean_ctor_get(v_l_1234_, 2);
                        v_l_1251_ = crate::leanh::lean_ctor_get(v_l_1234_, 3);
                        v_r_1252_ = crate::leanh::lean_ctor_get(v_l_1234_, 4);
                        v_size_1253_ = crate::leanh::lean_ctor_get(v_r_1235_, 0);
                        v___x_1254_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1255_ = lean_nat_mul(v___x_1254_, v_size_1253_);
                        v___x_1256_ = lean_nat_dec_lt(v_size_1248_, v___x_1255_);
                        crate::leanh::lean_dec(v___x_1255_);
                        if v___x_1256_ == 0 {
                            crate::leanh::lean_inc(v_r_1252_);
                            crate::leanh::lean_inc(v_l_1251_);
                            crate::leanh::lean_inc(v_v_1250_);
                            crate::leanh::lean_inc(v_k_1249_);
                            v_isSharedCheck_1285_ =
                                (!crate::leanh::lean_is_exclusive(v_l_1234_)) as u8;
                            if v_isSharedCheck_1285_ == 0 {
                                v_unused_1286_ = crate::leanh::lean_ctor_get(v_l_1234_, 4);
                                crate::leanh::lean_dec(v_unused_1286_);
                                v_unused_1287_ = crate::leanh::lean_ctor_get(v_l_1234_, 3);
                                crate::leanh::lean_dec(v_unused_1287_);
                                v_unused_1288_ = crate::leanh::lean_ctor_get(v_l_1234_, 2);
                                crate::leanh::lean_dec(v_unused_1288_);
                                v_unused_1289_ = crate::leanh::lean_ctor_get(v_l_1234_, 1);
                                crate::leanh::lean_dec(v_unused_1289_);
                                v_unused_1290_ = crate::leanh::lean_ctor_get(v_l_1234_, 0);
                                crate::leanh::lean_dec(v_unused_1290_);
                                v___x_1258_ = v_l_1234_;
                                v_isShared_1259_ = v_isSharedCheck_1285_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_1234_);
                                v___x_1258_ = crate::leanh::lean_box(0);
                                v_isShared_1259_ = v_isSharedCheck_1285_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1048_);
                            v___x_1291_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1230_);
                            v___x_1293_ = lean_nat_add(v___x_1292_, v_size_1231_);
                            crate::leanh::lean_dec(v_size_1231_);
                            v___x_1294_ = lean_nat_add(v___x_1292_, v_size_1248_);
                            crate::leanh::lean_dec(v___x_1292_);
                            crate::leanh::lean_inc_ref(v_l_1045_);
                            if v_isShared_1247_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1246_, 4, v_l_1234_);
                                crate::leanh::lean_ctor_set(v___x_1246_, 3, v_l_1045_);
                                crate::leanh::lean_ctor_set(v___x_1246_, 2, v_v_1044_);
                                crate::leanh::lean_ctor_set(v___x_1246_, 1, v_k_1043_);
                                crate::leanh::lean_ctor_set(v___x_1246_, 0, v___x_1294_);
                                v___x_1296_ = v___x_1246_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_1309_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1294_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1043_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1044_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_l_1045_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_l_1234_);
                                v___x_1296_ = v_reuseFailAlloc_1309_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_1234_, 5);
                        crate::leanh::lean_del_object(v___x_1246_);
                        crate::leanh::lean_dec(v_v_1233_);
                        crate::leanh::lean_dec(v_k_1232_);
                        crate::leanh::lean_dec(v_size_1231_);
                        crate::leanh::lean_dec_ref_known(v_l_1045_, 5);
                        crate::leanh::lean_del_object(v___x_1048_);
                        crate::leanh::lean_dec(v_v_1044_);
                        crate::leanh::lean_dec(v_k_1043_);
                        v___x_1310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
                        v___x_1311_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1310_);
                        return v___x_1311_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1246_);
                    crate::leanh::lean_dec(v_r_1235_);
                    crate::leanh::lean_dec(v_v_1233_);
                    crate::leanh::lean_dec(v_k_1232_);
                    crate::leanh::lean_dec(v_size_1231_);
                    crate::leanh::lean_dec_ref_known(v_l_1045_, 5);
                    crate::leanh::lean_del_object(v___x_1048_);
                    crate::leanh::lean_dec(v_v_1044_);
                    crate::leanh::lean_dec(v_k_1043_);
                    v___x_1312_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
                    v___x_1313_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_1312_);
                    return v___x_1313_;
                }
            }
            30 => {
                v___x_1260_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1261_ = lean_nat_add(v___x_1260_, v_size_1230_);
                v___x_1262_ = lean_nat_add(v___x_1261_, v_size_1231_);
                crate::leanh::lean_dec(v_size_1231_);
                if crate::leanh::lean_obj_tag(v_l_1251_) == 0 {
                    v_size_1283_ = crate::leanh::lean_ctor_get(v_l_1251_, 0);
                    crate::leanh::lean_inc(v_size_1283_);
                    v___y_1275_ = v_size_1283_;
                    state = 34;
                    continue;
                } else {
                    v___x_1284_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1275_ = v___x_1284_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1267_ = lean_nat_add(v___y_1265_, v___y_1266_);
                crate::leanh::lean_dec(v___y_1266_);
                crate::leanh::lean_dec(v___y_1265_);
                if v_isShared_1259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1258_, 4, v_r_1235_);
                    crate::leanh::lean_ctor_set(v___x_1258_, 3, v_r_1252_);
                    crate::leanh::lean_ctor_set(v___x_1258_, 2, v_v_1233_);
                    crate::leanh::lean_ctor_set(v___x_1258_, 1, v_k_1232_);
                    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1258_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_r_1252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_r_1235_);
                    v___x_1269_ = v_reuseFailAlloc_1273_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1246_, 4, v___x_1269_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 3, v___y_1264_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 2, v_v_1250_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 1, v_k_1249_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 0, v___x_1262_);
                    v___x_1271_ = v___x_1246_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_1249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_1250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___y_1264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___x_1269_);
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
                crate::leanh::lean_dec(v___y_1275_);
                crate::leanh::lean_dec(v___x_1261_);
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v_l_1251_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1276_);
                    v___x_1278_ = v___x_1048_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_l_1045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_l_1251_);
                    v___x_1278_ = v_reuseFailAlloc_1282_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1279_ = lean_nat_add(v___x_1260_, v_size_1253_);
                if crate::leanh::lean_obj_tag(v_r_1252_) == 0 {
                    v_size_1280_ = crate::leanh::lean_ctor_get(v_r_1252_, 0);
                    crate::leanh::lean_inc(v_size_1280_);
                    v___y_1264_ = v___x_1278_;
                    v___y_1265_ = v___x_1279_;
                    v___y_1266_ = v_size_1280_;
                    state = 31;
                    continue;
                } else {
                    v___x_1281_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1264_ = v___x_1278_;
                    v___y_1265_ = v___x_1279_;
                    v___y_1266_ = v___x_1281_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_1303_ = (!crate::leanh::lean_is_exclusive(v_l_1045_)) as u8;
                if v_isSharedCheck_1303_ == 0 {
                    v_unused_1304_ = crate::leanh::lean_ctor_get(v_l_1045_, 4);
                    crate::leanh::lean_dec(v_unused_1304_);
                    v_unused_1305_ = crate::leanh::lean_ctor_get(v_l_1045_, 3);
                    crate::leanh::lean_dec(v_unused_1305_);
                    v_unused_1306_ = crate::leanh::lean_ctor_get(v_l_1045_, 2);
                    crate::leanh::lean_dec(v_unused_1306_);
                    v_unused_1307_ = crate::leanh::lean_ctor_get(v_l_1045_, 1);
                    crate::leanh::lean_dec(v_unused_1307_);
                    v_unused_1308_ = crate::leanh::lean_ctor_get(v_l_1045_, 0);
                    crate::leanh::lean_dec(v_unused_1308_);
                    v___x_1298_ = v_l_1045_;
                    v_isShared_1299_ = v_isSharedCheck_1303_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1045_);
                    v___x_1298_ = crate::leanh::lean_box(0);
                    v_isShared_1299_ = v_isSharedCheck_1303_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1298_, 4, v_r_1235_);
                    crate::leanh::lean_ctor_set(v___x_1298_, 3, v___x_1296_);
                    crate::leanh::lean_ctor_set(v___x_1298_, 2, v_v_1233_);
                    crate::leanh::lean_ctor_set(v___x_1298_, 1, v_k_1232_);
                    crate::leanh::lean_ctor_set(v___x_1298_, 0, v___x_1293_);
                    v___x_1301_ = v___x_1298_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___x_1296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1235_);
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
                v_size_1334_ = crate::leanh::lean_ctor_get(v_l_1326_, 0);
                v___x_1335_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1336_ = lean_nat_add(v___x_1335_, v_size_1328_);
                crate::leanh::lean_dec(v_size_1328_);
                v___x_1337_ = lean_nat_add(v___x_1335_, v_size_1334_);
                if v_isShared_1333_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1332_, 4, v_l_1326_);
                    crate::leanh::lean_ctor_set(v___x_1332_, 3, v_l_1045_);
                    crate::leanh::lean_ctor_set(v___x_1332_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1332_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1332_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1332_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_l_1045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_l_1326_);
                    v___x_1339_ = v_reuseFailAlloc_1343_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v_r_1327_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1339_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1330_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1329_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1336_);
                    v___x_1341_ = v___x_1048_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1327_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1341_;
            }
            43 => {
                v_k_1352_ = crate::leanh::lean_ctor_get(v_l_1326_, 1);
                v_v_1353_ = crate::leanh::lean_ctor_get(v_l_1326_, 2);
                v_isSharedCheck_1368_ = (!crate::leanh::lean_is_exclusive(v_l_1326_)) as u8;
                if v_isSharedCheck_1368_ == 0 {
                    v_unused_1369_ = crate::leanh::lean_ctor_get(v_l_1326_, 4);
                    crate::leanh::lean_dec(v_unused_1369_);
                    v_unused_1370_ = crate::leanh::lean_ctor_get(v_l_1326_, 3);
                    crate::leanh::lean_dec(v_unused_1370_);
                    v_unused_1371_ = crate::leanh::lean_ctor_get(v_l_1326_, 0);
                    crate::leanh::lean_dec(v_unused_1371_);
                    v___x_1355_ = v_l_1326_;
                    v_isShared_1356_ = v_isSharedCheck_1368_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1353_);
                    crate::leanh::lean_inc(v_k_1352_);
                    crate::leanh::lean_dec(v_l_1326_);
                    v___x_1355_ = crate::leanh::lean_box(0);
                    v_isShared_1356_ = v_isSharedCheck_1368_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_1357_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1358_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1355_, 4, v_r_1327_);
                    crate::leanh::lean_ctor_set(v___x_1355_, 3, v_r_1327_);
                    crate::leanh::lean_ctor_set(v___x_1355_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1355_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1355_, 0, v___x_1358_);
                    v___x_1360_ = v___x_1355_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_r_1327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_r_1327_);
                    v___x_1360_ = v_reuseFailAlloc_1367_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1350_, 3, v_r_1327_);
                    crate::leanh::lean_ctor_set(v___x_1350_, 0, v___x_1358_);
                    v___x_1362_ = v___x_1350_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1327_);
                    v___x_1362_ = v_reuseFailAlloc_1366_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v___x_1362_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1360_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1353_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1352_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1357_);
                    v___x_1364_ = v___x_1048_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1365_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1365_, 4, v___x_1362_);
                    v___x_1364_ = v_reuseFailAlloc_1365_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1364_;
            }
            48 => {
                v___x_1382_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1383_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1380_, 4, v_l_1326_);
                    crate::leanh::lean_ctor_set(v___x_1380_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v___x_1380_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v___x_1380_, 0, v___x_1383_);
                    v___x_1385_ = v___x_1380_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_l_1326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_l_1326_);
                    v___x_1385_ = v_reuseFailAlloc_1389_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 4, v_r_1376_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 3, v___x_1385_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_v_1378_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_k_1377_);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1382_);
                    v___x_1387_ = v___x_1048_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___x_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_r_1376_);
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
    mut v_val_1405_: *mut crate::leanh::LeanObject,
    mut v_k_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v_t_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_k_1406_) == 0 {
                    v___x_1407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1407_, 0, v_val_1405_);
                    v___x_1408_ = crate::leanh::lean_box(1);
                    v___x_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1407_);
                    crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
                    return v___x_1409_;
                } else {
                    v_head_1410_ = crate::leanh::lean_ctor_get(v_k_1406_, 0);
                    v_tail_1411_ = crate::leanh::lean_ctor_get(v_k_1406_, 1);
                    v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v_k_1406_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1413_ = v_k_1406_;
                        v_isShared_1414_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1411_);
                        crate::leanh::lean_inc(v_head_1410_);
                        crate::leanh::lean_dec(v_k_1406_);
                        v___x_1413_ = crate::leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_t_1415_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1405_, v_tail_1411_);
                v___x_1416_ = crate::leanh::lean_box(0);
                v___x_1417_ = crate::leanh::lean_box(1);
                v___x_1418_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_1410_, v_t_1415_, v___x_1417_);
                if v_isShared_1414_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1413_, 0);
                    crate::leanh::lean_ctor_set(v___x_1413_, 1, v___x_1418_);
                    crate::leanh::lean_ctor_set(v___x_1413_, 0, v___x_1416_);
                    v___x_1420_ = v___x_1413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
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
    mut v_val_1423_: *mut crate::leanh::LeanObject,
    mut v_x_1424_: *mut crate::leanh::LeanObject,
    mut v_x_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_unused_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v_head_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1425_) == 0 {
                    v_a_1426_ = crate::leanh::lean_ctor_get(v_x_1424_, 1);
                    v_isSharedCheck_1434_ = (!crate::leanh::lean_is_exclusive(v_x_1424_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v_unused_1435_ = crate::leanh::lean_ctor_get(v_x_1424_, 0);
                        crate::leanh::lean_dec(v_unused_1435_);
                        v___x_1428_ = v_x_1424_;
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1426_);
                        crate::leanh::lean_dec(v_x_1424_);
                        v___x_1428_ = crate::leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1436_ = crate::leanh::lean_ctor_get(v_x_1424_, 0);
                    v_a_1437_ = crate::leanh::lean_ctor_get(v_x_1424_, 1);
                    v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v_x_1424_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1439_ = v_x_1424_;
                        v_isShared_1440_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1437_);
                        crate::leanh::lean_inc(v_a_1436_);
                        crate::leanh::lean_dec(v_x_1424_);
                        v___x_1439_ = crate::leanh::lean_box(0);
                        v_isShared_1440_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1430_, 0, v_val_1423_);
                if v_isShared_1429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1428_, 0, v___x_1430_);
                    v___x_1432_ = v___x_1428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_a_1426_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1432_;
            }
            3 => {
                v_head_1441_ = crate::leanh::lean_ctor_get(v_x_1425_, 0);
                crate::leanh::lean_inc(v_head_1441_);
                v_tail_1442_ = crate::leanh::lean_ctor_get(v_x_1425_, 1);
                crate::leanh::lean_inc(v_tail_1442_);
                crate::leanh::lean_dec_ref_known(v_x_1425_, 2);
                v___x_1449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1437_, v_head_1441_);
                if crate::leanh::lean_obj_tag(v___x_1449_) == 0 {
                    v___x_1450_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1423_, v_tail_1442_);
                    v___y_1444_ = v___x_1450_;
                    state = 4;
                    continue;
                } else {
                    v_val_1451_ = crate::leanh::lean_ctor_get(v___x_1449_, 0);
                    crate::leanh::lean_inc(v_val_1451_);
                    crate::leanh::lean_dec_ref_known(v___x_1449_, 1);
                    v___x_1452_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_1423_, v_val_1451_, v_tail_1442_);
                    v___y_1444_ = v___x_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_1441_, v___y_1444_, v_a_1437_);
                if v_isShared_1440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1439_, 1, v___x_1445_);
                    v___x_1447_ = v___x_1439_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1445_);
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
    mut v_t_1454_: *mut crate::leanh::LeanObject,
    mut v_n_1455_: *mut crate::leanh::LeanObject,
    mut v_b_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_1455_);
    v___x_1458_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_1456_, v_t_1454_, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn l_Lean_NameTrie_insert___redArg___boxed(
    mut v_t_1459_: *mut crate::leanh::LeanObject,
    mut v_n_1460_: *mut crate::leanh::LeanObject,
    mut v_b_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Lean_NameTrie_insert___redArg(v_t_1459_, v_n_1460_, v_b_1461_);
    crate::leanh::lean_dec(v_n_1460_);
    return v_res_1462_;
}
pub unsafe fn l_Lean_NameTrie_insert(
    mut v_00_u03b2_1463_: *mut crate::leanh::LeanObject,
    mut v_t_1464_: *mut crate::leanh::LeanObject,
    mut v_n_1465_: *mut crate::leanh::LeanObject,
    mut v_b_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Lean_NameTrie_insert___redArg(v_t_1464_, v_n_1465_, v_b_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lean_NameTrie_insert___boxed(
    mut v_00_u03b2_1468_: *mut crate::leanh::LeanObject,
    mut v_t_1469_: *mut crate::leanh::LeanObject,
    mut v_n_1470_: *mut crate::leanh::LeanObject,
    mut v_b_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_NameTrie_insert(v_00_u03b2_1468_, v_t_1469_, v_n_1470_, v_b_1471_);
    crate::leanh::lean_dec(v_n_1470_);
    return v_res_1472_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(
    mut v_00_u03b2_1473_: *mut crate::leanh::LeanObject,
    mut v_val_1474_: *mut crate::leanh::LeanObject,
    mut v_x_1475_: *mut crate::leanh::LeanObject,
    mut v_x_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_1474_, v_x_1475_, v_x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1478_: *mut crate::leanh::LeanObject,
    mut v_msg_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(
    mut v_00_u03b2_1481_: *mut crate::leanh::LeanObject,
    mut v_k_1482_: *mut crate::leanh::LeanObject,
    mut v_v_1483_: *mut crate::leanh::LeanObject,
    mut v_t_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_1482_, v_v_1483_, v_t_1484_);
    return v___x_1485_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(
    mut v_00_u03b4_1486_: *mut crate::leanh::LeanObject,
    mut v_t_1487_: *mut crate::leanh::LeanObject,
    mut v_k_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_1487_, v_k_1488_);
    return v___x_1489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(
    mut v_00_u03b4_1490_: *mut crate::leanh::LeanObject,
    mut v_t_1491_: *mut crate::leanh::LeanObject,
    mut v_k_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_1490_, v_t_1491_, v_k_1492_);
    crate::leanh::lean_dec_ref(v_k_1492_);
    crate::leanh::lean_dec(v_t_1491_);
    return v_res_1493_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(
    mut v_00_u03b2_1494_: *mut crate::leanh::LeanObject,
    mut v_val_1495_: *mut crate::leanh::LeanObject,
    mut v_k_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_1495_, v_k_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_NameTrie_empty___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1500_ = l_Lean_PrefixTreeNode_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1499_,
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_NameTrie_empty(
    mut v_00_u03b2_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_empty___closed__1_once),
        _init_l_Lean_NameTrie_empty___closed__1,
    );
    return v___x_1502_;
}
pub unsafe fn _init_l_Lean_instInhabitedNameTrie___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lean_NameTrie_empty(crate::leanh::lean_box(0));
    return v___x_1503_;
}
pub unsafe fn l_Lean_instInhabitedNameTrie(
    mut v_00_u03b2_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0_once),
        _init_l_Lean_instInhabitedNameTrie___closed__0,
    );
    return v___x_1505_;
}
pub unsafe fn l_Lean_instEmptyCollectionNameTrie(
    mut v_00_u03b2_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedNameTrie___closed__0_once),
        _init_l_Lean_instInhabitedNameTrie___closed__0,
    );
    return v___x_1507_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(
    mut v_x_1508_: *mut crate::leanh::LeanObject,
    mut v_x_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1509_) == 0 {
                    v_a_1510_ = crate::leanh::lean_ctor_get(v_x_1508_, 0);
                    crate::leanh::lean_inc(v_a_1510_);
                    crate::leanh::lean_dec_ref(v_x_1508_);
                    return v_a_1510_;
                } else {
                    v_a_1511_ = crate::leanh::lean_ctor_get(v_x_1508_, 1);
                    crate::leanh::lean_inc(v_a_1511_);
                    crate::leanh::lean_dec_ref(v_x_1508_);
                    v_head_1512_ = crate::leanh::lean_ctor_get(v_x_1509_, 0);
                    v_tail_1513_ = crate::leanh::lean_ctor_get(v_x_1509_, 1);
                    v___x_1514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1511_, v_head_1512_);
                    crate::leanh::lean_dec(v_a_1511_);
                    if crate::leanh::lean_obj_tag(v___x_1514_) == 0 {
                        v___x_1515_ = crate::leanh::lean_box(0);
                        return v___x_1515_;
                    } else {
                        v_val_1516_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                        crate::leanh::lean_inc(v_val_1516_);
                        crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
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
    mut v_x_1518_: *mut crate::leanh::LeanObject,
    mut v_x_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_1518_, v_x_1519_);
    crate::leanh::lean_dec(v_x_1519_);
    return v_res_1520_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___redArg(
    mut v_t_1521_: *mut crate::leanh::LeanObject,
    mut v_k_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1522_);
    v___x_1524_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_1521_, v___x_1523_);
    crate::leanh::lean_dec(v___x_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___redArg___boxed(
    mut v_t_1525_: *mut crate::leanh::LeanObject,
    mut v_k_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ = l_Lean_NameTrie_find_x3f___redArg(v_t_1525_, v_k_1526_);
    crate::leanh::lean_dec(v_k_1526_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f(
    mut v_00_u03b2_1528_: *mut crate::leanh::LeanObject,
    mut v_t_1529_: *mut crate::leanh::LeanObject,
    mut v_k_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_NameTrie_find_x3f___redArg(v_t_1529_, v_k_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_NameTrie_find_x3f___boxed(
    mut v_00_u03b2_1532_: *mut crate::leanh::LeanObject,
    mut v_t_1533_: *mut crate::leanh::LeanObject,
    mut v_k_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_1532_, v_t_1533_, v_k_1534_);
    crate::leanh::lean_dec(v_k_1534_);
    return v_res_1535_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(
    mut v_00_u03b2_1536_: *mut crate::leanh::LeanObject,
    mut v_x_1537_: *mut crate::leanh::LeanObject,
    mut v_x_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_1537_, v_x_1538_);
    return v___x_1539_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(
    mut v_00_u03b2_1540_: *mut crate::leanh::LeanObject,
    mut v_x_1541_: *mut crate::leanh::LeanObject,
    mut v_x_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_1540_, v_x_1541_, v_x_1542_);
    crate::leanh::lean_dec(v_x_1542_);
    return v_res_1543_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___redArg(
    mut v_t_1544_: *mut crate::leanh::LeanObject,
    mut v_k_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1547_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1545_);
    v___x_1548_ = crate::leanh::lean_box(0);
    v___x_1549_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1546_,
            v___x_1548_,
            v_t_1544_,
            v___x_1547_,
        );
    return v___x_1549_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(
    mut v_t_1550_: *mut crate::leanh::LeanObject,
    mut v_k_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_1550_, v_k_1551_);
    crate::leanh::lean_dec(v_k_1551_);
    return v_res_1552_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f(
    mut v_00_u03b2_1553_: *mut crate::leanh::LeanObject,
    mut v_t_1554_: *mut crate::leanh::LeanObject,
    mut v_k_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1557_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1555_);
    v___x_1558_ = crate::leanh::lean_box(0);
    v___x_1559_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1556_,
            v___x_1558_,
            v_t_1554_,
            v___x_1557_,
        );
    return v___x_1559_;
}
pub unsafe fn l_Lean_NameTrie_findLongestPrefix_x3f___boxed(
    mut v_00_u03b2_1560_: *mut crate::leanh::LeanObject,
    mut v_t_1561_: *mut crate::leanh::LeanObject,
    mut v_k_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_1560_, v_t_1561_, v_k_1562_);
    crate::leanh::lean_dec(v_k_1562_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM___redArg(
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
    mut v_t_1565_: *mut crate::leanh::LeanObject,
    mut v_k_1566_: *mut crate::leanh::LeanObject,
    mut v_init_1567_: *mut crate::leanh::LeanObject,
    mut v_f_1568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1570_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1566_);
    crate::leanh::lean_inc(v_init_1567_);
    v___x_1571_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_t_1573_: *mut crate::leanh::LeanObject,
    mut v_k_1574_: *mut crate::leanh::LeanObject,
    mut v_init_1575_: *mut crate::leanh::LeanObject,
    mut v_f_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Lean_NameTrie_foldMatchingM___redArg(
        v_inst_1572_,
        v_t_1573_,
        v_k_1574_,
        v_init_1575_,
        v_f_1576_,
    );
    crate::leanh::lean_dec(v_k_1574_);
    return v_res_1577_;
}
pub unsafe fn l_Lean_NameTrie_foldMatchingM(
    mut v_m_1578_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1579_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1580_: *mut crate::leanh::LeanObject,
    mut v_inst_1581_: *mut crate::leanh::LeanObject,
    mut v_t_1582_: *mut crate::leanh::LeanObject,
    mut v_k_1583_: *mut crate::leanh::LeanObject,
    mut v_init_1584_: *mut crate::leanh::LeanObject,
    mut v_f_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1587_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1583_);
    crate::leanh::lean_inc(v_init_1584_);
    v___x_1588_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_m_1589_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1590_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1591_: *mut crate::leanh::LeanObject,
    mut v_inst_1592_: *mut crate::leanh::LeanObject,
    mut v_t_1593_: *mut crate::leanh::LeanObject,
    mut v_k_1594_: *mut crate::leanh::LeanObject,
    mut v_init_1595_: *mut crate::leanh::LeanObject,
    mut v_f_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_k_1594_);
    return v_res_1597_;
}
pub unsafe fn _init_l_Lean_NameTrie_foldM___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = crate::leanh::lean_box(0);
    v___x_1599_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_NameTrie_foldM___redArg(
    mut v_inst_1600_: *mut crate::leanh::LeanObject,
    mut v_t_1601_: *mut crate::leanh::LeanObject,
    mut v_init_1602_: *mut crate::leanh::LeanObject,
    mut v_f_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1605_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    crate::leanh::lean_inc(v_init_1602_);
    v___x_1606_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_m_1607_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1608_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1609_: *mut crate::leanh::LeanObject,
    mut v_inst_1610_: *mut crate::leanh::LeanObject,
    mut v_t_1611_: *mut crate::leanh::LeanObject,
    mut v_init_1612_: *mut crate::leanh::LeanObject,
    mut v_f_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1615_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    crate::leanh::lean_inc(v_init_1612_);
    v___x_1616_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_f_1617_: *mut crate::leanh::LeanObject,
    mut v_b_1618_: *mut crate::leanh::LeanObject,
    mut v_x_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = crate::leanh::lean_apply_1(v_f_1617_, v_b_1618_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM___redArg(
    mut v_inst_1621_: *mut crate::leanh::LeanObject,
    mut v_t_1622_: *mut crate::leanh::LeanObject,
    mut v_k_1623_: *mut crate::leanh::LeanObject,
    mut v_f_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1625_ = crate::leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1625_, 0, v_f_1624_);
    v___x_1626_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1627_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1623_);
    v___x_1628_ = crate::leanh::lean_box(0);
    v___x_1629_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_t_1631_: *mut crate::leanh::LeanObject,
    mut v_k_1632_: *mut crate::leanh::LeanObject,
    mut v_f_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ =
        l_Lean_NameTrie_forMatchingM___redArg(v_inst_1630_, v_t_1631_, v_k_1632_, v_f_1633_);
    crate::leanh::lean_dec(v_k_1632_);
    return v_res_1634_;
}
pub unsafe fn l_Lean_NameTrie_forMatchingM(
    mut v_m_1635_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1636_: *mut crate::leanh::LeanObject,
    mut v_inst_1637_: *mut crate::leanh::LeanObject,
    mut v_t_1638_: *mut crate::leanh::LeanObject,
    mut v_k_1639_: *mut crate::leanh::LeanObject,
    mut v_f_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1641_ = crate::leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1641_, 0, v_f_1640_);
    v___x_1642_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1643_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1639_);
    v___x_1644_ = crate::leanh::lean_box(0);
    v___x_1645_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_m_1646_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1647_: *mut crate::leanh::LeanObject,
    mut v_inst_1648_: *mut crate::leanh::LeanObject,
    mut v_t_1649_: *mut crate::leanh::LeanObject,
    mut v_k_1650_: *mut crate::leanh::LeanObject,
    mut v_f_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_NameTrie_forMatchingM(
        v_m_1646_,
        v_00_u03b2_1647_,
        v_inst_1648_,
        v_t_1649_,
        v_k_1650_,
        v_f_1651_,
    );
    crate::leanh::lean_dec(v_k_1650_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_NameTrie_forM___redArg(
    mut v_inst_1653_: *mut crate::leanh::LeanObject,
    mut v_t_1654_: *mut crate::leanh::LeanObject,
    mut v_f_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1656_ = crate::leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1656_, 0, v_f_1655_);
    v___x_1657_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1658_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1659_ = crate::leanh::lean_box(0);
    v___x_1660_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_m_1661_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1662_: *mut crate::leanh::LeanObject,
    mut v_inst_1663_: *mut crate::leanh::LeanObject,
    mut v_t_1664_: *mut crate::leanh::LeanObject,
    mut v_f_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1666_ = crate::leanh::lean_alloc_closure(
        l_Lean_NameTrie_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1666_, 0, v_f_1665_);
    v___x_1667_ = l_Lean_NameTrie_empty___closed__0;
    v___x_1668_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1669_ = crate::leanh::lean_box(0);
    v___x_1670_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_a_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1673_ = crate::leanh::lean_ctor_get(v_a_1671_, 0);
    if crate::leanh::lean_obj_tag(v_a_1673_) == 0 {
        let mut v_a_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1674_ = crate::leanh::lean_ctor_get(v_a_1671_, 1);
        crate::leanh::lean_inc(v_a_1674_);
        crate::leanh::lean_dec_ref(v_a_1671_);
        v___x_1675_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_1672_, v_a_1674_);
        return v___x_1675_;
    } else {
        let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_a_1673_);
        v_a_1676_ = crate::leanh::lean_ctor_get(v_a_1671_, 1);
        crate::leanh::lean_inc(v_a_1676_);
        crate::leanh::lean_dec_ref(v_a_1671_);
        v_val_1677_ = crate::leanh::lean_ctor_get(v_a_1673_, 0);
        crate::leanh::lean_inc(v_val_1677_);
        crate::leanh::lean_dec_ref_known(v_a_1673_, 1);
        v___x_1678_ = lean_array_push(v_a_1672_, v_val_1677_);
        v___x_1679_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_1678_, v_a_1676_);
        return v___x_1679_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(
    mut v_init_1680_: *mut crate::leanh::LeanObject,
    mut v_x_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1681_) == 0 {
                    v_v_1682_ = crate::leanh::lean_ctor_get(v_x_1681_, 2);
                    crate::leanh::lean_inc(v_v_1682_);
                    v_l_1683_ = crate::leanh::lean_ctor_get(v_x_1681_, 3);
                    crate::leanh::lean_inc(v_l_1683_);
                    v_r_1684_ = crate::leanh::lean_ctor_get(v_x_1681_, 4);
                    crate::leanh::lean_inc(v_r_1684_);
                    crate::leanh::lean_dec_ref_known(v_x_1681_, 5);
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
    mut v_init_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1689_) == 0 {
                    v___x_1692_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_1690_, v_a_1691_);
                    return v___x_1692_;
                } else {
                    v_head_1693_ = crate::leanh::lean_ctor_get(v_a_1689_, 0);
                    v_tail_1694_ = crate::leanh::lean_ctor_get(v_a_1689_, 1);
                    v_a_1695_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                    crate::leanh::lean_inc(v_a_1695_);
                    crate::leanh::lean_dec_ref(v_a_1690_);
                    v___x_1696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_1695_, v_head_1693_);
                    crate::leanh::lean_dec(v_a_1695_);
                    if crate::leanh::lean_obj_tag(v___x_1696_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_1691_);
                        crate::leanh::lean_inc_ref(v_init_1688_);
                        return v_init_1688_;
                    } else {
                        v_val_1697_ = crate::leanh::lean_ctor_get(v___x_1696_, 0);
                        crate::leanh::lean_inc(v_val_1697_);
                        crate::leanh::lean_dec_ref_known(v___x_1696_, 1);
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
    mut v_init_1699_: *mut crate::leanh::LeanObject,
    mut v_a_1700_: *mut crate::leanh::LeanObject,
    mut v_a_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
    crate::leanh::lean_dec(v_a_1700_);
    crate::leanh::lean_dec_ref(v_init_1699_);
    return v_res_1703_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___redArg(
    mut v_t_1706_: *mut crate::leanh::LeanObject,
    mut v_k_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_NameTrie_matchingToArray___redArg___closed__0;
    v___x_1709_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_1707_);
    v___x_1710_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_1708_, v___x_1709_, v_t_1706_, v___x_1708_);
    crate::leanh::lean_dec(v___x_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___redArg___boxed(
    mut v_t_1711_: *mut crate::leanh::LeanObject,
    mut v_k_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_1711_, v_k_1712_);
    crate::leanh::lean_dec(v_k_1712_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray(
    mut v_00_u03b2_1714_: *mut crate::leanh::LeanObject,
    mut v_t_1715_: *mut crate::leanh::LeanObject,
    mut v_k_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_1715_, v_k_1716_);
    return v___x_1717_;
}
pub unsafe fn l_Lean_NameTrie_matchingToArray___boxed(
    mut v_00_u03b2_1718_: *mut crate::leanh::LeanObject,
    mut v_t_1719_: *mut crate::leanh::LeanObject,
    mut v_k_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_1718_, v_t_1719_, v_k_1720_);
    crate::leanh::lean_dec(v_k_1720_);
    return v_res_1721_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(
    mut v_00_u03b2_1722_: *mut crate::leanh::LeanObject,
    mut v_init_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
    return v___x_1727_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(
    mut v_00_u03b2_1728_: *mut crate::leanh::LeanObject,
    mut v_init_1729_: *mut crate::leanh::LeanObject,
    mut v_a_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
    mut v_a_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_1728_, v_init_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
    crate::leanh::lean_dec(v_a_1730_);
    crate::leanh::lean_dec_ref(v_init_1729_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(
    mut v_00_u03b2_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_1735_, v_a_1736_);
    return v___x_1737_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1738_: *mut crate::leanh::LeanObject,
    mut v_init_1739_: *mut crate::leanh::LeanObject,
    mut v_x_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_1739_, v_x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Lean_NameTrie_toArray___redArg(
    mut v_t_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Lean_NameTrie_matchingToArray___redArg___closed__0;
    v___x_1744_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameTrie_foldM___redArg___closed__0_once),
        _init_l_Lean_NameTrie_foldM___redArg___closed__0,
    );
    v___x_1745_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_1743_, v___x_1744_, v_t_1742_, v___x_1743_);
    return v___x_1745_;
}
pub unsafe fn l_Lean_NameTrie_toArray(
    mut v_00_u03b2_1746_: *mut crate::leanh::LeanObject,
    mut v_t_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_NameTrie_toArray___redArg(v_t_1747_);
    return v___x_1748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_NameTrie(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_PrefixTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_NameTrie(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_NameTrie(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_PrefixTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameTrie(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_NameTrie(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_NameTrie(builtin);
}
