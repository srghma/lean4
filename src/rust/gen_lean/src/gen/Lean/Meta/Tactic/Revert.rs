// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Lean.Meta.Tactic.Clear
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_mvarId_x21, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_index, l_Lean_LocalDecl_isAuxDecl,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_MVarId_setKind___redArg, l_Lean_Meta_collectForwardDeps,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::{
    initialize_Lean_Meta_Tactic_Clear, l_Lean_MVarId_clear,
    runtime_initialize_Lean_Meta_Tactic_Clear,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_setTag___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_MetavarContext_revert;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 118, 101, 114, 116, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value: leanh::LeanStringObject<106> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [96, 58, 32, 73, 116, 32, 105, 115, 32, 97, 110, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 99, 114, 101, 97, 116, 101, 100, 32, 116, 111, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 97, 110, 32, 105, 110, 45, 112, 114, 111, 103, 114, 101, 115, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_revert___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_revert___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_revert___lam__0___closed__1_value: leanh::LeanStringObject<76> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 76,
        m_capacity: 76,
        m_length: 75,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 98, 105,
            110, 100, 101, 114, 32, 100, 117, 101, 32, 116, 111, 32, 102, 97, 105, 108, 117, 114,
            101, 32, 119, 104, 101, 110, 32, 114, 101, 118, 101, 114, 116, 105, 110, 103, 32, 118,
            97, 114, 105, 97, 98, 108, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105,
            101, 115, 0,
        ],
    };
static mut l_Lean_MVarId_revert___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_revert___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_revert___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_revert___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [114, 101, 118, 101, 114, 116, 0],
    };
static mut l_Lean_MVarId_revert___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_revert___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_revert___closed__0_value)
                as *mut leanh::LeanObject,
            6626065151470369524 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_revert___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_revert___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_revert___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
    mut v_mvarId_847_: *mut leanh::LeanObject,
    mut v_x_848_: *mut leanh::LeanObject,
    mut v___y_849_: *mut leanh::LeanObject,
    mut v___y_850_: *mut leanh::LeanObject,
    mut v___y_851_: *mut leanh::LeanObject,
    mut v___y_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_a_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_854_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_847_,
                    v_x_848_,
                    v___y_849_,
                    v___y_850_,
                    v___y_851_,
                    v___y_852_,
                );
                if leanh::lean_obj_tag(v___x_854_) == 0 {
                    v_a_855_ = leanh::lean_ctor_get(v___x_854_, 0);
                    v_isSharedCheck_862_ = (!leanh::lean_is_exclusive(v___x_854_)) as u8;
                    if v_isSharedCheck_862_ == 0 {
                        v___x_857_ = v___x_854_;
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_855_);
                        leanh::lean_dec(v___x_854_);
                        v___x_857_ = leanh::lean_box(0);
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_863_ = leanh::lean_ctor_get(v___x_854_, 0);
                    v_isSharedCheck_870_ = (!leanh::lean_is_exclusive(v___x_854_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_865_ = v___x_854_;
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_863_);
                        leanh::lean_dec(v___x_854_);
                        v___x_865_ = leanh::lean_box(0);
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_858_ == 0 {
                    v___x_860_ = v___x_857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
                    v___x_860_ = v_reuseFailAlloc_861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_860_;
            }
            3 => {
                if v_isShared_866_ == 0 {
                    v___x_868_ = v___x_865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
                    v___x_868_ = v_reuseFailAlloc_869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg___boxed(
    mut v_mvarId_871_: *mut leanh::LeanObject,
    mut v_x_872_: *mut leanh::LeanObject,
    mut v___y_873_: *mut leanh::LeanObject,
    mut v___y_874_: *mut leanh::LeanObject,
    mut v___y_875_: *mut leanh::LeanObject,
    mut v___y_876_: *mut leanh::LeanObject,
    mut v___y_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
        v_mvarId_871_,
        v_x_872_,
        v___y_873_,
        v___y_874_,
        v___y_875_,
        v___y_876_,
    );
    leanh::lean_dec(v___y_876_);
    leanh::lean_dec_ref(v___y_875_);
    leanh::lean_dec(v___y_874_);
    leanh::lean_dec_ref(v___y_873_);
    return v_res_878_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(
    mut v_00_u03b1_879_: *mut leanh::LeanObject,
    mut v_mvarId_880_: *mut leanh::LeanObject,
    mut v_x_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
    mut v___y_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
        v_mvarId_880_,
        v_x_881_,
        v___y_882_,
        v___y_883_,
        v___y_884_,
        v___y_885_,
    );
    return v___x_887_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___boxed(
    mut v_00_u03b1_888_: *mut leanh::LeanObject,
    mut v_mvarId_889_: *mut leanh::LeanObject,
    mut v_x_890_: *mut leanh::LeanObject,
    mut v___y_891_: *mut leanh::LeanObject,
    mut v___y_892_: *mut leanh::LeanObject,
    mut v___y_893_: *mut leanh::LeanObject,
    mut v___y_894_: *mut leanh::LeanObject,
    mut v___y_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(
        v_00_u03b1_888_,
        v_mvarId_889_,
        v_x_890_,
        v___y_891_,
        v___y_892_,
        v___y_893_,
        v___y_894_,
    );
    leanh::lean_dec(v___y_894_);
    leanh::lean_dec_ref(v___y_893_);
    leanh::lean_dec(v___y_892_);
    leanh::lean_dec_ref(v___y_891_);
    return v_res_896_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(
    mut v_msgData_897_: *mut leanh::LeanObject,
    mut v___y_898_: *mut leanh::LeanObject,
    mut v___y_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
    mut v___y_901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = lean_st_ref_get(v___y_901_);
    v_env_904_ = leanh::lean_ctor_get(v___x_903_, 0);
    leanh::lean_inc_ref(v_env_904_);
    leanh::lean_dec(v___x_903_);
    v___x_905_ = lean_st_ref_get(v___y_899_);
    v_mctx_906_ = leanh::lean_ctor_get(v___x_905_, 0);
    leanh::lean_inc_ref(v_mctx_906_);
    leanh::lean_dec(v___x_905_);
    v_lctx_907_ = leanh::lean_ctor_get(v___y_898_, 2);
    v_options_908_ = leanh::lean_ctor_get(v___y_900_, 2);
    leanh::lean_inc_ref(v_options_908_);
    leanh::lean_inc_ref(v_lctx_907_);
    v___x_909_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_909_, 0, v_env_904_);
    leanh::lean_ctor_set(v___x_909_, 1, v_mctx_906_);
    leanh::lean_ctor_set(v___x_909_, 2, v_lctx_907_);
    leanh::lean_ctor_set(v___x_909_, 3, v_options_908_);
    v___x_910_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_910_, 0, v___x_909_);
    leanh::lean_ctor_set(v___x_910_, 1, v_msgData_897_);
    v___x_911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_911_, 0, v___x_910_);
    return v___x_911_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(
    mut v_msgData_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
    leanh::lean_dec(v___y_916_);
    leanh::lean_dec_ref(v___y_915_);
    leanh::lean_dec(v___y_914_);
    leanh::lean_dec_ref(v___y_913_);
    return v_res_918_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
    mut v_msg_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_925_ = leanh::lean_ctor_get(v___y_922_, 5);
                v___x_926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
                v_a_927_ = leanh::lean_ctor_get(v___x_926_, 0);
                v_isSharedCheck_935_ = (!leanh::lean_is_exclusive(v___x_926_)) as u8;
                if v_isSharedCheck_935_ == 0 {
                    v___x_929_ = v___x_926_;
                    v_isShared_930_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_927_);
                    leanh::lean_dec(v___x_926_);
                    v___x_929_ = leanh::lean_box(0);
                    v_isShared_930_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_925_);
                v___x_931_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_931_, 0, v_ref_925_);
                leanh::lean_ctor_set(v___x_931_, 1, v_a_927_);
                if v_isShared_930_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_929_, 1);
                    leanh::lean_ctor_set(v___x_929_, 0, v___x_931_);
                    v___x_933_ = v___x_929_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
                    v___x_933_ = v_reuseFailAlloc_934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg___boxed(
    mut v_msg_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
    mut v___y_938_: *mut leanh::LeanObject,
    mut v___y_939_: *mut leanh::LeanObject,
    mut v___y_940_: *mut leanh::LeanObject,
    mut v___y_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
        v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_,
    );
    leanh::lean_dec(v___y_940_);
    leanh::lean_dec_ref(v___y_939_);
    leanh::lean_dec(v___y_938_);
    leanh::lean_dec_ref(v___y_937_);
    return v_res_942_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0;
    v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
    return v___x_945_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2;
    v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(
    mut v_as_949_: *mut leanh::LeanObject,
    mut v_sz_950_: usize,
    mut v_i_951_: usize,
    mut v_b_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
    mut v___y_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: usize = 0;
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: u8 = 0;
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_963_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
                if v___x_963_ == 0 {
                    v___x_964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_964_, 0, v_b_952_);
                    return v___x_964_;
                } else {
                    v_a_965_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
                    leanh::lean_inc(v_a_965_);
                    v___x_966_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_965_, v___y_953_, v___y_955_, v___y_956_,
                    );
                    if leanh::lean_obj_tag(v___x_966_) == 0 {
                        v_a_967_ = leanh::lean_ctor_get(v___x_966_, 0);
                        leanh::lean_inc(v_a_967_);
                        leanh::lean_dec_ref_known(v___x_966_, 1);
                        v___x_968_ = leanh::lean_box(0);
                        v___x_969_ = l_Lean_LocalDecl_isAuxDecl(v_a_967_);
                        leanh::lean_dec(v_a_967_);
                        if v___x_969_ == 0 {
                            v_a_959_ = v___x_968_;
                            state = 1;
                            continue;
                        } else {
                            v___x_970_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1);
                            leanh::lean_inc(v_a_965_);
                            v___x_971_ = l_Lean_mkFVar(v_a_965_);
                            v___x_972_ = l_Lean_MessageData_ofExpr(v___x_971_);
                            v___x_973_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_973_, 0, v___x_970_);
                            leanh::lean_ctor_set(v___x_973_, 1, v___x_972_);
                            v___x_974_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3);
                            v___x_975_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_975_, 0, v___x_973_);
                            leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
                            v___x_976_ =
                                l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
                                    v___x_975_, v___y_953_, v___y_954_, v___y_955_, v___y_956_,
                                );
                            if leanh::lean_obj_tag(v___x_976_) == 0 {
                                leanh::lean_dec_ref_known(v___x_976_, 1);
                                v_a_959_ = v___x_968_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_976_;
                            }
                        }
                    } else {
                        v_a_977_ = leanh::lean_ctor_get(v___x_966_, 0);
                        v_isSharedCheck_984_ = (!leanh::lean_is_exclusive(v___x_966_)) as u8;
                        if v_isSharedCheck_984_ == 0 {
                            v___x_979_ = v___x_966_;
                            v_isShared_980_ = v_isSharedCheck_984_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_977_);
                            leanh::lean_dec(v___x_966_);
                            v___x_979_ = leanh::lean_box(0);
                            v_isShared_980_ = v_isSharedCheck_984_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_960_ = 1usize;
                v___x_961_ = lean_usize_add(v_i_951_, v___x_960_);
                v_i_951_ = v___x_961_;
                v_b_952_ = v_a_959_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_980_ == 0 {
                    v___x_982_ = v___x_979_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
                    v___x_982_ = v_reuseFailAlloc_983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___boxed(
    mut v_as_985_: *mut leanh::LeanObject,
    mut v_sz_986_: *mut leanh::LeanObject,
    mut v_i_987_: *mut leanh::LeanObject,
    mut v_b_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
    mut v___y_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_994_: usize = 0;
    let mut v_i_boxed_995_: usize = 0;
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_994_ = leanh::lean_unbox_usize(v_sz_986_);
    leanh::lean_dec(v_sz_986_);
    v_i_boxed_995_ = leanh::lean_unbox_usize(v_i_987_);
    leanh::lean_dec(v_i_987_);
    v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_985_, v_sz_boxed_994_, v_i_boxed_995_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
    leanh::lean_dec(v___y_992_);
    leanh::lean_dec_ref(v___y_991_);
    leanh::lean_dec(v___y_990_);
    leanh::lean_dec_ref(v___y_989_);
    leanh::lean_dec_ref(v_as_985_);
    return v_res_996_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(
    mut v_sz_997_: usize,
    mut v_i_998_: usize,
    mut v_bs_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1000_: u8 = 0;
    let mut v_v_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1000_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
                if v___x_1000_ == 0 {
                    return v_bs_999_;
                } else {
                    v_v_1001_ = lean_array_uget(v_bs_999_, v_i_998_);
                    v___x_1002_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1003_ = lean_array_uset(v_bs_999_, v_i_998_, v___x_1002_);
                    v___x_1004_ = l_Lean_mkFVar(v_v_1001_);
                    v___x_1005_ = 1usize;
                    v___x_1006_ = lean_usize_add(v_i_998_, v___x_1005_);
                    v___x_1007_ = lean_array_uset(v_bs_x27_1003_, v_i_998_, v___x_1004_);
                    v_i_998_ = v___x_1006_;
                    v_bs_999_ = v___x_1007_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0___boxed(
    mut v_sz_1009_: *mut leanh::LeanObject,
    mut v_i_1010_: *mut leanh::LeanObject,
    mut v_bs_1011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1012_: usize = 0;
    let mut v_i_boxed_1013_: usize = 0;
    let mut v_res_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1012_ = leanh::lean_unbox_usize(v_sz_1009_);
    leanh::lean_dec(v_sz_1009_);
    v_i_boxed_1013_ = leanh::lean_unbox_usize(v_i_1010_);
    leanh::lean_dec(v_i_1010_);
    v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_boxed_1012_, v_i_boxed_1013_, v_bs_1011_);
    return v_res_1014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(
    mut v_sz_1015_: usize,
    mut v_i_1016_: usize,
    mut v_bs_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1018_: u8 = 0;
    let mut v_v_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: usize = 0;
    let mut v___x_1024_: usize = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1018_ = lean_usize_dec_lt(v_i_1016_, v_sz_1015_);
                if v___x_1018_ == 0 {
                    return v_bs_1017_;
                } else {
                    v_v_1019_ = lean_array_uget(v_bs_1017_, v_i_1016_);
                    v___x_1020_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1021_ = lean_array_uset(v_bs_1017_, v_i_1016_, v___x_1020_);
                    v___x_1022_ = l_Lean_Expr_fvarId_x21(v_v_1019_);
                    leanh::lean_dec(v_v_1019_);
                    v___x_1023_ = 1usize;
                    v___x_1024_ = lean_usize_add(v_i_1016_, v___x_1023_);
                    v___x_1025_ = lean_array_uset(v_bs_x27_1021_, v_i_1016_, v___x_1022_);
                    v_i_1016_ = v___x_1024_;
                    v_bs_1017_ = v___x_1025_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2___boxed(
    mut v_sz_1027_: *mut leanh::LeanObject,
    mut v_i_1028_: *mut leanh::LeanObject,
    mut v_bs_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1030_: usize = 0;
    let mut v_i_boxed_1031_: usize = 0;
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1030_ = leanh::lean_unbox_usize(v_sz_1027_);
    leanh::lean_dec(v_sz_1027_);
    v_i_boxed_1031_ = leanh::lean_unbox_usize(v_i_1028_);
    leanh::lean_dec(v_i_1028_);
    v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_boxed_1030_, v_i_boxed_1031_, v_bs_1029_);
    return v_res_1032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(
    mut v_as_1033_: *mut leanh::LeanObject,
    mut v_sz_1034_: usize,
    mut v_i_1035_: usize,
    mut v_b_1036_: *mut leanh::LeanObject,
    mut v___y_1037_: *mut leanh::LeanObject,
    mut v___y_1038_: *mut leanh::LeanObject,
    mut v___y_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: usize = 0;
    let mut v___x_1045_: usize = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_a_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1047_ = lean_usize_dec_lt(v_i_1035_, v_sz_1034_);
                if v___x_1047_ == 0 {
                    v___x_1048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1048_, 0, v_b_1036_);
                    return v___x_1048_;
                } else {
                    v_a_1049_ = lean_array_uget_borrowed(v_as_1033_, v_i_1035_);
                    v___x_1050_ = l_Lean_Expr_fvarId_x21(v_a_1049_);
                    leanh::lean_inc(v___x_1050_);
                    v___x_1051_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_1050_,
                        v___y_1037_,
                        v___y_1039_,
                        v___y_1040_,
                    );
                    if leanh::lean_obj_tag(v___x_1051_) == 0 {
                        v_a_1052_ = leanh::lean_ctor_get(v___x_1051_, 0);
                        leanh::lean_inc(v_a_1052_);
                        leanh::lean_dec_ref_known(v___x_1051_, 1);
                        v_fst_1053_ = leanh::lean_ctor_get(v_b_1036_, 0);
                        v_snd_1054_ = leanh::lean_ctor_get(v_b_1036_, 1);
                        v_isSharedCheck_1076_ = (!leanh::lean_is_exclusive(v_b_1036_)) as u8;
                        if v_isSharedCheck_1076_ == 0 {
                            v___x_1056_ = v_b_1036_;
                            v_isShared_1057_ = v_isSharedCheck_1076_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1054_);
                            leanh::lean_inc(v_fst_1053_);
                            leanh::lean_dec(v_b_1036_);
                            v___x_1056_ = leanh::lean_box(0);
                            v_isShared_1057_ = v_isSharedCheck_1076_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1050_);
                        leanh::lean_dec_ref(v_b_1036_);
                        v_a_1077_ = leanh::lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1084_ =
                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1084_ == 0 {
                            v___x_1079_ = v___x_1051_;
                            v_isShared_1080_ = v_isSharedCheck_1084_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1077_);
                            leanh::lean_dec(v___x_1051_);
                            v___x_1079_ = leanh::lean_box(0);
                            v_isShared_1080_ = v_isSharedCheck_1084_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1044_ = 1usize;
                v___x_1045_ = lean_usize_add(v_i_1035_, v___x_1044_);
                v_i_1035_ = v___x_1045_;
                v_b_1036_ = v_a_1043_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1058_ = l_Lean_LocalDecl_isAuxDecl(v_a_1052_);
                leanh::lean_dec(v_a_1052_);
                if v___x_1058_ == 0 {
                    leanh::lean_dec(v___x_1050_);
                    leanh::lean_inc(v_a_1049_);
                    v___x_1059_ = lean_array_push(v_snd_1054_, v_a_1049_);
                    if v_isShared_1057_ == 0 {
                        leanh::lean_ctor_set(v___x_1056_, 1, v___x_1059_);
                        v___x_1061_ = v___x_1056_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1062_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_fst_1053_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
                        v___x_1061_ = v_reuseFailAlloc_1062_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1063_ = l_Lean_MVarId_clear(
                        v_fst_1053_,
                        v___x_1050_,
                        v___y_1037_,
                        v___y_1038_,
                        v___y_1039_,
                        v___y_1040_,
                    );
                    if leanh::lean_obj_tag(v___x_1063_) == 0 {
                        v_a_1064_ = leanh::lean_ctor_get(v___x_1063_, 0);
                        leanh::lean_inc(v_a_1064_);
                        leanh::lean_dec_ref_known(v___x_1063_, 1);
                        if v_isShared_1057_ == 0 {
                            leanh::lean_ctor_set(v___x_1056_, 0, v_a_1064_);
                            v___x_1066_ = v___x_1056_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1067_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_snd_1054_);
                            v___x_1066_ = v_reuseFailAlloc_1067_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1056_);
                        leanh::lean_dec(v_snd_1054_);
                        v_a_1068_ = leanh::lean_ctor_get(v___x_1063_, 0);
                        v_isSharedCheck_1075_ =
                            (!leanh::lean_is_exclusive(v___x_1063_)) as u8;
                        if v_isSharedCheck_1075_ == 0 {
                            v___x_1070_ = v___x_1063_;
                            v_isShared_1071_ = v_isSharedCheck_1075_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1068_);
                            leanh::lean_dec(v___x_1063_);
                            v___x_1070_ = leanh::lean_box(0);
                            v_isShared_1071_ = v_isSharedCheck_1075_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_1043_ = v___x_1061_;
                state = 1;
                continue;
            }
            4 => {
                v_a_1043_ = v___x_1066_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_1071_ == 0 {
                    v___x_1073_ = v___x_1070_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
                    v___x_1073_ = v_reuseFailAlloc_1074_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1073_;
            }
            7 => {
                if v_isShared_1080_ == 0 {
                    v___x_1082_ = v___x_1079_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
                    v___x_1082_ = v_reuseFailAlloc_1083_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1___boxed(
    mut v_as_1085_: *mut leanh::LeanObject,
    mut v_sz_1086_: *mut leanh::LeanObject,
    mut v_i_1087_: *mut leanh::LeanObject,
    mut v_b_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1094_: usize = 0;
    let mut v_i_boxed_1095_: usize = 0;
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1094_ = leanh::lean_unbox_usize(v_sz_1086_);
    leanh::lean_dec(v_sz_1086_);
    v_i_boxed_1095_ = leanh::lean_unbox_usize(v_i_1087_);
    leanh::lean_dec(v_i_1087_);
    v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_1085_, v_sz_boxed_1094_, v_i_boxed_1095_, v_b_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
    leanh::lean_dec(v___y_1092_);
    leanh::lean_dec_ref(v___y_1091_);
    leanh::lean_dec(v___y_1090_);
    leanh::lean_dec_ref(v___y_1089_);
    leanh::lean_dec_ref(v_as_1085_);
    return v_res_1096_;
}
pub unsafe fn _init_l_Lean_MVarId_revert___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = leanh::lean_box(0);
    v___x_1098_ = leanh::lean_unsigned_to_nat(16);
    v___x_1099_ = lean_mk_array(v___x_1098_, v___x_1097_);
    return v___x_1099_;
}
pub unsafe fn _init_l_Lean_MVarId_revert___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_MVarId_revert___lam__0___closed__1;
    v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_MVarId_revert___lam__0(
    mut v_mvarId_1103_: *mut leanh::LeanObject,
    mut v___x_1104_: *mut leanh::LeanObject,
    mut v_fvarIds_1105_: *mut leanh::LeanObject,
    mut v_preserveOrder_1106_: u8,
    mut v___x_1107_: u8,
    mut v___x_1108_: *mut leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1109_: u8,
    mut v___y_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1117_: usize = 0;
    let mut v___y_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1119_: u8 = 0;
    let mut v___y_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1127_: u8 = 0;
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v_sz_1135_: usize = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_unused_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut v_a_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_a_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v___y_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1175_: usize = 0;
    let mut v___x_1176_: usize = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1182_: usize = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1189_: u8 = 0;
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_reuseFailAlloc_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_unused_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut v_unused_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1306_: u8 = 0;
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_a_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_a_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_a_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1338_: usize = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_a_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1103_);
                v___x_1336_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1103_,
                    v___x_1104_,
                    v___y_1110_,
                    v___y_1111_,
                    v___y_1112_,
                    v___y_1113_,
                );
                if leanh::lean_obj_tag(v___x_1336_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1336_, 1);
                    if v_clearAuxDeclsInsteadOfRevert_1109_ == 0 {
                        v___x_1337_ = leanh::lean_box(0);
                        v_sz_1338_ = lean_array_size(v_fvarIds_1105_);
                        v___x_1339_ = 0usize;
                        v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_1105_, v_sz_1338_, v___x_1339_, v___x_1337_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
                        if leanh::lean_obj_tag(v___x_1340_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1340_, 1);
                            v___y_1171_ = v___y_1110_;
                            v___y_1172_ = v___y_1111_;
                            v___y_1173_ = v___y_1112_;
                            v___y_1174_ = v___y_1113_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1108_);
                            leanh::lean_dec_ref(v_fvarIds_1105_);
                            leanh::lean_dec(v_mvarId_1103_);
                            v_a_1341_ = leanh::lean_ctor_get(v___x_1340_, 0);
                            v_isSharedCheck_1348_ =
                                (!leanh::lean_is_exclusive(v___x_1340_)) as u8;
                            if v_isSharedCheck_1348_ == 0 {
                                v___x_1343_ = v___x_1340_;
                                v_isShared_1344_ = v_isSharedCheck_1348_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1341_);
                                leanh::lean_dec(v___x_1340_);
                                v___x_1343_ = leanh::lean_box(0);
                                v_isShared_1344_ = v_isSharedCheck_1348_;
                                state = 35;
                                continue;
                            }
                        }
                    } else {
                        v___y_1171_ = v___y_1110_;
                        v___y_1172_ = v___y_1111_;
                        v___y_1173_ = v___y_1112_;
                        v___y_1174_ = v___y_1113_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1108_);
                    leanh::lean_dec_ref(v_fvarIds_1105_);
                    leanh::lean_dec(v_mvarId_1103_);
                    v_a_1349_ = leanh::lean_ctor_get(v___x_1336_, 0);
                    v_isSharedCheck_1356_ = (!leanh::lean_is_exclusive(v___x_1336_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1351_ = v___x_1336_;
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1349_);
                        leanh::lean_dec(v___x_1336_);
                        v___x_1351_ = leanh::lean_box(0);
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1122_ = l_Lean_MVarId_setKind___redArg(v___y_1120_, v___y_1119_, v___y_1116_);
                if leanh::lean_obj_tag(v___x_1122_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1122_, 1);
                    v_fst_1123_ = leanh::lean_ctor_get(v_a_1121_, 0);
                    v_snd_1124_ = leanh::lean_ctor_get(v_a_1121_, 1);
                    v_isSharedCheck_1161_ = (!leanh::lean_is_exclusive(v_a_1121_)) as u8;
                    if v_isSharedCheck_1161_ == 0 {
                        v___x_1126_ = v_a_1121_;
                        v_isShared_1127_ = v_isSharedCheck_1161_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1124_);
                        leanh::lean_inc(v_fst_1123_);
                        leanh::lean_dec(v_a_1121_);
                        v___x_1126_ = leanh::lean_box(0);
                        v_isShared_1127_ = v_isSharedCheck_1161_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1121_);
                    leanh::lean_dec(v___y_1118_);
                    v_a_1162_ = leanh::lean_ctor_get(v___x_1122_, 0);
                    v_isSharedCheck_1169_ = (!leanh::lean_is_exclusive(v___x_1122_)) as u8;
                    if v_isSharedCheck_1169_ == 0 {
                        v___x_1164_ = v___x_1122_;
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1162_);
                        leanh::lean_dec(v___x_1122_);
                        v___x_1164_ = leanh::lean_box(0);
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1128_ = l_Lean_Expr_getAppFn(v_fst_1123_);
                leanh::lean_dec(v_fst_1123_);
                v___x_1129_ = l_Lean_Expr_mvarId_x21(v___x_1128_);
                leanh::lean_dec_ref(v___x_1128_);
                leanh::lean_inc(v___x_1129_);
                v___x_1130_ = l_Lean_MVarId_setKind___redArg(v___x_1129_, v___y_1119_, v___y_1116_);
                if leanh::lean_obj_tag(v___x_1130_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1130_, 1);
                    leanh::lean_inc(v___x_1129_);
                    v___x_1131_ =
                        l_Lean_MVarId_setTag___redArg(v___x_1129_, v___y_1118_, v___y_1116_);
                    if leanh::lean_obj_tag(v___x_1131_) == 0 {
                        v_isSharedCheck_1143_ =
                            (!leanh::lean_is_exclusive(v___x_1131_)) as u8;
                        if v_isSharedCheck_1143_ == 0 {
                            v_unused_1144_ = leanh::lean_ctor_get(v___x_1131_, 0);
                            leanh::lean_dec(v_unused_1144_);
                            v___x_1133_ = v___x_1131_;
                            v_isShared_1134_ = v_isSharedCheck_1143_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1131_);
                            v___x_1133_ = leanh::lean_box(0);
                            v_isShared_1134_ = v_isSharedCheck_1143_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1129_);
                        leanh::lean_del_object(v___x_1126_);
                        leanh::lean_dec(v_snd_1124_);
                        v_a_1145_ = leanh::lean_ctor_get(v___x_1131_, 0);
                        v_isSharedCheck_1152_ =
                            (!leanh::lean_is_exclusive(v___x_1131_)) as u8;
                        if v_isSharedCheck_1152_ == 0 {
                            v___x_1147_ = v___x_1131_;
                            v_isShared_1148_ = v_isSharedCheck_1152_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1145_);
                            leanh::lean_dec(v___x_1131_);
                            v___x_1147_ = leanh::lean_box(0);
                            v_isShared_1148_ = v_isSharedCheck_1152_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1129_);
                    leanh::lean_del_object(v___x_1126_);
                    leanh::lean_dec(v_snd_1124_);
                    leanh::lean_dec(v___y_1118_);
                    v_a_1153_ = leanh::lean_ctor_get(v___x_1130_, 0);
                    v_isSharedCheck_1160_ = (!leanh::lean_is_exclusive(v___x_1130_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v___x_1155_ = v___x_1130_;
                        v_isShared_1156_ = v_isSharedCheck_1160_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1153_);
                        leanh::lean_dec(v___x_1130_);
                        v___x_1155_ = leanh::lean_box(0);
                        v_isShared_1156_ = v_isSharedCheck_1160_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_sz_1135_ = lean_array_size(v_snd_1124_);
                v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_1135_, v___y_1117_, v_snd_1124_);
                if v_isShared_1127_ == 0 {
                    leanh::lean_ctor_set(v___x_1126_, 1, v___x_1129_);
                    leanh::lean_ctor_set(v___x_1126_, 0, v___x_1136_);
                    v___x_1138_ = v___x_1126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1129_);
                    v___x_1138_ = v_reuseFailAlloc_1142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1134_ == 0 {
                    leanh::lean_ctor_set(v___x_1133_, 0, v___x_1138_);
                    v___x_1140_ = v___x_1133_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
                    v___x_1140_ = v_reuseFailAlloc_1141_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1140_;
            }
            6 => {
                if v_isShared_1148_ == 0 {
                    v___x_1150_ = v___x_1147_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1151_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
                    v___x_1150_ = v_reuseFailAlloc_1151_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1150_;
            }
            8 => {
                if v_isShared_1156_ == 0 {
                    v___x_1158_ = v___x_1155_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
                    v___x_1158_ = v_reuseFailAlloc_1159_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1158_;
            }
            10 => {
                if v_isShared_1165_ == 0 {
                    v___x_1167_ = v___x_1164_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1167_;
            }
            12 => {
                v_sz_1175_ = lean_array_size(v_fvarIds_1105_);
                v___x_1176_ = 0usize;
                v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_1175_, v___x_1176_, v_fvarIds_1105_);
                v___x_1178_ = l_Lean_Meta_collectForwardDeps(
                    v___x_1177_,
                    v_preserveOrder_1106_,
                    v___x_1107_,
                    v___y_1171_,
                    v___y_1172_,
                    v___y_1173_,
                    v___y_1174_,
                );
                if leanh::lean_obj_tag(v___x_1178_) == 0 {
                    v_a_1179_ = leanh::lean_ctor_get(v___x_1178_, 0);
                    leanh::lean_inc(v_a_1179_);
                    leanh::lean_dec_ref_known(v___x_1178_, 1);
                    v___x_1180_ = lean_mk_empty_array_with_capacity(v___x_1108_);
                    v___x_1181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1181_, 0, v_mvarId_1103_);
                    leanh::lean_ctor_set(v___x_1181_, 1, v___x_1180_);
                    v_sz_1182_ = lean_array_size(v_a_1179_);
                    v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_1179_, v_sz_1182_, v___x_1176_, v___x_1181_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
                    leanh::lean_dec(v_a_1179_);
                    if leanh::lean_obj_tag(v___x_1183_) == 0 {
                        v_a_1184_ = leanh::lean_ctor_get(v___x_1183_, 0);
                        leanh::lean_inc(v_a_1184_);
                        leanh::lean_dec_ref_known(v___x_1183_, 1);
                        v_fst_1185_ = leanh::lean_ctor_get(v_a_1184_, 0);
                        v_snd_1186_ = leanh::lean_ctor_get(v_a_1184_, 1);
                        v_isSharedCheck_1319_ = (!leanh::lean_is_exclusive(v_a_1184_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1188_ = v_a_1184_;
                            v_isShared_1189_ = v_isSharedCheck_1319_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1186_);
                            leanh::lean_inc(v_fst_1185_);
                            leanh::lean_dec(v_a_1184_);
                            v___x_1188_ = leanh::lean_box(0);
                            v_isShared_1189_ = v_isSharedCheck_1319_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1108_);
                        v_a_1320_ = leanh::lean_ctor_get(v___x_1183_, 0);
                        v_isSharedCheck_1327_ =
                            (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                        if v_isSharedCheck_1327_ == 0 {
                            v___x_1322_ = v___x_1183_;
                            v_isShared_1323_ = v_isSharedCheck_1327_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1320_);
                            leanh::lean_dec(v___x_1183_);
                            v___x_1322_ = leanh::lean_box(0);
                            v_isShared_1323_ = v_isSharedCheck_1327_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1108_);
                    leanh::lean_dec(v_mvarId_1103_);
                    v_a_1328_ = leanh::lean_ctor_get(v___x_1178_, 0);
                    v_isSharedCheck_1335_ = (!leanh::lean_is_exclusive(v___x_1178_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v___x_1330_ = v___x_1178_;
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1328_);
                        leanh::lean_dec(v___x_1178_);
                        v___x_1330_ = leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 33;
                        continue;
                    }
                }
            }
            13 => {
                leanh::lean_inc(v_fst_1185_);
                v___x_1190_ = l_Lean_MVarId_getTag(
                    v_fst_1185_,
                    v___y_1171_,
                    v___y_1172_,
                    v___y_1173_,
                    v___y_1174_,
                );
                if leanh::lean_obj_tag(v___x_1190_) == 0 {
                    v_a_1191_ = leanh::lean_ctor_get(v___x_1190_, 0);
                    leanh::lean_inc(v_a_1191_);
                    leanh::lean_dec_ref_known(v___x_1190_, 1);
                    v___x_1192_ = 0;
                    leanh::lean_inc(v_fst_1185_);
                    v___x_1193_ =
                        l_Lean_MVarId_setKind___redArg(v_fst_1185_, v___x_1192_, v___y_1172_);
                    if leanh::lean_obj_tag(v___x_1193_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1193_, 1);
                        v___x_1194_ = lean_st_ref_get(v___y_1172_);
                        v___x_1195_ = lean_st_ref_get(v___y_1174_);
                        v___x_1196_ = lean_st_ref_get(v___y_1174_);
                        v_lctx_1197_ = leanh::lean_ctor_get(v___y_1171_, 2);
                        v_mctx_1198_ = leanh::lean_ctor_get(v___x_1194_, 0);
                        leanh::lean_inc_ref(v_mctx_1198_);
                        leanh::lean_dec(v___x_1194_);
                        v_ngen_1199_ = leanh::lean_ctor_get(v___x_1195_, 2);
                        leanh::lean_inc_ref(v_ngen_1199_);
                        leanh::lean_dec(v___x_1195_);
                        v_quotContext_1200_ = leanh::lean_ctor_get(v___y_1173_, 10);
                        v_nextMacroScope_1201_ = leanh::lean_ctor_get(v___x_1196_, 1);
                        leanh::lean_inc(v_nextMacroScope_1201_);
                        leanh::lean_dec(v___x_1196_);
                        v___x_1202_ = 2;
                        leanh::lean_inc_ref(v_lctx_1197_);
                        leanh::lean_inc(v_quotContext_1200_);
                        if v_isShared_1189_ == 0 {
                            leanh::lean_ctor_set(v___x_1188_, 1, v_lctx_1197_);
                            leanh::lean_ctor_set(v___x_1188_, 0, v_quotContext_1200_);
                            v___x_1204_ = v___x_1188_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1302_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1302_,
                                0,
                                v_quotContext_1200_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_lctx_1197_);
                            v___x_1204_ = v_reuseFailAlloc_1302_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1191_);
                        leanh::lean_del_object(v___x_1188_);
                        leanh::lean_dec(v_snd_1186_);
                        leanh::lean_dec(v_fst_1185_);
                        leanh::lean_dec(v___x_1108_);
                        v_a_1303_ = leanh::lean_ctor_get(v___x_1193_, 0);
                        v_isSharedCheck_1310_ =
                            (!leanh::lean_is_exclusive(v___x_1193_)) as u8;
                        if v_isSharedCheck_1310_ == 0 {
                            v___x_1305_ = v___x_1193_;
                            v_isShared_1306_ = v_isSharedCheck_1310_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1303_);
                            leanh::lean_dec(v___x_1193_);
                            v___x_1305_ = leanh::lean_box(0);
                            v_isShared_1306_ = v_isSharedCheck_1310_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1188_);
                    leanh::lean_dec(v_snd_1186_);
                    leanh::lean_dec(v_fst_1185_);
                    leanh::lean_dec(v___x_1108_);
                    v_a_1311_ = leanh::lean_ctor_get(v___x_1190_, 0);
                    v_isSharedCheck_1318_ = (!leanh::lean_is_exclusive(v___x_1190_)) as u8;
                    if v_isSharedCheck_1318_ == 0 {
                        v___x_1313_ = v___x_1190_;
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1311_);
                        leanh::lean_dec(v___x_1190_);
                        v___x_1313_ = leanh::lean_box(0);
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 29;
                        continue;
                    }
                }
            }
            14 => {
                v___x_1205_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_revert___lam__0___closed__0,
                );
                v___x_1206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1206_, 0, v___x_1108_);
                leanh::lean_ctor_set(v___x_1206_, 1, v___x_1205_);
                v___x_1207_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1207_, 0, v_mctx_1198_);
                leanh::lean_ctor_set(v___x_1207_, 1, v_nextMacroScope_1201_);
                leanh::lean_ctor_set(v___x_1207_, 2, v_ngen_1199_);
                leanh::lean_ctor_set(v___x_1207_, 3, v___x_1206_);
                leanh::lean_inc(v_fst_1185_);
                v___x_1208_ = l_Lean_MetavarContext_revert(
                    v_snd_1186_,
                    v_fst_1185_,
                    v_preserveOrder_1106_,
                    v___x_1204_,
                    v___x_1207_,
                );
                leanh::lean_dec_ref(v___x_1204_);
                leanh::lean_dec(v_snd_1186_);
                if leanh::lean_obj_tag(v___x_1208_) == 0 {
                    v_a_1209_ = leanh::lean_ctor_get(v___x_1208_, 0);
                    leanh::lean_inc(v_a_1209_);
                    v_a_1210_ = leanh::lean_ctor_get(v___x_1208_, 1);
                    leanh::lean_inc(v_a_1210_);
                    leanh::lean_dec_ref_known(v___x_1208_, 2);
                    v___x_1211_ = lean_st_ref_take(v___y_1172_);
                    v_mctx_1212_ = leanh::lean_ctor_get(v_a_1210_, 0);
                    leanh::lean_inc_ref(v_mctx_1212_);
                    v_nextMacroScope_1213_ = leanh::lean_ctor_get(v_a_1210_, 1);
                    leanh::lean_inc(v_nextMacroScope_1213_);
                    v_ngen_1214_ = leanh::lean_ctor_get(v_a_1210_, 2);
                    leanh::lean_inc_ref(v_ngen_1214_);
                    leanh::lean_dec(v_a_1210_);
                    v_cache_1215_ = leanh::lean_ctor_get(v___x_1211_, 1);
                    v_zetaDeltaFVarIds_1216_ = leanh::lean_ctor_get(v___x_1211_, 2);
                    v_postponed_1217_ = leanh::lean_ctor_get(v___x_1211_, 3);
                    v_diag_1218_ = leanh::lean_ctor_get(v___x_1211_, 4);
                    v_isSharedCheck_1244_ = (!leanh::lean_is_exclusive(v___x_1211_)) as u8;
                    if v_isSharedCheck_1244_ == 0 {
                        v_unused_1245_ = leanh::lean_ctor_get(v___x_1211_, 0);
                        leanh::lean_dec(v_unused_1245_);
                        v___x_1220_ = v___x_1211_;
                        v_isShared_1221_ = v_isSharedCheck_1244_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1218_);
                        leanh::lean_inc(v_postponed_1217_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1216_);
                        leanh::lean_inc(v_cache_1215_);
                        leanh::lean_dec(v___x_1211_);
                        v___x_1220_ = leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1244_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1191_);
                    v_a_1246_ = leanh::lean_ctor_get(v___x_1208_, 1);
                    leanh::lean_inc(v_a_1246_);
                    leanh::lean_dec_ref_known(v___x_1208_, 2);
                    v___x_1247_ = lean_st_ref_take(v___y_1172_);
                    v_mctx_1248_ = leanh::lean_ctor_get(v_a_1246_, 0);
                    leanh::lean_inc_ref(v_mctx_1248_);
                    v_nextMacroScope_1249_ = leanh::lean_ctor_get(v_a_1246_, 1);
                    leanh::lean_inc(v_nextMacroScope_1249_);
                    v_ngen_1250_ = leanh::lean_ctor_get(v_a_1246_, 2);
                    leanh::lean_inc_ref(v_ngen_1250_);
                    leanh::lean_dec(v_a_1246_);
                    v_cache_1251_ = leanh::lean_ctor_get(v___x_1247_, 1);
                    v_zetaDeltaFVarIds_1252_ = leanh::lean_ctor_get(v___x_1247_, 2);
                    v_postponed_1253_ = leanh::lean_ctor_get(v___x_1247_, 3);
                    v_diag_1254_ = leanh::lean_ctor_get(v___x_1247_, 4);
                    v_isSharedCheck_1300_ = (!leanh::lean_is_exclusive(v___x_1247_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v_unused_1301_ = leanh::lean_ctor_get(v___x_1247_, 0);
                        leanh::lean_dec(v_unused_1301_);
                        v___x_1256_ = v___x_1247_;
                        v_isShared_1257_ = v_isSharedCheck_1300_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1254_);
                        leanh::lean_inc(v_postponed_1253_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1252_);
                        leanh::lean_inc(v_cache_1251_);
                        leanh::lean_dec(v___x_1247_);
                        v___x_1256_ = leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1300_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1221_ == 0 {
                    leanh::lean_ctor_set(v___x_1220_, 0, v_mctx_1212_);
                    v___x_1223_ = v___x_1220_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_mctx_1212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1215_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1243_,
                        2,
                        v_zetaDeltaFVarIds_1216_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1243_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1224_ = lean_st_ref_set(v___y_1172_, v___x_1223_);
                v___x_1225_ = lean_st_ref_take(v___y_1174_);
                v_env_1226_ = leanh::lean_ctor_get(v___x_1225_, 0);
                v_auxDeclNGen_1227_ = leanh::lean_ctor_get(v___x_1225_, 3);
                v_traceState_1228_ = leanh::lean_ctor_get(v___x_1225_, 4);
                v_cache_1229_ = leanh::lean_ctor_get(v___x_1225_, 5);
                v_messages_1230_ = leanh::lean_ctor_get(v___x_1225_, 6);
                v_infoState_1231_ = leanh::lean_ctor_get(v___x_1225_, 7);
                v_snapshotTasks_1232_ = leanh::lean_ctor_get(v___x_1225_, 8);
                v_isSharedCheck_1240_ = (!leanh::lean_is_exclusive(v___x_1225_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v_unused_1241_ = leanh::lean_ctor_get(v___x_1225_, 2);
                    leanh::lean_dec(v_unused_1241_);
                    v_unused_1242_ = leanh::lean_ctor_get(v___x_1225_, 1);
                    leanh::lean_dec(v_unused_1242_);
                    v___x_1234_ = v___x_1225_;
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1232_);
                    leanh::lean_inc(v_infoState_1231_);
                    leanh::lean_inc(v_messages_1230_);
                    leanh::lean_inc(v_cache_1229_);
                    leanh::lean_inc(v_traceState_1228_);
                    leanh::lean_inc(v_auxDeclNGen_1227_);
                    leanh::lean_inc(v_env_1226_);
                    leanh::lean_dec(v___x_1225_);
                    v___x_1234_ = leanh::lean_box(0);
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1235_ == 0 {
                    leanh::lean_ctor_set(v___x_1234_, 2, v_ngen_1214_);
                    leanh::lean_ctor_set(v___x_1234_, 1, v_nextMacroScope_1213_);
                    v___x_1237_ = v___x_1234_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_env_1226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_nextMacroScope_1213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_ngen_1214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_auxDeclNGen_1227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_traceState_1228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 5, v_cache_1229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 6, v_messages_1230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 7, v_infoState_1231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 8, v_snapshotTasks_1232_);
                    v___x_1237_ = v_reuseFailAlloc_1239_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1238_ = lean_st_ref_set(v___y_1174_, v___x_1237_);
                v___y_1116_ = v___y_1172_;
                v___y_1117_ = v___x_1176_;
                v___y_1118_ = v_a_1191_;
                v___y_1119_ = v___x_1202_;
                v___y_1120_ = v_fst_1185_;
                v_a_1121_ = v_a_1209_;
                state = 1;
                continue;
            }
            19 => {
                if v_isShared_1257_ == 0 {
                    leanh::lean_ctor_set(v___x_1256_, 0, v_mctx_1248_);
                    v___x_1259_ = v___x_1256_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_mctx_1248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_cache_1251_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1299_,
                        2,
                        v_zetaDeltaFVarIds_1252_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_postponed_1253_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_diag_1254_);
                    v___x_1259_ = v_reuseFailAlloc_1299_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_1260_ = lean_st_ref_set(v___y_1172_, v___x_1259_);
                v___x_1261_ = lean_st_ref_take(v___y_1174_);
                v_env_1262_ = leanh::lean_ctor_get(v___x_1261_, 0);
                v_auxDeclNGen_1263_ = leanh::lean_ctor_get(v___x_1261_, 3);
                v_traceState_1264_ = leanh::lean_ctor_get(v___x_1261_, 4);
                v_cache_1265_ = leanh::lean_ctor_get(v___x_1261_, 5);
                v_messages_1266_ = leanh::lean_ctor_get(v___x_1261_, 6);
                v_infoState_1267_ = leanh::lean_ctor_get(v___x_1261_, 7);
                v_snapshotTasks_1268_ = leanh::lean_ctor_get(v___x_1261_, 8);
                v_isSharedCheck_1296_ = (!leanh::lean_is_exclusive(v___x_1261_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v_unused_1297_ = leanh::lean_ctor_get(v___x_1261_, 2);
                    leanh::lean_dec(v_unused_1297_);
                    v_unused_1298_ = leanh::lean_ctor_get(v___x_1261_, 1);
                    leanh::lean_dec(v_unused_1298_);
                    v___x_1270_ = v___x_1261_;
                    v_isShared_1271_ = v_isSharedCheck_1296_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1268_);
                    leanh::lean_inc(v_infoState_1267_);
                    leanh::lean_inc(v_messages_1266_);
                    leanh::lean_inc(v_cache_1265_);
                    leanh::lean_inc(v_traceState_1264_);
                    leanh::lean_inc(v_auxDeclNGen_1263_);
                    leanh::lean_inc(v_env_1262_);
                    leanh::lean_dec(v___x_1261_);
                    v___x_1270_ = leanh::lean_box(0);
                    v_isShared_1271_ = v_isSharedCheck_1296_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_1271_ == 0 {
                    leanh::lean_ctor_set(v___x_1270_, 2, v_ngen_1250_);
                    leanh::lean_ctor_set(v___x_1270_, 1, v_nextMacroScope_1249_);
                    v___x_1273_ = v___x_1270_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_env_1262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_nextMacroScope_1249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_ngen_1250_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_auxDeclNGen_1263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_traceState_1264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_cache_1265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_messages_1266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_infoState_1267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_snapshotTasks_1268_);
                    v___x_1273_ = v_reuseFailAlloc_1295_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1274_ = lean_st_ref_set(v___y_1174_, v___x_1273_);
                v___x_1275_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__2_once),
                    _init_l_Lean_MVarId_revert___lam__0___closed__2,
                );
                v___x_1276_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
                    v___x_1275_,
                    v___y_1171_,
                    v___y_1172_,
                    v___y_1173_,
                    v___y_1174_,
                );
                v_a_1277_ = leanh::lean_ctor_get(v___x_1276_, 0);
                leanh::lean_inc(v_a_1277_);
                leanh::lean_dec_ref(v___x_1276_);
                v___x_1278_ = l_Lean_MVarId_setKind___redArg(v_fst_1185_, v___x_1202_, v___y_1172_);
                if leanh::lean_obj_tag(v___x_1278_) == 0 {
                    v_isSharedCheck_1285_ = (!leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1285_ == 0 {
                        v_unused_1286_ = leanh::lean_ctor_get(v___x_1278_, 0);
                        leanh::lean_dec(v_unused_1286_);
                        v___x_1280_ = v___x_1278_;
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1278_);
                        v___x_1280_ = leanh::lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 23;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1277_);
                    v_a_1287_ = leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1294_ = (!leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1289_ = v___x_1278_;
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1287_);
                        leanh::lean_dec(v___x_1278_);
                        v___x_1289_ = leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1281_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1280_, 1);
                    leanh::lean_ctor_set(v___x_1280_, 0, v_a_1277_);
                    v___x_1283_ = v___x_1280_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1277_);
                    v___x_1283_ = v_reuseFailAlloc_1284_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1283_;
            }
            25 => {
                if v_isShared_1290_ == 0 {
                    v___x_1292_ = v___x_1289_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
                    v___x_1292_ = v_reuseFailAlloc_1293_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1292_;
            }
            27 => {
                if v_isShared_1306_ == 0 {
                    v___x_1308_ = v___x_1305_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
                    v___x_1308_ = v_reuseFailAlloc_1309_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1308_;
            }
            29 => {
                if v_isShared_1314_ == 0 {
                    v___x_1316_ = v___x_1313_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1316_;
            }
            31 => {
                if v_isShared_1323_ == 0 {
                    v___x_1325_ = v___x_1322_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
                    v___x_1325_ = v_reuseFailAlloc_1326_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1325_;
            }
            33 => {
                if v_isShared_1331_ == 0 {
                    v___x_1333_ = v___x_1330_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
                    v___x_1333_ = v_reuseFailAlloc_1334_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_1333_;
            }
            35 => {
                if v_isShared_1344_ == 0 {
                    v___x_1346_ = v___x_1343_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
                    v___x_1346_ = v_reuseFailAlloc_1347_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1346_;
            }
            37 => {
                if v_isShared_1352_ == 0 {
                    v___x_1354_ = v___x_1351_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_revert___lam__0___boxed(
    mut v_mvarId_1357_: *mut leanh::LeanObject,
    mut v___x_1358_: *mut leanh::LeanObject,
    mut v_fvarIds_1359_: *mut leanh::LeanObject,
    mut v_preserveOrder_1360_: *mut leanh::LeanObject,
    mut v___x_1361_: *mut leanh::LeanObject,
    mut v___x_1362_: *mut leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1363_: *mut leanh::LeanObject,
    mut v___y_1364_: *mut leanh::LeanObject,
    mut v___y_1365_: *mut leanh::LeanObject,
    mut v___y_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveOrder_boxed_1369_: u8 = 0;
    let mut v___x_10049__boxed_1370_: u8 = 0;
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_1371_: u8 = 0;
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveOrder_boxed_1369_ = (leanh::lean_unbox(v_preserveOrder_1360_) as u8);
    v___x_10049__boxed_1370_ = (leanh::lean_unbox(v___x_1361_) as u8);
    v_clearAuxDeclsInsteadOfRevert_boxed_1371_ =
        (leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_1363_) as u8);
    v_res_1372_ = l_Lean_MVarId_revert___lam__0(
        v_mvarId_1357_,
        v___x_1358_,
        v_fvarIds_1359_,
        v_preserveOrder_boxed_1369_,
        v___x_10049__boxed_1370_,
        v___x_1362_,
        v_clearAuxDeclsInsteadOfRevert_boxed_1371_,
        v___y_1364_,
        v___y_1365_,
        v___y_1366_,
        v___y_1367_,
    );
    leanh::lean_dec(v___y_1367_);
    leanh::lean_dec_ref(v___y_1366_);
    leanh::lean_dec(v___y_1365_);
    leanh::lean_dec_ref(v___y_1364_);
    return v_res_1372_;
}
pub unsafe fn l_Lean_MVarId_revert(
    mut v_mvarId_1378_: *mut leanh::LeanObject,
    mut v_fvarIds_1379_: *mut leanh::LeanObject,
    mut v_preserveOrder_1380_: u8,
    mut v_clearAuxDeclsInsteadOfRevert_1381_: u8,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    v___x_1387_ = lean_array_get_size(v_fvarIds_1379_);
    v___x_1388_ = leanh::lean_unsigned_to_nat(0);
    v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
    if v___x_1389_ == 0 {
        let mut v___x_1390_: u8 = 0;
        let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1390_ = 1;
        v___x_1391_ = l_Lean_MVarId_revert___closed__1;
        v___x_1392_ = leanh::lean_box((v_preserveOrder_1380_) as usize);
        v___x_1393_ = leanh::lean_box((v___x_1390_) as usize);
        v___x_1394_ = leanh::lean_box((v_clearAuxDeclsInsteadOfRevert_1381_) as usize);
        leanh::lean_inc(v_mvarId_1378_);
        v___f_1395_ = leanh::lean_alloc_closure(
            l_Lean_MVarId_revert___lam__0___boxed as *mut core::ffi::c_void,
            12,
            7,
        );
        leanh::lean_closure_set(v___f_1395_, 0, v_mvarId_1378_);
        leanh::lean_closure_set(v___f_1395_, 1, v___x_1391_);
        leanh::lean_closure_set(v___f_1395_, 2, v_fvarIds_1379_);
        leanh::lean_closure_set(v___f_1395_, 3, v___x_1392_);
        leanh::lean_closure_set(v___f_1395_, 4, v___x_1393_);
        leanh::lean_closure_set(v___f_1395_, 5, v___x_1388_);
        leanh::lean_closure_set(v___f_1395_, 6, v___x_1394_);
        v___x_1396_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
            v_mvarId_1378_,
            v___f_1395_,
            v_a_1382_,
            v_a_1383_,
            v_a_1384_,
            v_a_1385_,
        );
        return v___x_1396_;
    } else {
        let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_fvarIds_1379_);
        v___x_1397_ = l_Lean_MVarId_revert___closed__2;
        v___x_1398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
        leanh::lean_ctor_set(v___x_1398_, 1, v_mvarId_1378_);
        v___x_1399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1399_, 0, v___x_1398_);
        return v___x_1399_;
    }
}
pub unsafe fn l_Lean_MVarId_revert___boxed(
    mut v_mvarId_1400_: *mut leanh::LeanObject,
    mut v_fvarIds_1401_: *mut leanh::LeanObject,
    mut v_preserveOrder_1402_: *mut leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveOrder_boxed_1409_: u8 = 0;
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_1410_: u8 = 0;
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveOrder_boxed_1409_ = (leanh::lean_unbox(v_preserveOrder_1402_) as u8);
    v_clearAuxDeclsInsteadOfRevert_boxed_1410_ =
        (leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_1403_) as u8);
    v_res_1411_ = l_Lean_MVarId_revert(
        v_mvarId_1400_,
        v_fvarIds_1401_,
        v_preserveOrder_boxed_1409_,
        v_clearAuxDeclsInsteadOfRevert_boxed_1410_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
        v_a_1407_,
    );
    leanh::lean_dec(v_a_1407_);
    leanh::lean_dec_ref(v_a_1406_);
    leanh::lean_dec(v_a_1405_);
    leanh::lean_dec_ref(v_a_1404_);
    return v_res_1411_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(
    mut v_00_u03b1_1412_: *mut leanh::LeanObject,
    mut v_msg_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
        v_msg_1413_,
        v___y_1414_,
        v___y_1415_,
        v___y_1416_,
        v___y_1417_,
    );
    return v___x_1419_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___boxed(
    mut v_00_u03b1_1420_: *mut leanh::LeanObject,
    mut v_msg_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(
        v_00_u03b1_1420_,
        v_msg_1421_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
    );
    leanh::lean_dec(v___y_1425_);
    leanh::lean_dec_ref(v___y_1424_);
    leanh::lean_dec(v___y_1423_);
    leanh::lean_dec_ref(v___y_1422_);
    return v_res_1427_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(
    mut v_as_1428_: *mut leanh::LeanObject,
    mut v_i_1429_: usize,
    mut v_stop_1430_: usize,
    mut v_b_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: usize = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1437_ = lean_usize_dec_eq(v_i_1429_, v_stop_1430_);
                if v___x_1437_ == 0 {
                    v___x_1438_ = lean_array_uget_borrowed(v_as_1428_, v_i_1429_);
                    if leanh::lean_obj_tag(v___x_1438_) == 0 {
                        v___y_1433_ = v_b_1431_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1439_ = leanh::lean_ctor_get(v___x_1438_, 0);
                        v___x_1440_ = l_Lean_LocalDecl_fvarId(v_val_1439_);
                        v___x_1441_ = lean_array_push(v_b_1431_, v___x_1440_);
                        v___y_1433_ = v___x_1441_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1431_;
                }
            }
            1 => {
                v___x_1434_ = 1usize;
                v___x_1435_ = lean_usize_add(v_i_1429_, v___x_1434_);
                v_i_1429_ = v___x_1435_;
                v_b_1431_ = v___y_1433_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2___boxed(
    mut v_as_1442_: *mut leanh::LeanObject,
    mut v_i_1443_: *mut leanh::LeanObject,
    mut v_stop_1444_: *mut leanh::LeanObject,
    mut v_b_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1446_: usize = 0;
    let mut v_stop_boxed_1447_: usize = 0;
    let mut v_res_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1446_ = leanh::lean_unbox_usize(v_i_1443_);
    leanh::lean_dec(v_i_1443_);
    v_stop_boxed_1447_ = leanh::lean_unbox_usize(v_stop_1444_);
    leanh::lean_dec(v_stop_1444_);
    v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_1442_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1445_);
    leanh::lean_dec_ref(v_as_1442_);
    return v_res_1448_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(
    mut v_x_1449_: *mut leanh::LeanObject,
    mut v_x_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1449_) == 0 {
        let mut v_cs_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: u8 = 0;
        v_cs_1451_ = leanh::lean_ctor_get(v_x_1449_, 0);
        v___x_1452_ = leanh::lean_unsigned_to_nat(0);
        v___x_1453_ = lean_array_get_size(v_cs_1451_);
        v___x_1454_ = lean_nat_dec_lt(v___x_1452_, v___x_1453_);
        if v___x_1454_ == 0 {
            return v_x_1450_;
        } else {
            let mut v___x_1455_: u8 = 0;
            v___x_1455_ = lean_nat_dec_le(v___x_1453_, v___x_1453_);
            if v___x_1455_ == 0 {
                if v___x_1454_ == 0 {
                    return v_x_1450_;
                } else {
                    let mut v___x_1456_: usize = 0;
                    let mut v___x_1457_: usize = 0;
                    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1456_ = 0usize;
                    v___x_1457_ = lean_usize_of_nat(v___x_1453_);
                    v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1451_, v___x_1456_, v___x_1457_, v_x_1450_);
                    return v___x_1458_;
                }
            } else {
                let mut v___x_1459_: usize = 0;
                let mut v___x_1460_: usize = 0;
                let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1459_ = 0usize;
                v___x_1460_ = lean_usize_of_nat(v___x_1453_);
                v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1451_, v___x_1459_, v___x_1460_, v_x_1450_);
                return v___x_1461_;
            }
        }
    } else {
        let mut v_vs_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: u8 = 0;
        v_vs_1462_ = leanh::lean_ctor_get(v_x_1449_, 0);
        v___x_1463_ = leanh::lean_unsigned_to_nat(0);
        v___x_1464_ = lean_array_get_size(v_vs_1462_);
        v___x_1465_ = lean_nat_dec_lt(v___x_1463_, v___x_1464_);
        if v___x_1465_ == 0 {
            return v_x_1450_;
        } else {
            let mut v___x_1466_: u8 = 0;
            v___x_1466_ = lean_nat_dec_le(v___x_1464_, v___x_1464_);
            if v___x_1466_ == 0 {
                if v___x_1465_ == 0 {
                    return v_x_1450_;
                } else {
                    let mut v___x_1467_: usize = 0;
                    let mut v___x_1468_: usize = 0;
                    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1467_ = 0usize;
                    v___x_1468_ = lean_usize_of_nat(v___x_1464_);
                    v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1462_, v___x_1467_, v___x_1468_, v_x_1450_);
                    return v___x_1469_;
                }
            } else {
                let mut v___x_1470_: usize = 0;
                let mut v___x_1471_: usize = 0;
                let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1470_ = 0usize;
                v___x_1471_ = lean_usize_of_nat(v___x_1464_);
                v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1462_, v___x_1470_, v___x_1471_, v_x_1450_);
                return v___x_1472_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(
    mut v_as_1473_: *mut leanh::LeanObject,
    mut v_i_1474_: usize,
    mut v_stop_1475_: usize,
    mut v_b_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_usize_dec_eq(v_i_1474_, v_stop_1475_);
                if v___x_1477_ == 0 {
                    v___x_1478_ = lean_array_uget_borrowed(v_as_1473_, v_i_1474_);
                    v___x_1479_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v___x_1478_, v_b_1476_);
                    v___x_1480_ = 1usize;
                    v___x_1481_ = lean_usize_add(v_i_1474_, v___x_1480_);
                    v_i_1474_ = v___x_1481_;
                    v_b_1476_ = v___x_1479_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1476_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_as_1483_: *mut leanh::LeanObject,
    mut v_i_1484_: *mut leanh::LeanObject,
    mut v_stop_1485_: *mut leanh::LeanObject,
    mut v_b_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1487_: usize = 0;
    let mut v_stop_boxed_1488_: usize = 0;
    let mut v_res_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1487_ = leanh::lean_unbox_usize(v_i_1484_);
    leanh::lean_dec(v_i_1484_);
    v_stop_boxed_1488_ = leanh::lean_unbox_usize(v_stop_1485_);
    leanh::lean_dec(v_stop_1485_);
    v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1486_);
    leanh::lean_dec_ref(v_as_1483_);
    return v_res_1489_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(
    mut v_x_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_1490_, v_x_1491_);
    leanh::lean_dec_ref(v_x_1490_);
    return v_res_1492_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_1493_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(
    mut v_x_1494_: *mut leanh::LeanObject,
    mut v_x_1495_: usize,
    mut v_x_1496_: usize,
    mut v_x_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1494_) == 0 {
        let mut v_cs_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: usize = 0;
        let mut v_j_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: usize = 0;
        let mut v___x_1504_: usize = 0;
        let mut v___x_1505_: usize = 0;
        let mut v___x_1506_: usize = 0;
        let mut v___x_1507_: usize = 0;
        let mut v___x_1508_: usize = 0;
        let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1513_: u8 = 0;
        v_cs_1498_ = leanh::lean_ctor_get(v_x_1494_, 0);
        v___x_1499_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
        v___x_1500_ = lean_usize_shift_right(v_x_1495_, v_x_1496_);
        v_j_1501_ = lean_usize_to_nat(v___x_1500_);
        v___x_1502_ = lean_array_get_borrowed(v___x_1499_, v_cs_1498_, v_j_1501_);
        v___x_1503_ = 1usize;
        v___x_1504_ = lean_usize_shift_left(v___x_1503_, v_x_1496_);
        v___x_1505_ = lean_usize_sub(v___x_1504_, v___x_1503_);
        v___x_1506_ = lean_usize_land(v_x_1495_, v___x_1505_);
        v___x_1507_ = 5usize;
        v___x_1508_ = lean_usize_sub(v_x_1496_, v___x_1507_);
        v___x_1509_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v___x_1502_, v___x_1506_, v___x_1508_, v_x_1497_);
        v___x_1510_ = leanh::lean_unsigned_to_nat(1);
        v___x_1511_ = lean_nat_add(v_j_1501_, v___x_1510_);
        leanh::lean_dec(v_j_1501_);
        v___x_1512_ = lean_array_get_size(v_cs_1498_);
        v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
        if v___x_1513_ == 0 {
            leanh::lean_dec(v___x_1511_);
            return v___x_1509_;
        } else {
            let mut v___x_1514_: u8 = 0;
            v___x_1514_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
            if v___x_1514_ == 0 {
                if v___x_1513_ == 0 {
                    leanh::lean_dec(v___x_1511_);
                    return v___x_1509_;
                } else {
                    let mut v___x_1515_: usize = 0;
                    let mut v___x_1516_: usize = 0;
                    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1515_ = lean_usize_of_nat(v___x_1511_);
                    leanh::lean_dec(v___x_1511_);
                    v___x_1516_ = lean_usize_of_nat(v___x_1512_);
                    v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1498_, v___x_1515_, v___x_1516_, v___x_1509_);
                    return v___x_1517_;
                }
            } else {
                let mut v___x_1518_: usize = 0;
                let mut v___x_1519_: usize = 0;
                let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1518_ = lean_usize_of_nat(v___x_1511_);
                leanh::lean_dec(v___x_1511_);
                v___x_1519_ = lean_usize_of_nat(v___x_1512_);
                v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1498_, v___x_1518_, v___x_1519_, v___x_1509_);
                return v___x_1520_;
            }
        }
    } else {
        let mut v_vs_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: u8 = 0;
        v_vs_1521_ = leanh::lean_ctor_get(v_x_1494_, 0);
        v___x_1522_ = lean_usize_to_nat(v_x_1495_);
        v___x_1523_ = lean_array_get_size(v_vs_1521_);
        v___x_1524_ = lean_nat_dec_lt(v___x_1522_, v___x_1523_);
        if v___x_1524_ == 0 {
            leanh::lean_dec(v___x_1522_);
            return v_x_1497_;
        } else {
            let mut v___x_1525_: u8 = 0;
            v___x_1525_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
            if v___x_1525_ == 0 {
                if v___x_1524_ == 0 {
                    leanh::lean_dec(v___x_1522_);
                    return v_x_1497_;
                } else {
                    let mut v___x_1526_: usize = 0;
                    let mut v___x_1527_: usize = 0;
                    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1526_ = lean_usize_of_nat(v___x_1522_);
                    leanh::lean_dec(v___x_1522_);
                    v___x_1527_ = lean_usize_of_nat(v___x_1523_);
                    v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1521_, v___x_1526_, v___x_1527_, v_x_1497_);
                    return v___x_1528_;
                }
            } else {
                let mut v___x_1529_: usize = 0;
                let mut v___x_1530_: usize = 0;
                let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1529_ = lean_usize_of_nat(v___x_1522_);
                leanh::lean_dec(v___x_1522_);
                v___x_1530_ = lean_usize_of_nat(v___x_1523_);
                v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1521_, v___x_1529_, v___x_1530_, v_x_1497_);
                return v___x_1531_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(
    mut v_x_1532_: *mut leanh::LeanObject,
    mut v_x_1533_: *mut leanh::LeanObject,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_x_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1742__boxed_1536_: usize = 0;
    let mut v_x_1743__boxed_1537_: usize = 0;
    let mut v_res_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1742__boxed_1536_ = leanh::lean_unbox_usize(v_x_1533_);
    leanh::lean_dec(v_x_1533_);
    v_x_1743__boxed_1537_ = leanh::lean_unbox_usize(v_x_1534_);
    leanh::lean_dec(v_x_1534_);
    v_res_1538_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_1532_, v_x_1742__boxed_1536_, v_x_1743__boxed_1537_, v_x_1535_);
    leanh::lean_dec_ref(v_x_1532_);
    return v_res_1538_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(
    mut v_t_1539_: *mut leanh::LeanObject,
    mut v_init_1540_: *mut leanh::LeanObject,
    mut v_start_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    v___x_1542_ = leanh::lean_unsigned_to_nat(0);
    v___x_1543_ = lean_nat_dec_eq(v_start_1541_, v___x_1542_);
    if v___x_1543_ == 0 {
        let mut v_root_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_1546_: usize = 0;
        let mut v_tailOff_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: u8 = 0;
        v_root_1544_ = leanh::lean_ctor_get(v_t_1539_, 0);
        v_tail_1545_ = leanh::lean_ctor_get(v_t_1539_, 1);
        v_shift_1546_ = leanh::lean_ctor_get_usize(v_t_1539_, 4);
        v_tailOff_1547_ = leanh::lean_ctor_get(v_t_1539_, 3);
        v___x_1548_ = lean_nat_dec_le(v_tailOff_1547_, v_start_1541_);
        if v___x_1548_ == 0 {
            let mut v___x_1549_: usize = 0;
            let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1552_: u8 = 0;
            v___x_1549_ = lean_usize_of_nat(v_start_1541_);
            v___x_1550_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_root_1544_, v___x_1549_, v_shift_1546_, v_init_1540_);
            v___x_1551_ = lean_array_get_size(v_tail_1545_);
            v___x_1552_ = lean_nat_dec_lt(v___x_1542_, v___x_1551_);
            if v___x_1552_ == 0 {
                return v___x_1550_;
            } else {
                let mut v___x_1553_: u8 = 0;
                v___x_1553_ = lean_nat_dec_le(v___x_1551_, v___x_1551_);
                if v___x_1553_ == 0 {
                    if v___x_1552_ == 0 {
                        return v___x_1550_;
                    } else {
                        let mut v___x_1554_: usize = 0;
                        let mut v___x_1555_: usize = 0;
                        let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1554_ = 0usize;
                        v___x_1555_ = lean_usize_of_nat(v___x_1551_);
                        v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1554_, v___x_1555_, v___x_1550_);
                        return v___x_1556_;
                    }
                } else {
                    let mut v___x_1557_: usize = 0;
                    let mut v___x_1558_: usize = 0;
                    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1557_ = 0usize;
                    v___x_1558_ = lean_usize_of_nat(v___x_1551_);
                    v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1557_, v___x_1558_, v___x_1550_);
                    return v___x_1559_;
                }
            }
        } else {
            let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1562_: u8 = 0;
            v___x_1560_ = lean_nat_sub(v_start_1541_, v_tailOff_1547_);
            v___x_1561_ = lean_array_get_size(v_tail_1545_);
            v___x_1562_ = lean_nat_dec_lt(v___x_1560_, v___x_1561_);
            if v___x_1562_ == 0 {
                leanh::lean_dec(v___x_1560_);
                return v_init_1540_;
            } else {
                let mut v___x_1563_: u8 = 0;
                v___x_1563_ = lean_nat_dec_le(v___x_1561_, v___x_1561_);
                if v___x_1563_ == 0 {
                    if v___x_1562_ == 0 {
                        leanh::lean_dec(v___x_1560_);
                        return v_init_1540_;
                    } else {
                        let mut v___x_1564_: usize = 0;
                        let mut v___x_1565_: usize = 0;
                        let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1564_ = lean_usize_of_nat(v___x_1560_);
                        leanh::lean_dec(v___x_1560_);
                        v___x_1565_ = lean_usize_of_nat(v___x_1561_);
                        v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1564_, v___x_1565_, v_init_1540_);
                        return v___x_1566_;
                    }
                } else {
                    let mut v___x_1567_: usize = 0;
                    let mut v___x_1568_: usize = 0;
                    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1567_ = lean_usize_of_nat(v___x_1560_);
                    leanh::lean_dec(v___x_1560_);
                    v___x_1568_ = lean_usize_of_nat(v___x_1561_);
                    v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1567_, v___x_1568_, v_init_1540_);
                    return v___x_1569_;
                }
            }
        }
    } else {
        let mut v_root_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: u8 = 0;
        v_root_1570_ = leanh::lean_ctor_get(v_t_1539_, 0);
        v_tail_1571_ = leanh::lean_ctor_get(v_t_1539_, 1);
        v___x_1572_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_root_1570_, v_init_1540_);
        v___x_1573_ = lean_array_get_size(v_tail_1571_);
        v___x_1574_ = lean_nat_dec_lt(v___x_1542_, v___x_1573_);
        if v___x_1574_ == 0 {
            return v___x_1572_;
        } else {
            let mut v___x_1575_: u8 = 0;
            v___x_1575_ = lean_nat_dec_le(v___x_1573_, v___x_1573_);
            if v___x_1575_ == 0 {
                if v___x_1574_ == 0 {
                    return v___x_1572_;
                } else {
                    let mut v___x_1576_: usize = 0;
                    let mut v___x_1577_: usize = 0;
                    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1576_ = 0usize;
                    v___x_1577_ = lean_usize_of_nat(v___x_1573_);
                    v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1571_, v___x_1576_, v___x_1577_, v___x_1572_);
                    return v___x_1578_;
                }
            } else {
                let mut v___x_1579_: usize = 0;
                let mut v___x_1580_: usize = 0;
                let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1579_ = 0usize;
                v___x_1580_ = lean_usize_of_nat(v___x_1573_);
                v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1571_, v___x_1579_, v___x_1580_, v___x_1572_);
                return v___x_1581_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(
    mut v_t_1582_: *mut leanh::LeanObject,
    mut v_init_1583_: *mut leanh::LeanObject,
    mut v_start_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_1582_, v_init_1583_, v_start_1584_);
    leanh::lean_dec(v_start_1584_);
    leanh::lean_dec_ref(v_t_1582_);
    return v_res_1585_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
    mut v_lctx_1586_: *mut leanh::LeanObject,
    mut v_init_1587_: *mut leanh::LeanObject,
    mut v_start_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_1589_ = leanh::lean_ctor_get(v_lctx_1586_, 1);
    v___x_1590_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_1589_, v_init_1587_, v_start_1588_);
    return v___x_1590_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(
    mut v_lctx_1591_: *mut leanh::LeanObject,
    mut v_init_1592_: *mut leanh::LeanObject,
    mut v_start_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
        v_lctx_1591_,
        v_init_1592_,
        v_start_1593_,
    );
    leanh::lean_dec(v_start_1593_);
    leanh::lean_dec_ref(v_lctx_1591_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_MVarId_revertAfter___lam__0(
    mut v_fvarId_1595_: *mut leanh::LeanObject,
    mut v_mvarId_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1602_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_1595_,
                    v___y_1597_,
                    v___y_1599_,
                    v___y_1600_,
                );
                if leanh::lean_obj_tag(v___x_1602_) == 0 {
                    v_a_1603_ = leanh::lean_ctor_get(v___x_1602_, 0);
                    leanh::lean_inc(v_a_1603_);
                    leanh::lean_dec_ref_known(v___x_1602_, 1);
                    v_lctx_1604_ = leanh::lean_ctor_get(v___y_1597_, 2);
                    v___x_1605_ = l_Lean_MVarId_revert___closed__2;
                    v___x_1606_ = l_Lean_LocalDecl_index(v_a_1603_);
                    leanh::lean_dec(v_a_1603_);
                    v___x_1607_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1608_ = lean_nat_add(v___x_1606_, v___x_1607_);
                    leanh::lean_dec(v___x_1606_);
                    v___x_1609_ =
                        l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
                            v_lctx_1604_,
                            v___x_1605_,
                            v___x_1608_,
                        );
                    leanh::lean_dec(v___x_1608_);
                    v___x_1610_ = 1;
                    v___x_1611_ = l_Lean_MVarId_revert(
                        v_mvarId_1596_,
                        v___x_1609_,
                        v___x_1610_,
                        v___x_1610_,
                        v___y_1597_,
                        v___y_1598_,
                        v___y_1599_,
                        v___y_1600_,
                    );
                    return v___x_1611_;
                } else {
                    leanh::lean_dec(v_mvarId_1596_);
                    v_a_1612_ = leanh::lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1619_ = (!leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1614_ = v___x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1612_);
                        leanh::lean_dec(v___x_1602_);
                        v___x_1614_ = leanh::lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1615_ == 0 {
                    v___x_1617_ = v___x_1614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
                    v___x_1617_ = v_reuseFailAlloc_1618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_revertAfter___lam__0___boxed(
    mut v_fvarId_1620_: *mut leanh::LeanObject,
    mut v_mvarId_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Lean_MVarId_revertAfter___lam__0(
        v_fvarId_1620_,
        v_mvarId_1621_,
        v___y_1622_,
        v___y_1623_,
        v___y_1624_,
        v___y_1625_,
    );
    leanh::lean_dec(v___y_1625_);
    leanh::lean_dec_ref(v___y_1624_);
    leanh::lean_dec(v___y_1623_);
    leanh::lean_dec_ref(v___y_1622_);
    return v_res_1627_;
}
pub unsafe fn l_Lean_MVarId_revertAfter(
    mut v_mvarId_1628_: *mut leanh::LeanObject,
    mut v_fvarId_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_a_1631_: *mut leanh::LeanObject,
    mut v_a_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_1628_);
    v___f_1635_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_revertAfter___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1635_, 0, v_fvarId_1629_);
    leanh::lean_closure_set(v___f_1635_, 1, v_mvarId_1628_);
    v___x_1636_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
        v_mvarId_1628_,
        v___f_1635_,
        v_a_1630_,
        v_a_1631_,
        v_a_1632_,
        v_a_1633_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Lean_MVarId_revertAfter___boxed(
    mut v_mvarId_1637_: *mut leanh::LeanObject,
    mut v_fvarId_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
    mut v_a_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l_Lean_MVarId_revertAfter(
        v_mvarId_1637_,
        v_fvarId_1638_,
        v_a_1639_,
        v_a_1640_,
        v_a_1641_,
        v_a_1642_,
    );
    leanh::lean_dec(v_a_1642_);
    leanh::lean_dec_ref(v_a_1641_);
    leanh::lean_dec(v_a_1640_);
    leanh::lean_dec_ref(v_a_1639_);
    return v_res_1644_;
}
pub unsafe fn l_Lean_MVarId_revertFrom___lam__0(
    mut v_fvarId_1645_: *mut leanh::LeanObject,
    mut v_mvarId_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1652_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_1645_,
                    v___y_1647_,
                    v___y_1649_,
                    v___y_1650_,
                );
                if leanh::lean_obj_tag(v___x_1652_) == 0 {
                    v_a_1653_ = leanh::lean_ctor_get(v___x_1652_, 0);
                    leanh::lean_inc(v_a_1653_);
                    leanh::lean_dec_ref_known(v___x_1652_, 1);
                    v_lctx_1654_ = leanh::lean_ctor_get(v___y_1647_, 2);
                    v___x_1655_ = l_Lean_MVarId_revert___closed__2;
                    v___x_1656_ = l_Lean_LocalDecl_index(v_a_1653_);
                    leanh::lean_dec(v_a_1653_);
                    v___x_1657_ =
                        l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
                            v_lctx_1654_,
                            v___x_1655_,
                            v___x_1656_,
                        );
                    leanh::lean_dec(v___x_1656_);
                    v___x_1658_ = 1;
                    v___x_1659_ = l_Lean_MVarId_revert(
                        v_mvarId_1646_,
                        v___x_1657_,
                        v___x_1658_,
                        v___x_1658_,
                        v___y_1647_,
                        v___y_1648_,
                        v___y_1649_,
                        v___y_1650_,
                    );
                    return v___x_1659_;
                } else {
                    leanh::lean_dec(v_mvarId_1646_);
                    v_a_1660_ = leanh::lean_ctor_get(v___x_1652_, 0);
                    v_isSharedCheck_1667_ = (!leanh::lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1652_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1660_);
                        leanh::lean_dec(v___x_1652_);
                        v___x_1662_ = leanh::lean_box(0);
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_revertFrom___lam__0___boxed(
    mut v_fvarId_1668_: *mut leanh::LeanObject,
    mut v_mvarId_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Lean_MVarId_revertFrom___lam__0(
        v_fvarId_1668_,
        v_mvarId_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
    );
    leanh::lean_dec(v___y_1673_);
    leanh::lean_dec_ref(v___y_1672_);
    leanh::lean_dec(v___y_1671_);
    leanh::lean_dec_ref(v___y_1670_);
    return v_res_1675_;
}
pub unsafe fn l_Lean_MVarId_revertFrom(
    mut v_mvarId_1676_: *mut leanh::LeanObject,
    mut v_fvarId_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
    mut v_a_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_1676_);
    v___f_1683_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_revertFrom___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1683_, 0, v_fvarId_1677_);
    leanh::lean_closure_set(v___f_1683_, 1, v_mvarId_1676_);
    v___x_1684_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
        v_mvarId_1676_,
        v___f_1683_,
        v_a_1678_,
        v_a_1679_,
        v_a_1680_,
        v_a_1681_,
    );
    return v___x_1684_;
}
pub unsafe fn l_Lean_MVarId_revertFrom___boxed(
    mut v_mvarId_1685_: *mut leanh::LeanObject,
    mut v_fvarId_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v_a_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_MVarId_revertFrom(
        v_mvarId_1685_,
        v_fvarId_1686_,
        v_a_1687_,
        v_a_1688_,
        v_a_1689_,
        v_a_1690_,
    );
    leanh::lean_dec(v_a_1690_);
    leanh::lean_dec_ref(v_a_1689_);
    leanh::lean_dec(v_a_1688_);
    leanh::lean_dec_ref(v_a_1687_);
    return v_res_1692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Revert(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Revert(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Revert(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Revert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Revert(builtin);
}