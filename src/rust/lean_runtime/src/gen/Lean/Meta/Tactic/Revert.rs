// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Lean.Meta.Tactic.Clear
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 118, 101, 114, 116, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value: crate::leanh::LeanStringObject<106> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [96, 58, 32, 73, 116, 32, 105, 115, 32, 97, 110, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 99, 114, 101, 97, 116, 101, 100, 32, 116, 111, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 97, 110, 32, 105, 110, 45, 112, 114, 111, 103, 114, 101, 115, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_revert___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_revert___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_revert___lam__0___closed__1_value: crate::leanh::LeanStringObject<76> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_revert___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_revert___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_revert___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_revert___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_revert___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_revert___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_revert___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6626065151470369524 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_revert___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_revert___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_MVarId_revert___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revert___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
    mut v_mvarId_847_: *mut crate::leanh::LeanObject,
    mut v_x_848_: *mut crate::leanh::LeanObject,
    mut v___y_849_: *mut crate::leanh::LeanObject,
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_a_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_854_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_847_,
                    v_x_848_,
                    v___y_849_,
                    v___y_850_,
                    v___y_851_,
                    v___y_852_,
                );
                if crate::leanh::lean_obj_tag(v___x_854_) == 0 {
                    v_a_855_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                    v_isSharedCheck_862_ = (!crate::leanh::lean_is_exclusive(v___x_854_)) as u8;
                    if v_isSharedCheck_862_ == 0 {
                        v___x_857_ = v___x_854_;
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_855_);
                        crate::leanh::lean_dec(v___x_854_);
                        v___x_857_ = crate::leanh::lean_box(0);
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_863_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                    v_isSharedCheck_870_ = (!crate::leanh::lean_is_exclusive(v___x_854_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_865_ = v___x_854_;
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_863_);
                        crate::leanh::lean_dec(v___x_854_);
                        v___x_865_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
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
                    v_reuseFailAlloc_869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
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
    mut v_mvarId_871_: *mut crate::leanh::LeanObject,
    mut v_x_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
    mut v___y_876_: *mut crate::leanh::LeanObject,
    mut v___y_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(
        v_mvarId_871_,
        v_x_872_,
        v___y_873_,
        v___y_874_,
        v___y_875_,
        v___y_876_,
    );
    crate::leanh::lean_dec(v___y_876_);
    crate::leanh::lean_dec_ref(v___y_875_);
    crate::leanh::lean_dec(v___y_874_);
    crate::leanh::lean_dec_ref(v___y_873_);
    return v_res_878_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(
    mut v_00_u03b1_879_: *mut crate::leanh::LeanObject,
    mut v_mvarId_880_: *mut crate::leanh::LeanObject,
    mut v_x_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
    mut v___y_884_: *mut crate::leanh::LeanObject,
    mut v___y_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_888_: *mut crate::leanh::LeanObject,
    mut v_mvarId_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
    mut v___y_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(
        v_00_u03b1_888_,
        v_mvarId_889_,
        v_x_890_,
        v___y_891_,
        v___y_892_,
        v___y_893_,
        v___y_894_,
    );
    crate::leanh::lean_dec(v___y_894_);
    crate::leanh::lean_dec_ref(v___y_893_);
    crate::leanh::lean_dec(v___y_892_);
    crate::leanh::lean_dec_ref(v___y_891_);
    return v_res_896_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(
    mut v_msgData_897_: *mut crate::leanh::LeanObject,
    mut v___y_898_: *mut crate::leanh::LeanObject,
    mut v___y_899_: *mut crate::leanh::LeanObject,
    mut v___y_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = lean_st_ref_get(v___y_901_);
    v_env_904_ = crate::leanh::lean_ctor_get(v___x_903_, 0);
    crate::leanh::lean_inc_ref(v_env_904_);
    crate::leanh::lean_dec(v___x_903_);
    v___x_905_ = lean_st_ref_get(v___y_899_);
    v_mctx_906_ = crate::leanh::lean_ctor_get(v___x_905_, 0);
    crate::leanh::lean_inc_ref(v_mctx_906_);
    crate::leanh::lean_dec(v___x_905_);
    v_lctx_907_ = crate::leanh::lean_ctor_get(v___y_898_, 2);
    v_options_908_ = crate::leanh::lean_ctor_get(v___y_900_, 2);
    crate::leanh::lean_inc_ref(v_options_908_);
    crate::leanh::lean_inc_ref(v_lctx_907_);
    v___x_909_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_909_, 0, v_env_904_);
    crate::leanh::lean_ctor_set(v___x_909_, 1, v_mctx_906_);
    crate::leanh::lean_ctor_set(v___x_909_, 2, v_lctx_907_);
    crate::leanh::lean_ctor_set(v___x_909_, 3, v_options_908_);
    v___x_910_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_910_, 0, v___x_909_);
    crate::leanh::lean_ctor_set(v___x_910_, 1, v_msgData_897_);
    v___x_911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_911_, 0, v___x_910_);
    return v___x_911_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(
    mut v_msgData_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
    crate::leanh::lean_dec(v___y_916_);
    crate::leanh::lean_dec_ref(v___y_915_);
    crate::leanh::lean_dec(v___y_914_);
    crate::leanh::lean_dec_ref(v___y_913_);
    return v_res_918_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
    mut v_msg_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
    mut v___y_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_925_ = crate::leanh::lean_ctor_get(v___y_922_, 5);
                v___x_926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
                v_a_927_ = crate::leanh::lean_ctor_get(v___x_926_, 0);
                v_isSharedCheck_935_ = (!crate::leanh::lean_is_exclusive(v___x_926_)) as u8;
                if v_isSharedCheck_935_ == 0 {
                    v___x_929_ = v___x_926_;
                    v_isShared_930_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_927_);
                    crate::leanh::lean_dec(v___x_926_);
                    v___x_929_ = crate::leanh::lean_box(0);
                    v_isShared_930_ = v_isSharedCheck_935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_925_);
                v___x_931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_931_, 0, v_ref_925_);
                crate::leanh::lean_ctor_set(v___x_931_, 1, v_a_927_);
                if v_isShared_930_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_929_, 1);
                    crate::leanh::lean_ctor_set(v___x_929_, 0, v___x_931_);
                    v___x_933_ = v___x_929_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
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
    mut v_msg_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
    mut v___y_940_: *mut crate::leanh::LeanObject,
    mut v___y_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
        v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_,
    );
    crate::leanh::lean_dec(v___y_940_);
    crate::leanh::lean_dec_ref(v___y_939_);
    crate::leanh::lean_dec(v___y_938_);
    crate::leanh::lean_dec_ref(v___y_937_);
    return v_res_942_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0;
    v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
    return v___x_945_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2;
    v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(
    mut v_as_949_: *mut crate::leanh::LeanObject,
    mut v_sz_950_: usize,
    mut v_i_951_: usize,
    mut v_b_952_: *mut crate::leanh::LeanObject,
    mut v___y_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
    mut v___y_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: usize = 0;
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_963_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
                if v___x_963_ == 0 {
                    v___x_964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_964_, 0, v_b_952_);
                    return v___x_964_;
                } else {
                    v_a_965_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
                    crate::leanh::lean_inc(v_a_965_);
                    v___x_966_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_965_, v___y_953_, v___y_955_, v___y_956_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_966_) == 0 {
                        v_a_967_ = crate::leanh::lean_ctor_get(v___x_966_, 0);
                        crate::leanh::lean_inc(v_a_967_);
                        crate::leanh::lean_dec_ref_known(v___x_966_, 1);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v___x_969_ = l_Lean_LocalDecl_isAuxDecl(v_a_967_);
                        crate::leanh::lean_dec(v_a_967_);
                        if v___x_969_ == 0 {
                            v_a_959_ = v___x_968_;
                            state = 1;
                            continue;
                        } else {
                            v___x_970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1);
                            crate::leanh::lean_inc(v_a_965_);
                            v___x_971_ = l_Lean_mkFVar(v_a_965_);
                            v___x_972_ = l_Lean_MessageData_ofExpr(v___x_971_);
                            v___x_973_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_973_, 0, v___x_970_);
                            crate::leanh::lean_ctor_set(v___x_973_, 1, v___x_972_);
                            v___x_974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3);
                            v___x_975_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_973_);
                            crate::leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
                            v___x_976_ =
                                l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(
                                    v___x_975_, v___y_953_, v___y_954_, v___y_955_, v___y_956_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_976_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_976_, 1);
                                v_a_959_ = v___x_968_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_976_;
                            }
                        }
                    } else {
                        v_a_977_ = crate::leanh::lean_ctor_get(v___x_966_, 0);
                        v_isSharedCheck_984_ = (!crate::leanh::lean_is_exclusive(v___x_966_)) as u8;
                        if v_isSharedCheck_984_ == 0 {
                            v___x_979_ = v___x_966_;
                            v_isShared_980_ = v_isSharedCheck_984_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_977_);
                            crate::leanh::lean_dec(v___x_966_);
                            v___x_979_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
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
    mut v_as_985_: *mut crate::leanh::LeanObject,
    mut v_sz_986_: *mut crate::leanh::LeanObject,
    mut v_i_987_: *mut crate::leanh::LeanObject,
    mut v_b_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_994_: usize = 0;
    let mut v_i_boxed_995_: usize = 0;
    let mut v_res_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_994_ = crate::leanh::lean_unbox_usize(v_sz_986_);
    crate::leanh::lean_dec(v_sz_986_);
    v_i_boxed_995_ = crate::leanh::lean_unbox_usize(v_i_987_);
    crate::leanh::lean_dec(v_i_987_);
    v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_985_, v_sz_boxed_994_, v_i_boxed_995_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
    crate::leanh::lean_dec(v___y_992_);
    crate::leanh::lean_dec_ref(v___y_991_);
    crate::leanh::lean_dec(v___y_990_);
    crate::leanh::lean_dec_ref(v___y_989_);
    crate::leanh::lean_dec_ref(v_as_985_);
    return v_res_996_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(
    mut v_sz_997_: usize,
    mut v_i_998_: usize,
    mut v_bs_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: u8 = 0;
    let mut v_v_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1000_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
                if v___x_1000_ == 0 {
                    return v_bs_999_;
                } else {
                    v_v_1001_ = lean_array_uget(v_bs_999_, v_i_998_);
                    v___x_1002_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1009_: *mut crate::leanh::LeanObject,
    mut v_i_1010_: *mut crate::leanh::LeanObject,
    mut v_bs_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1012_: usize = 0;
    let mut v_i_boxed_1013_: usize = 0;
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1012_ = crate::leanh::lean_unbox_usize(v_sz_1009_);
    crate::leanh::lean_dec(v_sz_1009_);
    v_i_boxed_1013_ = crate::leanh::lean_unbox_usize(v_i_1010_);
    crate::leanh::lean_dec(v_i_1010_);
    v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_boxed_1012_, v_i_boxed_1013_, v_bs_1011_);
    return v_res_1014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(
    mut v_sz_1015_: usize,
    mut v_i_1016_: usize,
    mut v_bs_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: u8 = 0;
    let mut v_v_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: usize = 0;
    let mut v___x_1024_: usize = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1018_ = lean_usize_dec_lt(v_i_1016_, v_sz_1015_);
                if v___x_1018_ == 0 {
                    return v_bs_1017_;
                } else {
                    v_v_1019_ = lean_array_uget(v_bs_1017_, v_i_1016_);
                    v___x_1020_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1021_ = lean_array_uset(v_bs_1017_, v_i_1016_, v___x_1020_);
                    v___x_1022_ = l_Lean_Expr_fvarId_x21(v_v_1019_);
                    crate::leanh::lean_dec(v_v_1019_);
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
    mut v_sz_1027_: *mut crate::leanh::LeanObject,
    mut v_i_1028_: *mut crate::leanh::LeanObject,
    mut v_bs_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1030_: usize = 0;
    let mut v_i_boxed_1031_: usize = 0;
    let mut v_res_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1030_ = crate::leanh::lean_unbox_usize(v_sz_1027_);
    crate::leanh::lean_dec(v_sz_1027_);
    v_i_boxed_1031_ = crate::leanh::lean_unbox_usize(v_i_1028_);
    crate::leanh::lean_dec(v_i_1028_);
    v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_boxed_1030_, v_i_boxed_1031_, v_bs_1029_);
    return v_res_1032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(
    mut v_as_1033_: *mut crate::leanh::LeanObject,
    mut v_sz_1034_: usize,
    mut v_i_1035_: usize,
    mut v_b_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: usize = 0;
    let mut v___x_1045_: usize = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1047_ = lean_usize_dec_lt(v_i_1035_, v_sz_1034_);
                if v___x_1047_ == 0 {
                    v___x_1048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v_b_1036_);
                    return v___x_1048_;
                } else {
                    v_a_1049_ = lean_array_uget_borrowed(v_as_1033_, v_i_1035_);
                    v___x_1050_ = l_Lean_Expr_fvarId_x21(v_a_1049_);
                    crate::leanh::lean_inc(v___x_1050_);
                    v___x_1051_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_1050_,
                        v___y_1037_,
                        v___y_1039_,
                        v___y_1040_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                        v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                        crate::leanh::lean_inc(v_a_1052_);
                        crate::leanh::lean_dec_ref_known(v___x_1051_, 1);
                        v_fst_1053_ = crate::leanh::lean_ctor_get(v_b_1036_, 0);
                        v_snd_1054_ = crate::leanh::lean_ctor_get(v_b_1036_, 1);
                        v_isSharedCheck_1076_ = (!crate::leanh::lean_is_exclusive(v_b_1036_)) as u8;
                        if v_isSharedCheck_1076_ == 0 {
                            v___x_1056_ = v_b_1036_;
                            v_isShared_1057_ = v_isSharedCheck_1076_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1054_);
                            crate::leanh::lean_inc(v_fst_1053_);
                            crate::leanh::lean_dec(v_b_1036_);
                            v___x_1056_ = crate::leanh::lean_box(0);
                            v_isShared_1057_ = v_isSharedCheck_1076_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1050_);
                        crate::leanh::lean_dec_ref(v_b_1036_);
                        v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1084_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1084_ == 0 {
                            v___x_1079_ = v___x_1051_;
                            v_isShared_1080_ = v_isSharedCheck_1084_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1077_);
                            crate::leanh::lean_dec(v___x_1051_);
                            v___x_1079_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_a_1052_);
                if v___x_1058_ == 0 {
                    crate::leanh::lean_dec(v___x_1050_);
                    crate::leanh::lean_inc(v_a_1049_);
                    v___x_1059_ = lean_array_push(v_snd_1054_, v_a_1049_);
                    if v_isShared_1057_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1056_, 1, v___x_1059_);
                        v___x_1061_ = v___x_1056_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_fst_1053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
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
                    if crate::leanh::lean_obj_tag(v___x_1063_) == 0 {
                        v_a_1064_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                        crate::leanh::lean_inc(v_a_1064_);
                        crate::leanh::lean_dec_ref_known(v___x_1063_, 1);
                        if v_isShared_1057_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1056_, 0, v_a_1064_);
                            v___x_1066_ = v___x_1056_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1067_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_snd_1054_);
                            v___x_1066_ = v_reuseFailAlloc_1067_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1056_);
                        crate::leanh::lean_dec(v_snd_1054_);
                        v_a_1068_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                        v_isSharedCheck_1075_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1063_)) as u8;
                        if v_isSharedCheck_1075_ == 0 {
                            v___x_1070_ = v___x_1063_;
                            v_isShared_1071_ = v_isSharedCheck_1075_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1068_);
                            crate::leanh::lean_dec(v___x_1063_);
                            v___x_1070_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
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
                    v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
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
    mut v_as_1085_: *mut crate::leanh::LeanObject,
    mut v_sz_1086_: *mut crate::leanh::LeanObject,
    mut v_i_1087_: *mut crate::leanh::LeanObject,
    mut v_b_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1094_: usize = 0;
    let mut v_i_boxed_1095_: usize = 0;
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1094_ = crate::leanh::lean_unbox_usize(v_sz_1086_);
    crate::leanh::lean_dec(v_sz_1086_);
    v_i_boxed_1095_ = crate::leanh::lean_unbox_usize(v_i_1087_);
    crate::leanh::lean_dec(v_i_1087_);
    v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_1085_, v_sz_boxed_1094_, v_i_boxed_1095_, v_b_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
    crate::leanh::lean_dec(v___y_1092_);
    crate::leanh::lean_dec_ref(v___y_1091_);
    crate::leanh::lean_dec(v___y_1090_);
    crate::leanh::lean_dec_ref(v___y_1089_);
    crate::leanh::lean_dec_ref(v_as_1085_);
    return v_res_1096_;
}
pub unsafe fn _init_l_Lean_MVarId_revert___lam__0___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = crate::leanh::lean_box(0);
    v___x_1098_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1099_ = lean_mk_array(v___x_1098_, v___x_1097_);
    return v___x_1099_;
}
pub unsafe fn _init_l_Lean_MVarId_revert___lam__0___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_MVarId_revert___lam__0___closed__1;
    v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_MVarId_revert___lam__0(
    mut v_mvarId_1103_: *mut crate::leanh::LeanObject,
    mut v___x_1104_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1105_: *mut crate::leanh::LeanObject,
    mut v_preserveOrder_1106_: u8,
    mut v___x_1107_: u8,
    mut v___x_1108_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1109_: u8,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1117_: usize = 0;
    let mut v___y_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1119_: u8 = 0;
    let mut v___y_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v_sz_1135_: usize = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_unused_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut v_a_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v___y_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1175_: usize = 0;
    let mut v___x_1176_: usize = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1182_: usize = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1189_: u8 = 0;
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_unused_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut v_unused_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1306_: u8 = 0;
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_a_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_a_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1338_: usize = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1103_);
                v___x_1336_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1103_,
                    v___x_1104_,
                    v___y_1110_,
                    v___y_1111_,
                    v___y_1112_,
                    v___y_1113_,
                );
                if crate::leanh::lean_obj_tag(v___x_1336_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1336_, 1);
                    if v_clearAuxDeclsInsteadOfRevert_1109_ == 0 {
                        v___x_1337_ = crate::leanh::lean_box(0);
                        v_sz_1338_ = lean_array_size(v_fvarIds_1105_);
                        v___x_1339_ = 0usize;
                        v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_1105_, v_sz_1338_, v___x_1339_, v___x_1337_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
                        if crate::leanh::lean_obj_tag(v___x_1340_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1340_, 1);
                            v___y_1171_ = v___y_1110_;
                            v___y_1172_ = v___y_1111_;
                            v___y_1173_ = v___y_1112_;
                            v___y_1174_ = v___y_1113_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1108_);
                            crate::leanh::lean_dec_ref(v_fvarIds_1105_);
                            crate::leanh::lean_dec(v_mvarId_1103_);
                            v_a_1341_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                            v_isSharedCheck_1348_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1340_)) as u8;
                            if v_isSharedCheck_1348_ == 0 {
                                v___x_1343_ = v___x_1340_;
                                v_isShared_1344_ = v_isSharedCheck_1348_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1341_);
                                crate::leanh::lean_dec(v___x_1340_);
                                v___x_1343_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_1108_);
                    crate::leanh::lean_dec_ref(v_fvarIds_1105_);
                    crate::leanh::lean_dec(v_mvarId_1103_);
                    v_a_1349_ = crate::leanh::lean_ctor_get(v___x_1336_, 0);
                    v_isSharedCheck_1356_ = (!crate::leanh::lean_is_exclusive(v___x_1336_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1351_ = v___x_1336_;
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1349_);
                        crate::leanh::lean_dec(v___x_1336_);
                        v___x_1351_ = crate::leanh::lean_box(0);
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1122_ = l_Lean_MVarId_setKind___redArg(v___y_1120_, v___y_1119_, v___y_1116_);
                if crate::leanh::lean_obj_tag(v___x_1122_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1122_, 1);
                    v_fst_1123_ = crate::leanh::lean_ctor_get(v_a_1121_, 0);
                    v_snd_1124_ = crate::leanh::lean_ctor_get(v_a_1121_, 1);
                    v_isSharedCheck_1161_ = (!crate::leanh::lean_is_exclusive(v_a_1121_)) as u8;
                    if v_isSharedCheck_1161_ == 0 {
                        v___x_1126_ = v_a_1121_;
                        v_isShared_1127_ = v_isSharedCheck_1161_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1124_);
                        crate::leanh::lean_inc(v_fst_1123_);
                        crate::leanh::lean_dec(v_a_1121_);
                        v___x_1126_ = crate::leanh::lean_box(0);
                        v_isShared_1127_ = v_isSharedCheck_1161_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1121_);
                    crate::leanh::lean_dec(v___y_1118_);
                    v_a_1162_ = crate::leanh::lean_ctor_get(v___x_1122_, 0);
                    v_isSharedCheck_1169_ = (!crate::leanh::lean_is_exclusive(v___x_1122_)) as u8;
                    if v_isSharedCheck_1169_ == 0 {
                        v___x_1164_ = v___x_1122_;
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1162_);
                        crate::leanh::lean_dec(v___x_1122_);
                        v___x_1164_ = crate::leanh::lean_box(0);
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1128_ = l_Lean_Expr_getAppFn(v_fst_1123_);
                crate::leanh::lean_dec(v_fst_1123_);
                v___x_1129_ = l_Lean_Expr_mvarId_x21(v___x_1128_);
                crate::leanh::lean_dec_ref(v___x_1128_);
                crate::leanh::lean_inc(v___x_1129_);
                v___x_1130_ = l_Lean_MVarId_setKind___redArg(v___x_1129_, v___y_1119_, v___y_1116_);
                if crate::leanh::lean_obj_tag(v___x_1130_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1130_, 1);
                    crate::leanh::lean_inc(v___x_1129_);
                    v___x_1131_ =
                        l_Lean_MVarId_setTag___redArg(v___x_1129_, v___y_1118_, v___y_1116_);
                    if crate::leanh::lean_obj_tag(v___x_1131_) == 0 {
                        v_isSharedCheck_1143_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1131_)) as u8;
                        if v_isSharedCheck_1143_ == 0 {
                            v_unused_1144_ = crate::leanh::lean_ctor_get(v___x_1131_, 0);
                            crate::leanh::lean_dec(v_unused_1144_);
                            v___x_1133_ = v___x_1131_;
                            v_isShared_1134_ = v_isSharedCheck_1143_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1131_);
                            v___x_1133_ = crate::leanh::lean_box(0);
                            v_isShared_1134_ = v_isSharedCheck_1143_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1129_);
                        crate::leanh::lean_del_object(v___x_1126_);
                        crate::leanh::lean_dec(v_snd_1124_);
                        v_a_1145_ = crate::leanh::lean_ctor_get(v___x_1131_, 0);
                        v_isSharedCheck_1152_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1131_)) as u8;
                        if v_isSharedCheck_1152_ == 0 {
                            v___x_1147_ = v___x_1131_;
                            v_isShared_1148_ = v_isSharedCheck_1152_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1145_);
                            crate::leanh::lean_dec(v___x_1131_);
                            v___x_1147_ = crate::leanh::lean_box(0);
                            v_isShared_1148_ = v_isSharedCheck_1152_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1129_);
                    crate::leanh::lean_del_object(v___x_1126_);
                    crate::leanh::lean_dec(v_snd_1124_);
                    crate::leanh::lean_dec(v___y_1118_);
                    v_a_1153_ = crate::leanh::lean_ctor_get(v___x_1130_, 0);
                    v_isSharedCheck_1160_ = (!crate::leanh::lean_is_exclusive(v___x_1130_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v___x_1155_ = v___x_1130_;
                        v_isShared_1156_ = v_isSharedCheck_1160_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1153_);
                        crate::leanh::lean_dec(v___x_1130_);
                        v___x_1155_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1126_, 1, v___x_1129_);
                    crate::leanh::lean_ctor_set(v___x_1126_, 0, v___x_1136_);
                    v___x_1138_ = v___x_1126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1129_);
                    v___x_1138_ = v_reuseFailAlloc_1142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1138_);
                    v___x_1140_ = v___x_1133_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
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
                    v_reuseFailAlloc_1151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
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
                    v_reuseFailAlloc_1159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
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
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
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
                if crate::leanh::lean_obj_tag(v___x_1178_) == 0 {
                    v_a_1179_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
                    crate::leanh::lean_inc(v_a_1179_);
                    crate::leanh::lean_dec_ref_known(v___x_1178_, 1);
                    v___x_1180_ = lean_mk_empty_array_with_capacity(v___x_1108_);
                    v___x_1181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1181_, 0, v_mvarId_1103_);
                    crate::leanh::lean_ctor_set(v___x_1181_, 1, v___x_1180_);
                    v_sz_1182_ = lean_array_size(v_a_1179_);
                    v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_1179_, v_sz_1182_, v___x_1176_, v___x_1181_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
                    crate::leanh::lean_dec(v_a_1179_);
                    if crate::leanh::lean_obj_tag(v___x_1183_) == 0 {
                        v_a_1184_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                        crate::leanh::lean_inc(v_a_1184_);
                        crate::leanh::lean_dec_ref_known(v___x_1183_, 1);
                        v_fst_1185_ = crate::leanh::lean_ctor_get(v_a_1184_, 0);
                        v_snd_1186_ = crate::leanh::lean_ctor_get(v_a_1184_, 1);
                        v_isSharedCheck_1319_ = (!crate::leanh::lean_is_exclusive(v_a_1184_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1188_ = v_a_1184_;
                            v_isShared_1189_ = v_isSharedCheck_1319_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1186_);
                            crate::leanh::lean_inc(v_fst_1185_);
                            crate::leanh::lean_dec(v_a_1184_);
                            v___x_1188_ = crate::leanh::lean_box(0);
                            v_isShared_1189_ = v_isSharedCheck_1319_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1108_);
                        v_a_1320_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                        v_isSharedCheck_1327_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1183_)) as u8;
                        if v_isSharedCheck_1327_ == 0 {
                            v___x_1322_ = v___x_1183_;
                            v_isShared_1323_ = v_isSharedCheck_1327_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1320_);
                            crate::leanh::lean_dec(v___x_1183_);
                            v___x_1322_ = crate::leanh::lean_box(0);
                            v_isShared_1323_ = v_isSharedCheck_1327_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1108_);
                    crate::leanh::lean_dec(v_mvarId_1103_);
                    v_a_1328_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
                    v_isSharedCheck_1335_ = (!crate::leanh::lean_is_exclusive(v___x_1178_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v___x_1330_ = v___x_1178_;
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1328_);
                        crate::leanh::lean_dec(v___x_1178_);
                        v___x_1330_ = crate::leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 33;
                        continue;
                    }
                }
            }
            13 => {
                crate::leanh::lean_inc(v_fst_1185_);
                v___x_1190_ = l_Lean_MVarId_getTag(
                    v_fst_1185_,
                    v___y_1171_,
                    v___y_1172_,
                    v___y_1173_,
                    v___y_1174_,
                );
                if crate::leanh::lean_obj_tag(v___x_1190_) == 0 {
                    v_a_1191_ = crate::leanh::lean_ctor_get(v___x_1190_, 0);
                    crate::leanh::lean_inc(v_a_1191_);
                    crate::leanh::lean_dec_ref_known(v___x_1190_, 1);
                    v___x_1192_ = 0;
                    crate::leanh::lean_inc(v_fst_1185_);
                    v___x_1193_ =
                        l_Lean_MVarId_setKind___redArg(v_fst_1185_, v___x_1192_, v___y_1172_);
                    if crate::leanh::lean_obj_tag(v___x_1193_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1193_, 1);
                        v___x_1194_ = lean_st_ref_get(v___y_1172_);
                        v___x_1195_ = lean_st_ref_get(v___y_1174_);
                        v___x_1196_ = lean_st_ref_get(v___y_1174_);
                        v_lctx_1197_ = crate::leanh::lean_ctor_get(v___y_1171_, 2);
                        v_mctx_1198_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_1198_);
                        crate::leanh::lean_dec(v___x_1194_);
                        v_ngen_1199_ = crate::leanh::lean_ctor_get(v___x_1195_, 2);
                        crate::leanh::lean_inc_ref(v_ngen_1199_);
                        crate::leanh::lean_dec(v___x_1195_);
                        v_quotContext_1200_ = crate::leanh::lean_ctor_get(v___y_1173_, 10);
                        v_nextMacroScope_1201_ = crate::leanh::lean_ctor_get(v___x_1196_, 1);
                        crate::leanh::lean_inc(v_nextMacroScope_1201_);
                        crate::leanh::lean_dec(v___x_1196_);
                        v___x_1202_ = 2;
                        crate::leanh::lean_inc_ref(v_lctx_1197_);
                        crate::leanh::lean_inc(v_quotContext_1200_);
                        if v_isShared_1189_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1188_, 1, v_lctx_1197_);
                            crate::leanh::lean_ctor_set(v___x_1188_, 0, v_quotContext_1200_);
                            v___x_1204_ = v___x_1188_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1302_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1302_,
                                0,
                                v_quotContext_1200_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_lctx_1197_);
                            v___x_1204_ = v_reuseFailAlloc_1302_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1191_);
                        crate::leanh::lean_del_object(v___x_1188_);
                        crate::leanh::lean_dec(v_snd_1186_);
                        crate::leanh::lean_dec(v_fst_1185_);
                        crate::leanh::lean_dec(v___x_1108_);
                        v_a_1303_ = crate::leanh::lean_ctor_get(v___x_1193_, 0);
                        v_isSharedCheck_1310_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1193_)) as u8;
                        if v_isSharedCheck_1310_ == 0 {
                            v___x_1305_ = v___x_1193_;
                            v_isShared_1306_ = v_isSharedCheck_1310_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1303_);
                            crate::leanh::lean_dec(v___x_1193_);
                            v___x_1305_ = crate::leanh::lean_box(0);
                            v_isShared_1306_ = v_isSharedCheck_1310_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1188_);
                    crate::leanh::lean_dec(v_snd_1186_);
                    crate::leanh::lean_dec(v_fst_1185_);
                    crate::leanh::lean_dec(v___x_1108_);
                    v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1190_, 0);
                    v_isSharedCheck_1318_ = (!crate::leanh::lean_is_exclusive(v___x_1190_)) as u8;
                    if v_isSharedCheck_1318_ == 0 {
                        v___x_1313_ = v___x_1190_;
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1311_);
                        crate::leanh::lean_dec(v___x_1190_);
                        v___x_1313_ = crate::leanh::lean_box(0);
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 29;
                        continue;
                    }
                }
            }
            14 => {
                v___x_1205_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_revert___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_revert___lam__0___closed__0,
                );
                v___x_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1206_, 0, v___x_1108_);
                crate::leanh::lean_ctor_set(v___x_1206_, 1, v___x_1205_);
                v___x_1207_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1207_, 0, v_mctx_1198_);
                crate::leanh::lean_ctor_set(v___x_1207_, 1, v_nextMacroScope_1201_);
                crate::leanh::lean_ctor_set(v___x_1207_, 2, v_ngen_1199_);
                crate::leanh::lean_ctor_set(v___x_1207_, 3, v___x_1206_);
                crate::leanh::lean_inc(v_fst_1185_);
                v___x_1208_ = l_Lean_MetavarContext_revert(
                    v_snd_1186_,
                    v_fst_1185_,
                    v_preserveOrder_1106_,
                    v___x_1204_,
                    v___x_1207_,
                );
                crate::leanh::lean_dec_ref(v___x_1204_);
                crate::leanh::lean_dec(v_snd_1186_);
                if crate::leanh::lean_obj_tag(v___x_1208_) == 0 {
                    v_a_1209_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                    crate::leanh::lean_inc(v_a_1209_);
                    v_a_1210_ = crate::leanh::lean_ctor_get(v___x_1208_, 1);
                    crate::leanh::lean_inc(v_a_1210_);
                    crate::leanh::lean_dec_ref_known(v___x_1208_, 2);
                    v___x_1211_ = lean_st_ref_take(v___y_1172_);
                    v_mctx_1212_ = crate::leanh::lean_ctor_get(v_a_1210_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1212_);
                    v_nextMacroScope_1213_ = crate::leanh::lean_ctor_get(v_a_1210_, 1);
                    crate::leanh::lean_inc(v_nextMacroScope_1213_);
                    v_ngen_1214_ = crate::leanh::lean_ctor_get(v_a_1210_, 2);
                    crate::leanh::lean_inc_ref(v_ngen_1214_);
                    crate::leanh::lean_dec(v_a_1210_);
                    v_cache_1215_ = crate::leanh::lean_ctor_get(v___x_1211_, 1);
                    v_zetaDeltaFVarIds_1216_ = crate::leanh::lean_ctor_get(v___x_1211_, 2);
                    v_postponed_1217_ = crate::leanh::lean_ctor_get(v___x_1211_, 3);
                    v_diag_1218_ = crate::leanh::lean_ctor_get(v___x_1211_, 4);
                    v_isSharedCheck_1244_ = (!crate::leanh::lean_is_exclusive(v___x_1211_)) as u8;
                    if v_isSharedCheck_1244_ == 0 {
                        v_unused_1245_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                        crate::leanh::lean_dec(v_unused_1245_);
                        v___x_1220_ = v___x_1211_;
                        v_isShared_1221_ = v_isSharedCheck_1244_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1218_);
                        crate::leanh::lean_inc(v_postponed_1217_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1216_);
                        crate::leanh::lean_inc(v_cache_1215_);
                        crate::leanh::lean_dec(v___x_1211_);
                        v___x_1220_ = crate::leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1244_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1191_);
                    v_a_1246_ = crate::leanh::lean_ctor_get(v___x_1208_, 1);
                    crate::leanh::lean_inc(v_a_1246_);
                    crate::leanh::lean_dec_ref_known(v___x_1208_, 2);
                    v___x_1247_ = lean_st_ref_take(v___y_1172_);
                    v_mctx_1248_ = crate::leanh::lean_ctor_get(v_a_1246_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1248_);
                    v_nextMacroScope_1249_ = crate::leanh::lean_ctor_get(v_a_1246_, 1);
                    crate::leanh::lean_inc(v_nextMacroScope_1249_);
                    v_ngen_1250_ = crate::leanh::lean_ctor_get(v_a_1246_, 2);
                    crate::leanh::lean_inc_ref(v_ngen_1250_);
                    crate::leanh::lean_dec(v_a_1246_);
                    v_cache_1251_ = crate::leanh::lean_ctor_get(v___x_1247_, 1);
                    v_zetaDeltaFVarIds_1252_ = crate::leanh::lean_ctor_get(v___x_1247_, 2);
                    v_postponed_1253_ = crate::leanh::lean_ctor_get(v___x_1247_, 3);
                    v_diag_1254_ = crate::leanh::lean_ctor_get(v___x_1247_, 4);
                    v_isSharedCheck_1300_ = (!crate::leanh::lean_is_exclusive(v___x_1247_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v_unused_1301_ = crate::leanh::lean_ctor_get(v___x_1247_, 0);
                        crate::leanh::lean_dec(v_unused_1301_);
                        v___x_1256_ = v___x_1247_;
                        v_isShared_1257_ = v_isSharedCheck_1300_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1254_);
                        crate::leanh::lean_inc(v_postponed_1253_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1252_);
                        crate::leanh::lean_inc(v_cache_1251_);
                        crate::leanh::lean_dec(v___x_1247_);
                        v___x_1256_ = crate::leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1300_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1220_, 0, v_mctx_1212_);
                    v___x_1223_ = v___x_1220_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_mctx_1212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1215_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1243_,
                        2,
                        v_zetaDeltaFVarIds_1216_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1243_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1224_ = lean_st_ref_set(v___y_1172_, v___x_1223_);
                v___x_1225_ = lean_st_ref_take(v___y_1174_);
                v_env_1226_ = crate::leanh::lean_ctor_get(v___x_1225_, 0);
                v_auxDeclNGen_1227_ = crate::leanh::lean_ctor_get(v___x_1225_, 3);
                v_traceState_1228_ = crate::leanh::lean_ctor_get(v___x_1225_, 4);
                v_cache_1229_ = crate::leanh::lean_ctor_get(v___x_1225_, 5);
                v_messages_1230_ = crate::leanh::lean_ctor_get(v___x_1225_, 6);
                v_infoState_1231_ = crate::leanh::lean_ctor_get(v___x_1225_, 7);
                v_snapshotTasks_1232_ = crate::leanh::lean_ctor_get(v___x_1225_, 8);
                v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1225_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v_unused_1241_ = crate::leanh::lean_ctor_get(v___x_1225_, 2);
                    crate::leanh::lean_dec(v_unused_1241_);
                    v_unused_1242_ = crate::leanh::lean_ctor_get(v___x_1225_, 1);
                    crate::leanh::lean_dec(v_unused_1242_);
                    v___x_1234_ = v___x_1225_;
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1232_);
                    crate::leanh::lean_inc(v_infoState_1231_);
                    crate::leanh::lean_inc(v_messages_1230_);
                    crate::leanh::lean_inc(v_cache_1229_);
                    crate::leanh::lean_inc(v_traceState_1228_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1227_);
                    crate::leanh::lean_inc(v_env_1226_);
                    crate::leanh::lean_dec(v___x_1225_);
                    v___x_1234_ = crate::leanh::lean_box(0);
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1234_, 2, v_ngen_1214_);
                    crate::leanh::lean_ctor_set(v___x_1234_, 1, v_nextMacroScope_1213_);
                    v___x_1237_ = v___x_1234_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_env_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_nextMacroScope_1213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_ngen_1214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_auxDeclNGen_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_traceState_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 5, v_cache_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 6, v_messages_1230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 7, v_infoState_1231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 8, v_snapshotTasks_1232_);
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
                    crate::leanh::lean_ctor_set(v___x_1256_, 0, v_mctx_1248_);
                    v___x_1259_ = v___x_1256_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_mctx_1248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_cache_1251_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1299_,
                        2,
                        v_zetaDeltaFVarIds_1252_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_postponed_1253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_diag_1254_);
                    v___x_1259_ = v_reuseFailAlloc_1299_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_1260_ = lean_st_ref_set(v___y_1172_, v___x_1259_);
                v___x_1261_ = lean_st_ref_take(v___y_1174_);
                v_env_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
                v_auxDeclNGen_1263_ = crate::leanh::lean_ctor_get(v___x_1261_, 3);
                v_traceState_1264_ = crate::leanh::lean_ctor_get(v___x_1261_, 4);
                v_cache_1265_ = crate::leanh::lean_ctor_get(v___x_1261_, 5);
                v_messages_1266_ = crate::leanh::lean_ctor_get(v___x_1261_, 6);
                v_infoState_1267_ = crate::leanh::lean_ctor_get(v___x_1261_, 7);
                v_snapshotTasks_1268_ = crate::leanh::lean_ctor_get(v___x_1261_, 8);
                v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v___x_1261_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v_unused_1297_ = crate::leanh::lean_ctor_get(v___x_1261_, 2);
                    crate::leanh::lean_dec(v_unused_1297_);
                    v_unused_1298_ = crate::leanh::lean_ctor_get(v___x_1261_, 1);
                    crate::leanh::lean_dec(v_unused_1298_);
                    v___x_1270_ = v___x_1261_;
                    v_isShared_1271_ = v_isSharedCheck_1296_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1268_);
                    crate::leanh::lean_inc(v_infoState_1267_);
                    crate::leanh::lean_inc(v_messages_1266_);
                    crate::leanh::lean_inc(v_cache_1265_);
                    crate::leanh::lean_inc(v_traceState_1264_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1263_);
                    crate::leanh::lean_inc(v_env_1262_);
                    crate::leanh::lean_dec(v___x_1261_);
                    v___x_1270_ = crate::leanh::lean_box(0);
                    v_isShared_1271_ = v_isSharedCheck_1296_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_1271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1270_, 2, v_ngen_1250_);
                    crate::leanh::lean_ctor_set(v___x_1270_, 1, v_nextMacroScope_1249_);
                    v___x_1273_ = v___x_1270_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_env_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_nextMacroScope_1249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_ngen_1250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_auxDeclNGen_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_traceState_1264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_cache_1265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_messages_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_infoState_1267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_snapshotTasks_1268_);
                    v___x_1273_ = v_reuseFailAlloc_1295_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1274_ = lean_st_ref_set(v___y_1174_, v___x_1273_);
                v___x_1275_ = crate::leanh::lean_obj_once(
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
                v_a_1277_ = crate::leanh::lean_ctor_get(v___x_1276_, 0);
                crate::leanh::lean_inc(v_a_1277_);
                crate::leanh::lean_dec_ref(v___x_1276_);
                v___x_1278_ = l_Lean_MVarId_setKind___redArg(v_fst_1185_, v___x_1202_, v___y_1172_);
                if crate::leanh::lean_obj_tag(v___x_1278_) == 0 {
                    v_isSharedCheck_1285_ = (!crate::leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1285_ == 0 {
                        v_unused_1286_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                        crate::leanh::lean_dec(v_unused_1286_);
                        v___x_1280_ = v___x_1278_;
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1278_);
                        v___x_1280_ = crate::leanh::lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1277_);
                    v_a_1287_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1289_ = v___x_1278_;
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1287_);
                        crate::leanh::lean_dec(v___x_1278_);
                        v___x_1289_ = crate::leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1281_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1280_, 1);
                    crate::leanh::lean_ctor_set(v___x_1280_, 0, v_a_1277_);
                    v___x_1283_ = v___x_1280_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1277_);
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
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
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
                    v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
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
                    v_reuseFailAlloc_1317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
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
                    v_reuseFailAlloc_1326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
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
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
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
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
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
                    v_reuseFailAlloc_1355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
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
    mut v_mvarId_1357_: *mut crate::leanh::LeanObject,
    mut v___x_1358_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1359_: *mut crate::leanh::LeanObject,
    mut v_preserveOrder_1360_: *mut crate::leanh::LeanObject,
    mut v___x_1361_: *mut crate::leanh::LeanObject,
    mut v___x_1362_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveOrder_boxed_1369_: u8 = 0;
    let mut v___x_10049__boxed_1370_: u8 = 0;
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_1371_: u8 = 0;
    let mut v_res_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveOrder_boxed_1369_ = (crate::leanh::lean_unbox(v_preserveOrder_1360_) as u8);
    v___x_10049__boxed_1370_ = (crate::leanh::lean_unbox(v___x_1361_) as u8);
    v_clearAuxDeclsInsteadOfRevert_boxed_1371_ =
        (crate::leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_1363_) as u8);
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
    crate::leanh::lean_dec(v___y_1367_);
    crate::leanh::lean_dec_ref(v___y_1366_);
    crate::leanh::lean_dec(v___y_1365_);
    crate::leanh::lean_dec_ref(v___y_1364_);
    return v_res_1372_;
}
pub unsafe fn l_Lean_MVarId_revert(
    mut v_mvarId_1378_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1379_: *mut crate::leanh::LeanObject,
    mut v_preserveOrder_1380_: u8,
    mut v_clearAuxDeclsInsteadOfRevert_1381_: u8,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    v___x_1387_ = lean_array_get_size(v_fvarIds_1379_);
    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
    if v___x_1389_ == 0 {
        let mut v___x_1390_: u8 = 0;
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1390_ = 1;
        v___x_1391_ = l_Lean_MVarId_revert___closed__1;
        v___x_1392_ = crate::leanh::lean_box((v_preserveOrder_1380_) as usize);
        v___x_1393_ = crate::leanh::lean_box((v___x_1390_) as usize);
        v___x_1394_ = crate::leanh::lean_box((v_clearAuxDeclsInsteadOfRevert_1381_) as usize);
        crate::leanh::lean_inc(v_mvarId_1378_);
        v___f_1395_ = crate::leanh::lean_alloc_closure(
            l_Lean_MVarId_revert___lam__0___boxed as *mut core::ffi::c_void,
            12,
            7,
        );
        crate::leanh::lean_closure_set(v___f_1395_, 0, v_mvarId_1378_);
        crate::leanh::lean_closure_set(v___f_1395_, 1, v___x_1391_);
        crate::leanh::lean_closure_set(v___f_1395_, 2, v_fvarIds_1379_);
        crate::leanh::lean_closure_set(v___f_1395_, 3, v___x_1392_);
        crate::leanh::lean_closure_set(v___f_1395_, 4, v___x_1393_);
        crate::leanh::lean_closure_set(v___f_1395_, 5, v___x_1388_);
        crate::leanh::lean_closure_set(v___f_1395_, 6, v___x_1394_);
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
        let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_fvarIds_1379_);
        v___x_1397_ = l_Lean_MVarId_revert___closed__2;
        v___x_1398_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
        crate::leanh::lean_ctor_set(v___x_1398_, 1, v_mvarId_1378_);
        v___x_1399_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1399_, 0, v___x_1398_);
        return v___x_1399_;
    }
}
pub unsafe fn l_Lean_MVarId_revert___boxed(
    mut v_mvarId_1400_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1401_: *mut crate::leanh::LeanObject,
    mut v_preserveOrder_1402_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveOrder_boxed_1409_: u8 = 0;
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_1410_: u8 = 0;
    let mut v_res_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveOrder_boxed_1409_ = (crate::leanh::lean_unbox(v_preserveOrder_1402_) as u8);
    v_clearAuxDeclsInsteadOfRevert_boxed_1410_ =
        (crate::leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_1403_) as u8);
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
    crate::leanh::lean_dec(v_a_1407_);
    crate::leanh::lean_dec_ref(v_a_1406_);
    crate::leanh::lean_dec(v_a_1405_);
    crate::leanh::lean_dec_ref(v_a_1404_);
    return v_res_1411_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(
    mut v_00_u03b1_1412_: *mut crate::leanh::LeanObject,
    mut v_msg_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1420_: *mut crate::leanh::LeanObject,
    mut v_msg_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(
        v_00_u03b1_1420_,
        v_msg_1421_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
    );
    crate::leanh::lean_dec(v___y_1425_);
    crate::leanh::lean_dec_ref(v___y_1424_);
    crate::leanh::lean_dec(v___y_1423_);
    crate::leanh::lean_dec_ref(v___y_1422_);
    return v_res_1427_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(
    mut v_as_1428_: *mut crate::leanh::LeanObject,
    mut v_i_1429_: usize,
    mut v_stop_1430_: usize,
    mut v_b_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: usize = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1437_ = lean_usize_dec_eq(v_i_1429_, v_stop_1430_);
                if v___x_1437_ == 0 {
                    v___x_1438_ = lean_array_uget_borrowed(v_as_1428_, v_i_1429_);
                    if crate::leanh::lean_obj_tag(v___x_1438_) == 0 {
                        v___y_1433_ = v_b_1431_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1439_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
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
    mut v_as_1442_: *mut crate::leanh::LeanObject,
    mut v_i_1443_: *mut crate::leanh::LeanObject,
    mut v_stop_1444_: *mut crate::leanh::LeanObject,
    mut v_b_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1446_: usize = 0;
    let mut v_stop_boxed_1447_: usize = 0;
    let mut v_res_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1446_ = crate::leanh::lean_unbox_usize(v_i_1443_);
    crate::leanh::lean_dec(v_i_1443_);
    v_stop_boxed_1447_ = crate::leanh::lean_unbox_usize(v_stop_1444_);
    crate::leanh::lean_dec(v_stop_1444_);
    v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_1442_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1445_);
    crate::leanh::lean_dec_ref(v_as_1442_);
    return v_res_1448_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(
    mut v_x_1449_: *mut crate::leanh::LeanObject,
    mut v_x_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1449_) == 0 {
        let mut v_cs_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: u8 = 0;
        v_cs_1451_ = crate::leanh::lean_ctor_get(v_x_1449_, 0);
        v___x_1452_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1456_ = 0usize;
                    v___x_1457_ = lean_usize_of_nat(v___x_1453_);
                    v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1451_, v___x_1456_, v___x_1457_, v_x_1450_);
                    return v___x_1458_;
                }
            } else {
                let mut v___x_1459_: usize = 0;
                let mut v___x_1460_: usize = 0;
                let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1459_ = 0usize;
                v___x_1460_ = lean_usize_of_nat(v___x_1453_);
                v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1451_, v___x_1459_, v___x_1460_, v_x_1450_);
                return v___x_1461_;
            }
        }
    } else {
        let mut v_vs_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: u8 = 0;
        v_vs_1462_ = crate::leanh::lean_ctor_get(v_x_1449_, 0);
        v___x_1463_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1467_ = 0usize;
                    v___x_1468_ = lean_usize_of_nat(v___x_1464_);
                    v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1462_, v___x_1467_, v___x_1468_, v_x_1450_);
                    return v___x_1469_;
                }
            } else {
                let mut v___x_1470_: usize = 0;
                let mut v___x_1471_: usize = 0;
                let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1470_ = 0usize;
                v___x_1471_ = lean_usize_of_nat(v___x_1464_);
                v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1462_, v___x_1470_, v___x_1471_, v_x_1450_);
                return v___x_1472_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(
    mut v_as_1473_: *mut crate::leanh::LeanObject,
    mut v_i_1474_: usize,
    mut v_stop_1475_: usize,
    mut v_b_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_1483_: *mut crate::leanh::LeanObject,
    mut v_i_1484_: *mut crate::leanh::LeanObject,
    mut v_stop_1485_: *mut crate::leanh::LeanObject,
    mut v_b_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1487_: usize = 0;
    let mut v_stop_boxed_1488_: usize = 0;
    let mut v_res_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1487_ = crate::leanh::lean_unbox_usize(v_i_1484_);
    crate::leanh::lean_dec(v_i_1484_);
    v_stop_boxed_1488_ = crate::leanh::lean_unbox_usize(v_stop_1485_);
    crate::leanh::lean_dec(v_stop_1485_);
    v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1486_);
    crate::leanh::lean_dec_ref(v_as_1483_);
    return v_res_1489_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(
    mut v_x_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_1490_, v_x_1491_);
    crate::leanh::lean_dec_ref(v_x_1490_);
    return v_res_1492_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_1493_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(
    mut v_x_1494_: *mut crate::leanh::LeanObject,
    mut v_x_1495_: usize,
    mut v_x_1496_: usize,
    mut v_x_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1494_) == 0 {
        let mut v_cs_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: usize = 0;
        let mut v_j_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: usize = 0;
        let mut v___x_1504_: usize = 0;
        let mut v___x_1505_: usize = 0;
        let mut v___x_1506_: usize = 0;
        let mut v___x_1507_: usize = 0;
        let mut v___x_1508_: usize = 0;
        let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1513_: u8 = 0;
        v_cs_1498_ = crate::leanh::lean_ctor_get(v_x_1494_, 0);
        v___x_1499_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
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
        v___x_1510_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1511_ = lean_nat_add(v_j_1501_, v___x_1510_);
        crate::leanh::lean_dec(v_j_1501_);
        v___x_1512_ = lean_array_get_size(v_cs_1498_);
        v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
        if v___x_1513_ == 0 {
            crate::leanh::lean_dec(v___x_1511_);
            return v___x_1509_;
        } else {
            let mut v___x_1514_: u8 = 0;
            v___x_1514_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
            if v___x_1514_ == 0 {
                if v___x_1513_ == 0 {
                    crate::leanh::lean_dec(v___x_1511_);
                    return v___x_1509_;
                } else {
                    let mut v___x_1515_: usize = 0;
                    let mut v___x_1516_: usize = 0;
                    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1515_ = lean_usize_of_nat(v___x_1511_);
                    crate::leanh::lean_dec(v___x_1511_);
                    v___x_1516_ = lean_usize_of_nat(v___x_1512_);
                    v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1498_, v___x_1515_, v___x_1516_, v___x_1509_);
                    return v___x_1517_;
                }
            } else {
                let mut v___x_1518_: usize = 0;
                let mut v___x_1519_: usize = 0;
                let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1518_ = lean_usize_of_nat(v___x_1511_);
                crate::leanh::lean_dec(v___x_1511_);
                v___x_1519_ = lean_usize_of_nat(v___x_1512_);
                v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_1498_, v___x_1518_, v___x_1519_, v___x_1509_);
                return v___x_1520_;
            }
        }
    } else {
        let mut v_vs_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: u8 = 0;
        v_vs_1521_ = crate::leanh::lean_ctor_get(v_x_1494_, 0);
        v___x_1522_ = lean_usize_to_nat(v_x_1495_);
        v___x_1523_ = lean_array_get_size(v_vs_1521_);
        v___x_1524_ = lean_nat_dec_lt(v___x_1522_, v___x_1523_);
        if v___x_1524_ == 0 {
            crate::leanh::lean_dec(v___x_1522_);
            return v_x_1497_;
        } else {
            let mut v___x_1525_: u8 = 0;
            v___x_1525_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
            if v___x_1525_ == 0 {
                if v___x_1524_ == 0 {
                    crate::leanh::lean_dec(v___x_1522_);
                    return v_x_1497_;
                } else {
                    let mut v___x_1526_: usize = 0;
                    let mut v___x_1527_: usize = 0;
                    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1526_ = lean_usize_of_nat(v___x_1522_);
                    crate::leanh::lean_dec(v___x_1522_);
                    v___x_1527_ = lean_usize_of_nat(v___x_1523_);
                    v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1521_, v___x_1526_, v___x_1527_, v_x_1497_);
                    return v___x_1528_;
                }
            } else {
                let mut v___x_1529_: usize = 0;
                let mut v___x_1530_: usize = 0;
                let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1529_ = lean_usize_of_nat(v___x_1522_);
                crate::leanh::lean_dec(v___x_1522_);
                v___x_1530_ = lean_usize_of_nat(v___x_1523_);
                v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_1521_, v___x_1529_, v___x_1530_, v_x_1497_);
                return v___x_1531_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(
    mut v_x_1532_: *mut crate::leanh::LeanObject,
    mut v_x_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_x_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1742__boxed_1536_: usize = 0;
    let mut v_x_1743__boxed_1537_: usize = 0;
    let mut v_res_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1742__boxed_1536_ = crate::leanh::lean_unbox_usize(v_x_1533_);
    crate::leanh::lean_dec(v_x_1533_);
    v_x_1743__boxed_1537_ = crate::leanh::lean_unbox_usize(v_x_1534_);
    crate::leanh::lean_dec(v_x_1534_);
    v_res_1538_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_1532_, v_x_1742__boxed_1536_, v_x_1743__boxed_1537_, v_x_1535_);
    crate::leanh::lean_dec_ref(v_x_1532_);
    return v_res_1538_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(
    mut v_t_1539_: *mut crate::leanh::LeanObject,
    mut v_init_1540_: *mut crate::leanh::LeanObject,
    mut v_start_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    v___x_1542_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1543_ = lean_nat_dec_eq(v_start_1541_, v___x_1542_);
    if v___x_1543_ == 0 {
        let mut v_root_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_1546_: usize = 0;
        let mut v_tailOff_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: u8 = 0;
        v_root_1544_ = crate::leanh::lean_ctor_get(v_t_1539_, 0);
        v_tail_1545_ = crate::leanh::lean_ctor_get(v_t_1539_, 1);
        v_shift_1546_ = crate::leanh::lean_ctor_get_usize(v_t_1539_, 4);
        v_tailOff_1547_ = crate::leanh::lean_ctor_get(v_t_1539_, 3);
        v___x_1548_ = lean_nat_dec_le(v_tailOff_1547_, v_start_1541_);
        if v___x_1548_ == 0 {
            let mut v___x_1549_: usize = 0;
            let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                        let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1554_ = 0usize;
                        v___x_1555_ = lean_usize_of_nat(v___x_1551_);
                        v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1554_, v___x_1555_, v___x_1550_);
                        return v___x_1556_;
                    }
                } else {
                    let mut v___x_1557_: usize = 0;
                    let mut v___x_1558_: usize = 0;
                    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1557_ = 0usize;
                    v___x_1558_ = lean_usize_of_nat(v___x_1551_);
                    v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1557_, v___x_1558_, v___x_1550_);
                    return v___x_1559_;
                }
            }
        } else {
            let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1562_: u8 = 0;
            v___x_1560_ = lean_nat_sub(v_start_1541_, v_tailOff_1547_);
            v___x_1561_ = lean_array_get_size(v_tail_1545_);
            v___x_1562_ = lean_nat_dec_lt(v___x_1560_, v___x_1561_);
            if v___x_1562_ == 0 {
                crate::leanh::lean_dec(v___x_1560_);
                return v_init_1540_;
            } else {
                let mut v___x_1563_: u8 = 0;
                v___x_1563_ = lean_nat_dec_le(v___x_1561_, v___x_1561_);
                if v___x_1563_ == 0 {
                    if v___x_1562_ == 0 {
                        crate::leanh::lean_dec(v___x_1560_);
                        return v_init_1540_;
                    } else {
                        let mut v___x_1564_: usize = 0;
                        let mut v___x_1565_: usize = 0;
                        let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1564_ = lean_usize_of_nat(v___x_1560_);
                        crate::leanh::lean_dec(v___x_1560_);
                        v___x_1565_ = lean_usize_of_nat(v___x_1561_);
                        v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1564_, v___x_1565_, v_init_1540_);
                        return v___x_1566_;
                    }
                } else {
                    let mut v___x_1567_: usize = 0;
                    let mut v___x_1568_: usize = 0;
                    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1567_ = lean_usize_of_nat(v___x_1560_);
                    crate::leanh::lean_dec(v___x_1560_);
                    v___x_1568_ = lean_usize_of_nat(v___x_1561_);
                    v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1545_, v___x_1567_, v___x_1568_, v_init_1540_);
                    return v___x_1569_;
                }
            }
        }
    } else {
        let mut v_root_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: u8 = 0;
        v_root_1570_ = crate::leanh::lean_ctor_get(v_t_1539_, 0);
        v_tail_1571_ = crate::leanh::lean_ctor_get(v_t_1539_, 1);
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
                    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1576_ = 0usize;
                    v___x_1577_ = lean_usize_of_nat(v___x_1573_);
                    v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1571_, v___x_1576_, v___x_1577_, v___x_1572_);
                    return v___x_1578_;
                }
            } else {
                let mut v___x_1579_: usize = 0;
                let mut v___x_1580_: usize = 0;
                let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1579_ = 0usize;
                v___x_1580_ = lean_usize_of_nat(v___x_1573_);
                v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_1571_, v___x_1579_, v___x_1580_, v___x_1572_);
                return v___x_1581_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(
    mut v_t_1582_: *mut crate::leanh::LeanObject,
    mut v_init_1583_: *mut crate::leanh::LeanObject,
    mut v_start_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_1582_, v_init_1583_, v_start_1584_);
    crate::leanh::lean_dec(v_start_1584_);
    crate::leanh::lean_dec_ref(v_t_1582_);
    return v_res_1585_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
    mut v_lctx_1586_: *mut crate::leanh::LeanObject,
    mut v_init_1587_: *mut crate::leanh::LeanObject,
    mut v_start_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_1589_ = crate::leanh::lean_ctor_get(v_lctx_1586_, 1);
    v___x_1590_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_1589_, v_init_1587_, v_start_1588_);
    return v___x_1590_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(
    mut v_lctx_1591_: *mut crate::leanh::LeanObject,
    mut v_init_1592_: *mut crate::leanh::LeanObject,
    mut v_start_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
        v_lctx_1591_,
        v_init_1592_,
        v_start_1593_,
    );
    crate::leanh::lean_dec(v_start_1593_);
    crate::leanh::lean_dec_ref(v_lctx_1591_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_MVarId_revertAfter___lam__0(
    mut v_fvarId_1595_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_1602_) == 0 {
                    v_a_1603_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                    crate::leanh::lean_inc(v_a_1603_);
                    crate::leanh::lean_dec_ref_known(v___x_1602_, 1);
                    v_lctx_1604_ = crate::leanh::lean_ctor_get(v___y_1597_, 2);
                    v___x_1605_ = l_Lean_MVarId_revert___closed__2;
                    v___x_1606_ = l_Lean_LocalDecl_index(v_a_1603_);
                    crate::leanh::lean_dec(v_a_1603_);
                    v___x_1607_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1608_ = lean_nat_add(v___x_1606_, v___x_1607_);
                    crate::leanh::lean_dec(v___x_1606_);
                    v___x_1609_ =
                        l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
                            v_lctx_1604_,
                            v___x_1605_,
                            v___x_1608_,
                        );
                    crate::leanh::lean_dec(v___x_1608_);
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
                    crate::leanh::lean_dec(v_mvarId_1596_);
                    v_a_1612_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1619_ = (!crate::leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1614_ = v___x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1619_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1612_);
                        crate::leanh::lean_dec(v___x_1602_);
                        v___x_1614_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
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
    mut v_fvarId_1620_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Lean_MVarId_revertAfter___lam__0(
        v_fvarId_1620_,
        v_mvarId_1621_,
        v___y_1622_,
        v___y_1623_,
        v___y_1624_,
        v___y_1625_,
    );
    crate::leanh::lean_dec(v___y_1625_);
    crate::leanh::lean_dec_ref(v___y_1624_);
    crate::leanh::lean_dec(v___y_1623_);
    crate::leanh::lean_dec_ref(v___y_1622_);
    return v_res_1627_;
}
pub unsafe fn l_Lean_MVarId_revertAfter(
    mut v_mvarId_1628_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_1628_);
    v___f_1635_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_revertAfter___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1635_, 0, v_fvarId_1629_);
    crate::leanh::lean_closure_set(v___f_1635_, 1, v_mvarId_1628_);
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
    mut v_mvarId_1637_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l_Lean_MVarId_revertAfter(
        v_mvarId_1637_,
        v_fvarId_1638_,
        v_a_1639_,
        v_a_1640_,
        v_a_1641_,
        v_a_1642_,
    );
    crate::leanh::lean_dec(v_a_1642_);
    crate::leanh::lean_dec_ref(v_a_1641_);
    crate::leanh::lean_dec(v_a_1640_);
    crate::leanh::lean_dec_ref(v_a_1639_);
    return v_res_1644_;
}
pub unsafe fn l_Lean_MVarId_revertFrom___lam__0(
    mut v_fvarId_1645_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_1652_) == 0 {
                    v_a_1653_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                    crate::leanh::lean_inc(v_a_1653_);
                    crate::leanh::lean_dec_ref_known(v___x_1652_, 1);
                    v_lctx_1654_ = crate::leanh::lean_ctor_get(v___y_1647_, 2);
                    v___x_1655_ = l_Lean_MVarId_revert___closed__2;
                    v___x_1656_ = l_Lean_LocalDecl_index(v_a_1653_);
                    crate::leanh::lean_dec(v_a_1653_);
                    v___x_1657_ =
                        l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(
                            v_lctx_1654_,
                            v___x_1655_,
                            v___x_1656_,
                        );
                    crate::leanh::lean_dec(v___x_1656_);
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
                    crate::leanh::lean_dec(v_mvarId_1646_);
                    v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                    v_isSharedCheck_1667_ = (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1652_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1660_);
                        crate::leanh::lean_dec(v___x_1652_);
                        v___x_1662_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
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
    mut v_fvarId_1668_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Lean_MVarId_revertFrom___lam__0(
        v_fvarId_1668_,
        v_mvarId_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
    );
    crate::leanh::lean_dec(v___y_1673_);
    crate::leanh::lean_dec_ref(v___y_1672_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v___y_1670_);
    return v_res_1675_;
}
pub unsafe fn l_Lean_MVarId_revertFrom(
    mut v_mvarId_1676_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v_a_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_1676_);
    v___f_1683_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_revertFrom___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1683_, 0, v_fvarId_1677_);
    crate::leanh::lean_closure_set(v___f_1683_, 1, v_mvarId_1676_);
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
    mut v_mvarId_1685_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_MVarId_revertFrom(
        v_mvarId_1685_,
        v_fvarId_1686_,
        v_a_1687_,
        v_a_1688_,
        v_a_1689_,
        v_a_1690_,
    );
    crate::leanh::lean_dec(v_a_1690_);
    crate::leanh::lean_dec_ref(v_a_1689_);
    crate::leanh::lean_dec(v_a_1688_);
    crate::leanh::lean_dec_ref(v_a_1687_);
    return v_res_1692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Revert(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Revert(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Revert(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Revert(builtin);
}
