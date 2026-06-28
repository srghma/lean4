// Lean compiler output
// Module: Lean.Compiler.LCNF.Toposort
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.InitAttr
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_getBuiltinInitFnNameFor_x3f,
    lean_get_init_fn_name_for, runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_Phase_toPurity,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_8, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toposortPass___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 111, 112, 111, 115, 111, 114, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_toposortPass___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toposortPass___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_toposortPass___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_toposortPass___closed__0_value)
                as *mut LeanObject,
            17728408230735906812 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_toposortPass___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toposortPass___closed__1_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_toposortPass___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_toposortPass___closed__2: u8 = 0;
static mut l_Lean_Compiler_LCNF_toposortPass___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_toposortPass___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_toposortPass___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_toposortPass___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_toposortPass: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(
    mut v_f_849_: *mut LeanObject,
    mut v_v_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_unused_868_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_850_) == 0 {
                    v_code_858_ = lean_ctor_get(v_v_850_, 0);
                    lean_inc_ref(v_code_858_);
                    lean_dec_ref_known(v_v_850_, 1);
                    lean_inc(v___y_856_);
                    lean_inc_ref(v___y_855_);
                    lean_inc(v___y_854_);
                    lean_inc_ref(v___y_853_);
                    lean_inc(v___y_852_);
                    lean_inc_ref(v___y_851_);
                    v___x_859_ = lean_apply_8(
                        v_f_849_,
                        v_code_858_,
                        v___y_851_,
                        v___y_852_,
                        v___y_853_,
                        v___y_854_,
                        v___y_855_,
                        v___y_856_,
                        lean_box(0),
                    );
                    return v___x_859_;
                } else {
                    lean_dec_ref(v_f_849_);
                    v_isSharedCheck_867_ = (!lean_is_exclusive(v_v_850_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v_unused_868_ = lean_ctor_get(v_v_850_, 0);
                        lean_dec(v_unused_868_);
                        v___x_861_ = v_v_850_;
                        v_isShared_862_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_850_);
                        v___x_861_ = lean_box(0);
                        v_isShared_862_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_863_ = lean_box(0);
                if v_isShared_862_ == 0 {
                    lean_ctor_set_tag(v___x_861_, 0);
                    lean_ctor_set(v___x_861_, 0, v___x_863_);
                    v___x_865_ = v___x_861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
                    v___x_865_ = v_reuseFailAlloc_866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg___boxed(
    mut v_f_869_: *mut LeanObject,
    mut v_v_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_878_: *mut LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_869_, v_v_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
    lean_dec(v___y_876_);
    lean_dec_ref(v___y_875_);
    lean_dec(v___y_874_);
    lean_dec_ref(v___y_873_);
    lean_dec(v___y_872_);
    lean_dec_ref(v___y_871_);
    return v_res_878_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(
    mut v_a_879_: *mut LeanObject,
    mut v_x_880_: *mut LeanObject,
) -> u8 {
    let mut v___x_881_: u8 = 0;
    let mut v_key_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_880_) == 0 {
                    v___x_881_ = 0;
                    return v___x_881_;
                } else {
                    v_key_882_ = lean_ctor_get(v_x_880_, 0);
                    v_tail_883_ = lean_ctor_get(v_x_880_, 2);
                    v___x_884_ = lean_name_eq(v_key_882_, v_a_879_);
                    if v___x_884_ == 0 {
                        v_x_880_ = v_tail_883_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_884_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg___boxed(
    mut v_a_886_: *mut LeanObject,
    mut v_x_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_888_: u8 = 0;
    let mut v_r_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_886_, v_x_887_);
    lean_dec(v_x_887_);
    lean_dec(v_a_886_);
    v_r_889_ = lean_box((v_res_888_) as usize);
    return v_r_889_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0()
-> u64 {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u64 = 0;
    v___x_890_ = lean_unsigned_to_nat(1723);
    v___x_891_ = lean_uint64_of_nat(v___x_890_);
    return v___x_891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(
    mut v_x_892_: *mut LeanObject,
    mut v_x_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_902_: u64 = 0;
    let mut v___x_903_: u64 = 0;
    let mut v___x_904_: u64 = 0;
    let mut v_fold_905_: u64 = 0;
    let mut v___x_906_: u64 = 0;
    let mut v___x_907_: u64 = 0;
    let mut v___x_908_: u64 = 0;
    let mut v___x_909_: usize = 0;
    let mut v___x_910_: usize = 0;
    let mut v___x_911_: usize = 0;
    let mut v___x_912_: usize = 0;
    let mut v___x_913_: usize = 0;
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u64 = 0;
    let mut v_hash_921_: u64 = 0;
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_893_) == 0 {
                    return v_x_892_;
                } else {
                    v_key_894_ = lean_ctor_get(v_x_893_, 0);
                    v_value_895_ = lean_ctor_get(v_x_893_, 1);
                    v_tail_896_ = lean_ctor_get(v_x_893_, 2);
                    v_isSharedCheck_922_ = (!lean_is_exclusive(v_x_893_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_898_ = v_x_893_;
                        v_isShared_899_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_896_);
                        lean_inc(v_value_895_);
                        lean_inc(v_key_894_);
                        lean_dec(v_x_893_);
                        v___x_898_ = lean_box(0);
                        v_isShared_899_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_900_ = lean_array_get_size(v_x_892_);
                if lean_obj_tag(v_key_894_) == 0 {
                    v___x_920_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_902_ = v___x_920_;
                    state = 2;
                    continue;
                } else {
                    v_hash_921_ = lean_ctor_get_uint64(
                        v_key_894_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_902_ = v_hash_921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_903_ = 32u64;
                v___x_904_ = lean_uint64_shift_right(v___y_902_, v___x_903_);
                v_fold_905_ = lean_uint64_xor(v___y_902_, v___x_904_);
                v___x_906_ = 16u64;
                v___x_907_ = lean_uint64_shift_right(v_fold_905_, v___x_906_);
                v___x_908_ = lean_uint64_xor(v_fold_905_, v___x_907_);
                v___x_909_ = lean_uint64_to_usize(v___x_908_);
                v___x_910_ = lean_usize_of_nat(v___x_900_);
                v___x_911_ = 1usize;
                v___x_912_ = lean_usize_sub(v___x_910_, v___x_911_);
                v___x_913_ = lean_usize_land(v___x_909_, v___x_912_);
                v___x_914_ = lean_array_uget_borrowed(v_x_892_, v___x_913_);
                lean_inc(v___x_914_);
                if v_isShared_899_ == 0 {
                    lean_ctor_set(v___x_898_, 2, v___x_914_);
                    v___x_916_ = v___x_898_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_919_, 0, v_key_894_);
                    lean_ctor_set(v_reuseFailAlloc_919_, 1, v_value_895_);
                    lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_914_);
                    v___x_916_ = v_reuseFailAlloc_919_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_917_ = lean_array_uset(v_x_892_, v___x_913_, v___x_916_);
                v_x_892_ = v___x_917_;
                v_x_893_ = v_tail_896_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(
    mut v_i_923_: *mut LeanObject,
    mut v_source_924_: *mut LeanObject,
    mut v_target_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u8 = 0;
    let mut v_es_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_926_ = lean_array_get_size(v_source_924_);
                v___x_927_ = lean_nat_dec_lt(v_i_923_, v___x_926_);
                if v___x_927_ == 0 {
                    lean_dec_ref(v_source_924_);
                    lean_dec(v_i_923_);
                    return v_target_925_;
                } else {
                    v_es_928_ = lean_array_fget(v_source_924_, v_i_923_);
                    v___x_929_ = lean_box(0);
                    v_source_930_ = lean_array_fset(v_source_924_, v_i_923_, v___x_929_);
                    v_target_931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_target_925_, v_es_928_);
                    v___x_932_ = lean_unsigned_to_nat(1);
                    v___x_933_ = lean_nat_add(v_i_923_, v___x_932_);
                    lean_dec(v_i_923_);
                    v_i_923_ = v___x_933_;
                    v_source_924_ = v_source_930_;
                    v_target_925_ = v_target_931_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(
    mut v_data_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___x_936_ = lean_array_get_size(v_data_935_);
    v___x_937_ = lean_unsigned_to_nat(2);
    v_nbuckets_938_ = lean_nat_mul(v___x_936_, v___x_937_);
    v___x_939_ = lean_unsigned_to_nat(0);
    v___x_940_ = lean_box(0);
    v___x_941_ = lean_mk_array(v_nbuckets_938_, v___x_940_);
    v___x_942_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v___x_939_, v_data_935_, v___x_941_);
    return v___x_942_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(
    mut v_m_943_: *mut LeanObject,
    mut v_a_944_: *mut LeanObject,
    mut v_b_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_950_: u64 = 0;
    let mut v___x_951_: u64 = 0;
    let mut v___x_952_: u64 = 0;
    let mut v_fold_953_: u64 = 0;
    let mut v___x_954_: u64 = 0;
    let mut v___x_955_: u64 = 0;
    let mut v___x_956_: u64 = 0;
    let mut v___x_957_: usize = 0;
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: usize = 0;
    let mut v_bkt_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v_val_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut v_unused_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: u64 = 0;
    let mut v_hash_988_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_946_ = lean_ctor_get(v_m_943_, 0);
                v_buckets_947_ = lean_ctor_get(v_m_943_, 1);
                v___x_948_ = lean_array_get_size(v_buckets_947_);
                if lean_obj_tag(v_a_944_) == 0 {
                    v___x_987_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_950_ = v___x_987_;
                    state = 1;
                    continue;
                } else {
                    v_hash_988_ = lean_ctor_get_uint64(
                        v_a_944_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_950_ = v_hash_988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_951_ = 32u64;
                v___x_952_ = lean_uint64_shift_right(v___y_950_, v___x_951_);
                v_fold_953_ = lean_uint64_xor(v___y_950_, v___x_952_);
                v___x_954_ = 16u64;
                v___x_955_ = lean_uint64_shift_right(v_fold_953_, v___x_954_);
                v___x_956_ = lean_uint64_xor(v_fold_953_, v___x_955_);
                v___x_957_ = lean_uint64_to_usize(v___x_956_);
                v___x_958_ = lean_usize_of_nat(v___x_948_);
                v___x_959_ = 1usize;
                v___x_960_ = lean_usize_sub(v___x_958_, v___x_959_);
                v___x_961_ = lean_usize_land(v___x_957_, v___x_960_);
                v_bkt_962_ = lean_array_uget_borrowed(v_buckets_947_, v___x_961_);
                v___x_963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_944_, v_bkt_962_);
                if v___x_963_ == 0 {
                    lean_inc_ref(v_buckets_947_);
                    lean_inc(v_size_946_);
                    v_isSharedCheck_984_ = (!lean_is_exclusive(v_m_943_)) as u8;
                    if v_isSharedCheck_984_ == 0 {
                        v_unused_985_ = lean_ctor_get(v_m_943_, 1);
                        lean_dec(v_unused_985_);
                        v_unused_986_ = lean_ctor_get(v_m_943_, 0);
                        lean_dec(v_unused_986_);
                        v___x_965_ = v_m_943_;
                        v_isShared_966_ = v_isSharedCheck_984_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_943_);
                        v___x_965_ = lean_box(0);
                        v_isShared_966_ = v_isSharedCheck_984_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_945_);
                    lean_dec(v_a_944_);
                    return v_m_943_;
                }
            }
            2 => {
                v___x_967_ = lean_unsigned_to_nat(1);
                v_size_x27_968_ = lean_nat_add(v_size_946_, v___x_967_);
                lean_dec(v_size_946_);
                lean_inc(v_bkt_962_);
                v___x_969_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_969_, 0, v_a_944_);
                lean_ctor_set(v___x_969_, 1, v_b_945_);
                lean_ctor_set(v___x_969_, 2, v_bkt_962_);
                v_buckets_x27_970_ = lean_array_uset(v_buckets_947_, v___x_961_, v___x_969_);
                v___x_971_ = lean_unsigned_to_nat(4);
                v___x_972_ = lean_nat_mul(v_size_x27_968_, v___x_971_);
                v___x_973_ = lean_unsigned_to_nat(3);
                v___x_974_ = lean_nat_div(v___x_972_, v___x_973_);
                lean_dec(v___x_972_);
                v___x_975_ = lean_array_get_size(v_buckets_x27_970_);
                v___x_976_ = lean_nat_dec_le(v___x_974_, v___x_975_);
                lean_dec(v___x_974_);
                if v___x_976_ == 0 {
                    v_val_977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_970_);
                    if v_isShared_966_ == 0 {
                        lean_ctor_set(v___x_965_, 1, v_val_977_);
                        lean_ctor_set(v___x_965_, 0, v_size_x27_968_);
                        v___x_979_ = v___x_965_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_980_, 0, v_size_x27_968_);
                        lean_ctor_set(v_reuseFailAlloc_980_, 1, v_val_977_);
                        v___x_979_ = v_reuseFailAlloc_980_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_966_ == 0 {
                        lean_ctor_set(v___x_965_, 1, v_buckets_x27_970_);
                        lean_ctor_set(v___x_965_, 0, v_size_x27_968_);
                        v___x_982_ = v___x_965_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_983_, 0, v_size_x27_968_);
                        lean_ctor_set(v_reuseFailAlloc_983_, 1, v_buckets_x27_970_);
                        v___x_982_ = v_reuseFailAlloc_983_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_979_;
            }
            4 => {
                return v___x_982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(
    mut v_m_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_994_: u64 = 0;
    let mut v___x_995_: u64 = 0;
    let mut v___x_996_: u64 = 0;
    let mut v_fold_997_: u64 = 0;
    let mut v___x_998_: u64 = 0;
    let mut v___x_999_: u64 = 0;
    let mut v___x_1000_: u64 = 0;
    let mut v___x_1001_: usize = 0;
    let mut v___x_1002_: usize = 0;
    let mut v___x_1003_: usize = 0;
    let mut v___x_1004_: usize = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: u64 = 0;
    let mut v_hash_1009_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_991_ = lean_ctor_get(v_m_989_, 1);
                v___x_992_ = lean_array_get_size(v_buckets_991_);
                if lean_obj_tag(v_a_990_) == 0 {
                    v___x_1008_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_994_ = v___x_1008_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1009_ = lean_ctor_get_uint64(
                        v_a_990_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_994_ = v_hash_1009_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_995_ = 32u64;
                v___x_996_ = lean_uint64_shift_right(v___y_994_, v___x_995_);
                v_fold_997_ = lean_uint64_xor(v___y_994_, v___x_996_);
                v___x_998_ = 16u64;
                v___x_999_ = lean_uint64_shift_right(v_fold_997_, v___x_998_);
                v___x_1000_ = lean_uint64_xor(v_fold_997_, v___x_999_);
                v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
                v___x_1002_ = lean_usize_of_nat(v___x_992_);
                v___x_1003_ = 1usize;
                v___x_1004_ = lean_usize_sub(v___x_1002_, v___x_1003_);
                v___x_1005_ = lean_usize_land(v___x_1001_, v___x_1004_);
                v___x_1006_ = lean_array_uget_borrowed(v_buckets_991_, v___x_1005_);
                v___x_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_990_, v___x_1006_);
                return v___x_1007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg___boxed(
    mut v_m_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1012_: u8 = 0;
    let mut v_r_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1012_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_1010_, v_a_1011_);
    lean_dec(v_a_1011_);
    lean_dec_ref(v_m_1010_);
    v_r_1013_ = lean_box((v_res_1012_) as usize);
    return v_r_1013_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(
    mut v_a_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1015_) == 0 {
                    v___x_1016_ = lean_box(0);
                    return v___x_1016_;
                } else {
                    v_key_1017_ = lean_ctor_get(v_x_1015_, 0);
                    v_value_1018_ = lean_ctor_get(v_x_1015_, 1);
                    v_tail_1019_ = lean_ctor_get(v_x_1015_, 2);
                    v___x_1020_ = lean_name_eq(v_key_1017_, v_a_1014_);
                    if v___x_1020_ == 0 {
                        v_x_1015_ = v_tail_1019_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1018_);
                        v___x_1022_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1022_, 0, v_value_1018_);
                        return v___x_1022_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg___boxed(
    mut v_a_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_1023_, v_x_1024_);
    lean_dec(v_x_1024_);
    lean_dec(v_a_1023_);
    return v_res_1025_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(
    mut v_m_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: u64 = 0;
    let mut v___x_1032_: u64 = 0;
    let mut v___x_1033_: u64 = 0;
    let mut v_fold_1034_: u64 = 0;
    let mut v___x_1035_: u64 = 0;
    let mut v___x_1036_: u64 = 0;
    let mut v___x_1037_: u64 = 0;
    let mut v___x_1038_: usize = 0;
    let mut v___x_1039_: usize = 0;
    let mut v___x_1040_: usize = 0;
    let mut v___x_1041_: usize = 0;
    let mut v___x_1042_: usize = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u64 = 0;
    let mut v_hash_1046_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1028_ = lean_ctor_get(v_m_1026_, 1);
                v___x_1029_ = lean_array_get_size(v_buckets_1028_);
                if lean_obj_tag(v_a_1027_) == 0 {
                    v___x_1045_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_1031_ = v___x_1045_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1046_ = lean_ctor_get_uint64(
                        v_a_1027_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1031_ = v_hash_1046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1032_ = 32u64;
                v___x_1033_ = lean_uint64_shift_right(v___y_1031_, v___x_1032_);
                v_fold_1034_ = lean_uint64_xor(v___y_1031_, v___x_1033_);
                v___x_1035_ = 16u64;
                v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
                v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
                v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
                v___x_1039_ = lean_usize_of_nat(v___x_1029_);
                v___x_1040_ = 1usize;
                v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
                v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
                v___x_1043_ = lean_array_uget_borrowed(v_buckets_1028_, v___x_1042_);
                v___x_1044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_1027_, v___x_1043_);
                return v___x_1044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg___boxed(
    mut v_m_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1049_: *mut LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_1047_, v_a_1048_);
    lean_dec(v_a_1048_);
    lean_dec_ref(v_m_1047_);
    return v_res_1049_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed(
    mut v_pu_1050_: *mut LeanObject,
    mut v_x_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1059_: u8 = 0;
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1059_ = (lean_unbox(v_pu_1050_) as u8);
    v_res_1060_ =
        l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(
            v_pu_boxed_1059_,
            v_x_1051_,
            v___y_1052_,
            v___y_1053_,
            v___y_1054_,
            v___y_1055_,
            v___y_1056_,
            v___y_1057_,
        );
    lean_dec(v___y_1057_);
    lean_dec_ref(v___y_1056_);
    lean_dec(v___y_1055_);
    lean_dec_ref(v___y_1054_);
    lean_dec(v___y_1053_);
    lean_dec_ref(v___y_1052_);
    lean_dec_ref(v_x_1051_);
    return v_res_1060_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(
    mut v_pu_1061_: u8,
    mut v_decl_1062_: *mut LeanObject,
    mut v_a_1063_: *mut LeanObject,
    mut v_a_1064_: *mut LeanObject,
    mut v_a_1065_: *mut LeanObject,
    mut v_a_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1077_: u8 = 0;
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1086_ = lean_st_ref_get(v_a_1064_);
                v_toSignature_1087_ = lean_ctor_get(v_decl_1062_, 0);
                v_seen_1088_ = lean_ctor_get(v___x_1086_, 0);
                lean_inc_ref(v_seen_1088_);
                lean_dec(v___x_1086_);
                v_value_1089_ = lean_ctor_get(v_decl_1062_, 1);
                v_name_1090_ = lean_ctor_get(v_toSignature_1087_, 0);
                v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_seen_1088_, v_name_1090_);
                lean_dec_ref(v_seen_1088_);
                if v___x_1091_ == 0 {
                    v___x_1092_ = lean_st_ref_get(v_a_1068_);
                    v___x_1093_ = lean_st_ref_take(v_a_1064_);
                    v_seen_1094_ = lean_ctor_get(v___x_1093_, 0);
                    v_order_1095_ = lean_ctor_get(v___x_1093_, 1);
                    v_isSharedCheck_1115_ = (!lean_is_exclusive(v___x_1093_)) as u8;
                    if v_isSharedCheck_1115_ == 0 {
                        v___x_1097_ = v___x_1093_;
                        v_isShared_1098_ = v_isSharedCheck_1115_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_order_1095_);
                        lean_inc(v_seen_1094_);
                        lean_dec(v___x_1093_);
                        v___x_1097_ = lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1115_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_1062_);
                    v___x_1116_ = lean_box(0);
                    v___x_1117_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1117_, 0, v___x_1116_);
                    return v___x_1117_;
                }
            }
            1 => {
                v___x_1072_ = lean_st_ref_take(v___y_1071_);
                v_seen_1073_ = lean_ctor_get(v___x_1072_, 0);
                v_order_1074_ = lean_ctor_get(v___x_1072_, 1);
                v_isSharedCheck_1085_ = (!lean_is_exclusive(v___x_1072_)) as u8;
                if v_isSharedCheck_1085_ == 0 {
                    v___x_1076_ = v___x_1072_;
                    v_isShared_1077_ = v_isSharedCheck_1085_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_order_1074_);
                    lean_inc(v_seen_1073_);
                    lean_dec(v___x_1072_);
                    v___x_1076_ = lean_box(0);
                    v_isShared_1077_ = v_isSharedCheck_1085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1078_ = lean_array_push(v_order_1074_, v_decl_1062_);
                if v_isShared_1077_ == 0 {
                    lean_ctor_set(v___x_1076_, 1, v___x_1078_);
                    v___x_1080_ = v___x_1076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_seen_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1078_);
                    v___x_1080_ = v_reuseFailAlloc_1084_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1081_ = lean_st_ref_set(v___y_1071_, v___x_1080_);
                v___x_1082_ = lean_box(0);
                v___x_1083_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1083_, 0, v___x_1082_);
                return v___x_1083_;
            }
            4 => {
                v___x_1099_ = lean_box(0);
                lean_inc(v_name_1090_);
                v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_seen_1094_, v_name_1090_, v___x_1099_);
                if v_isShared_1098_ == 0 {
                    lean_ctor_set(v___x_1097_, 0, v___x_1100_);
                    v___x_1102_ = v___x_1097_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1100_);
                    lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_order_1095_);
                    v___x_1102_ = v_reuseFailAlloc_1114_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1103_ = lean_st_ref_set(v_a_1064_, v___x_1102_);
                v___x_1104_ = lean_box((v_pu_1061_) as usize);
                v___f_1105_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v___f_1105_, 0, v___x_1104_);
                lean_inc_ref(v_value_1089_);
                v___x_1106_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v___f_1105_, v_value_1089_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
                if lean_obj_tag(v___x_1106_) == 0 {
                    lean_dec_ref_known(v___x_1106_, 1);
                    v_env_1111_ = lean_ctor_get(v___x_1092_, 0);
                    lean_inc_ref_n(v_env_1111_, 2);
                    lean_dec(v___x_1092_);
                    lean_inc(v_name_1090_);
                    v___x_1112_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_1111_, v_name_1090_);
                    if lean_obj_tag(v___x_1112_) == 0 {
                        lean_inc(v_name_1090_);
                        v___x_1113_ = lean_get_init_fn_name_for(v_env_1111_, v_name_1090_);
                        v___y_1108_ = v___x_1113_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec_ref(v_env_1111_);
                        v___y_1108_ = v___x_1112_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1092_);
                    lean_dec_ref(v_decl_1062_);
                    return v___x_1106_;
                }
            }
            6 => {
                if lean_obj_tag(v___y_1108_) == 1 {
                    v_val_1109_ = lean_ctor_get(v___y_1108_, 0);
                    lean_inc(v_val_1109_);
                    lean_dec_ref_known(v___y_1108_, 1);
                    v___x_1110_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_1061_, v_val_1109_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
                    lean_dec(v_val_1109_);
                    if lean_obj_tag(v___x_1110_) == 0 {
                        lean_dec_ref_known(v___x_1110_, 1);
                        v___y_1071_ = v_a_1064_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_decl_1062_);
                        return v___x_1110_;
                    }
                } else {
                    lean_dec(v___y_1108_);
                    v___y_1071_ = v_a_1064_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(
    mut v_pu_1118_: u8,
    mut v_declName_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_a_1120_, v_declName_1119_);
    if lean_obj_tag(v___x_1127_) == 1 {
        let mut v_val_1128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
        v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
        lean_inc(v_val_1128_);
        lean_dec_ref_known(v___x_1127_, 1);
        v___x_1129_ =
            l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(
                v_pu_1118_,
                v_val_1128_,
                v_a_1120_,
                v_a_1121_,
                v_a_1122_,
                v_a_1123_,
                v_a_1124_,
                v_a_1125_,
            );
        return v___x_1129_;
    } else {
        let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1127_);
        v___x_1130_ = lean_box(0);
        v___x_1131_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1131_, 0, v___x_1130_);
        return v___x_1131_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(
    mut v_pu_1132_: u8,
    mut v_code_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
    mut v_a_1138_: *mut LeanObject,
    mut v_a_1139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_code_1133_) == 0 {
        let mut v_decl_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1142_: *mut LeanObject = core::ptr::null_mut();
        v_decl_1141_ = lean_ctor_get(v_code_1133_, 0);
        v_value_1142_ = lean_ctor_get(v_decl_1141_, 3);
        match lean_obj_tag(v_value_1142_) {
            3 => {
                let mut v_declName_1143_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
                v_declName_1143_ = lean_ctor_get(v_value_1142_, 0);
                v___x_1144_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_1132_, v_declName_1143_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
                return v___x_1144_;
            }
            9 => {
                let mut v_fn_1145_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
                v_fn_1145_ = lean_ctor_get(v_value_1142_, 0);
                v___x_1146_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_1132_, v_fn_1145_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
                return v___x_1146_;
            }
            10 => {
                let mut v_fn_1147_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
                v_fn_1147_ = lean_ctor_get(v_value_1142_, 0);
                v___x_1148_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(v_pu_1132_, v_fn_1147_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
                return v___x_1148_;
            }
            _ => {
                let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
                v___x_1149_ = lean_box(0);
                v___x_1150_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1150_, 0, v___x_1149_);
                return v___x_1150_;
            }
        }
    } else {
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
        v___x_1151_ = lean_box(0);
        v___x_1152_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1152_, 0, v___x_1151_);
        return v___x_1152_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(
    mut v_pu_1153_: u8,
    mut v_pu_1154_: u8,
    mut v_as_1155_: *mut LeanObject,
    mut v_i_1156_: usize,
    mut v_stop_1157_: usize,
    mut v_b_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
    mut v___y_1160_: *mut LeanObject,
    mut v___y_1161_: *mut LeanObject,
    mut v___y_1162_: *mut LeanObject,
    mut v___y_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1172_ = lean_usize_dec_eq(v_i_1156_, v_stop_1157_);
                if v___x_1172_ == 0 {
                    v___x_1173_ = lean_array_uget_borrowed(v_as_1155_, v_i_1156_);
                    match lean_obj_tag(v___x_1173_) {
                        0 => {
                            v_code_1174_ = lean_ctor_get(v___x_1173_, 2);
                            v___x_1175_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1153_, v_pu_1154_, v_code_1174_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
                            v___y_1167_ = v___x_1175_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1176_ = lean_ctor_get(v___x_1173_, 1);
                            v___x_1177_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1153_, v_pu_1154_, v_code_1176_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
                            v___y_1167_ = v___x_1177_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1178_ = lean_ctor_get(v___x_1173_, 0);
                            v___x_1179_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1153_, v_pu_1154_, v_code_1178_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
                            v___y_1167_ = v___x_1179_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1180_, 0, v_b_1158_);
                    return v___x_1180_;
                }
            }
            1 => {
                if lean_obj_tag(v___y_1167_) == 0 {
                    v_a_1168_ = lean_ctor_get(v___y_1167_, 0);
                    lean_inc(v_a_1168_);
                    lean_dec_ref_known(v___y_1167_, 1);
                    v___x_1169_ = 1usize;
                    v___x_1170_ = lean_usize_add(v_i_1156_, v___x_1169_);
                    v_i_1156_ = v___x_1170_;
                    v_b_1158_ = v_a_1168_;
                    state = 0;
                    continue;
                } else {
                    return v___y_1167_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(
    mut v_pu_1181_: u8,
    mut v_pu_1182_: u8,
    mut v_c_1183_: *mut LeanObject,
    mut v___y_1184_: *mut LeanObject,
    mut v___y_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v_k_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: usize = 0;
    let mut v___x_1221_: usize = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: usize = 0;
    let mut v___x_1224_: usize = 0;
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1191_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(v_pu_1181_, v_c_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
                if lean_obj_tag(v___x_1191_) == 0 {
                    v_isSharedCheck_1244_ = (!lean_is_exclusive(v___x_1191_)) as u8;
                    if v_isSharedCheck_1244_ == 0 {
                        v_unused_1245_ = lean_ctor_get(v___x_1191_, 0);
                        lean_dec(v_unused_1245_);
                        v___x_1193_ = v___x_1191_;
                        v_isShared_1194_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1191_);
                        v___x_1193_ = lean_box(0);
                        v_isShared_1194_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1191_;
                }
            }
            1 => match lean_obj_tag(v_c_1183_) {
                0 => {
                    lean_del_object(v___x_1193_);
                    v_k_1195_ = lean_ctor_get(v_c_1183_, 1);
                    v_c_1183_ = v_k_1195_;
                    state = 0;
                    continue;
                }
                1 => {
                    lean_del_object(v___x_1193_);
                    v_decl_1197_ = lean_ctor_get(v_c_1183_, 0);
                    v_k_1198_ = lean_ctor_get(v_c_1183_, 1);
                    v_value_1199_ = lean_ctor_get(v_decl_1197_, 4);
                    v___x_1200_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1181_, v_pu_1182_, v_value_1199_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
                    if lean_obj_tag(v___x_1200_) == 0 {
                        lean_dec_ref_known(v___x_1200_, 1);
                        v_c_1183_ = v_k_1198_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1200_;
                    }
                }
                2 => {
                    lean_del_object(v___x_1193_);
                    v_decl_1202_ = lean_ctor_get(v_c_1183_, 0);
                    v_k_1203_ = lean_ctor_get(v_c_1183_, 1);
                    v_value_1204_ = lean_ctor_get(v_decl_1202_, 4);
                    v___x_1205_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1181_, v_pu_1182_, v_value_1204_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
                    if lean_obj_tag(v___x_1205_) == 0 {
                        lean_dec_ref_known(v___x_1205_, 1);
                        v_c_1183_ = v_k_1203_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1205_;
                    }
                }
                4 => {
                    v_cases_1207_ = lean_ctor_get(v_c_1183_, 0);
                    v_alts_1208_ = lean_ctor_get(v_cases_1207_, 3);
                    v___x_1209_ = lean_unsigned_to_nat(0);
                    v___x_1210_ = lean_array_get_size(v_alts_1208_);
                    v___x_1211_ = lean_box(0);
                    v___x_1212_ = lean_nat_dec_lt(v___x_1209_, v___x_1210_);
                    if v___x_1212_ == 0 {
                        if v_isShared_1194_ == 0 {
                            lean_ctor_set(v___x_1193_, 0, v___x_1211_);
                            v___x_1214_ = v___x_1193_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1211_);
                            v___x_1214_ = v_reuseFailAlloc_1215_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1216_ = lean_nat_dec_le(v___x_1210_, v___x_1210_);
                        if v___x_1216_ == 0 {
                            if v___x_1212_ == 0 {
                                if v_isShared_1194_ == 0 {
                                    lean_ctor_set(v___x_1193_, 0, v___x_1211_);
                                    v___x_1218_ = v___x_1193_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
                                    v___x_1218_ = v_reuseFailAlloc_1219_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1193_);
                                v___x_1220_ = 0usize;
                                v___x_1221_ = lean_usize_of_nat(v___x_1210_);
                                v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_1181_, v_pu_1182_, v_alts_1208_, v___x_1220_, v___x_1221_, v___x_1211_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
                                return v___x_1222_;
                            }
                        } else {
                            lean_del_object(v___x_1193_);
                            v___x_1223_ = 0usize;
                            v___x_1224_ = lean_usize_of_nat(v___x_1210_);
                            v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_1181_, v_pu_1182_, v_alts_1208_, v___x_1223_, v___x_1224_, v___x_1211_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
                            return v___x_1225_;
                        }
                    }
                }
                7 => {
                    lean_del_object(v___x_1193_);
                    v_k_1226_ = lean_ctor_get(v_c_1183_, 3);
                    v_c_1183_ = v_k_1226_;
                    state = 0;
                    continue;
                }
                8 => {
                    lean_del_object(v___x_1193_);
                    v_k_1228_ = lean_ctor_get(v_c_1183_, 3);
                    v_c_1183_ = v_k_1228_;
                    state = 0;
                    continue;
                }
                9 => {
                    lean_del_object(v___x_1193_);
                    v_k_1230_ = lean_ctor_get(v_c_1183_, 5);
                    v_c_1183_ = v_k_1230_;
                    state = 0;
                    continue;
                }
                10 => {
                    lean_del_object(v___x_1193_);
                    v_k_1232_ = lean_ctor_get(v_c_1183_, 2);
                    v_c_1183_ = v_k_1232_;
                    state = 0;
                    continue;
                }
                11 => {
                    lean_del_object(v___x_1193_);
                    v_k_1234_ = lean_ctor_get(v_c_1183_, 2);
                    v_c_1183_ = v_k_1234_;
                    state = 0;
                    continue;
                }
                12 => {
                    lean_del_object(v___x_1193_);
                    v_k_1236_ = lean_ctor_get(v_c_1183_, 3);
                    v_c_1183_ = v_k_1236_;
                    state = 0;
                    continue;
                }
                13 => {
                    lean_del_object(v___x_1193_);
                    v_k_1238_ = lean_ctor_get(v_c_1183_, 1);
                    v_c_1183_ = v_k_1238_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_1240_ = lean_box(0);
                    if v_isShared_1194_ == 0 {
                        lean_ctor_set(v___x_1193_, 0, v___x_1240_);
                        v___x_1242_ = v___x_1193_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
                        v___x_1242_ = v_reuseFailAlloc_1243_;
                        state = 4;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_1214_;
            }
            3 => {
                return v___x_1218_;
            }
            4 => {
                return v___x_1242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___lam__0(
    mut v_pu_1246_: u8,
    mut v_x_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_1246_, v_pu_1246_, v_x_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
    return v___x_1255_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst___boxed(
    mut v_pu_1256_: *mut LeanObject,
    mut v_declName_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1265_: u8 = 0;
    let mut v_res_1266_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1265_ = (lean_unbox(v_pu_1256_) as u8);
    v_res_1266_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst(
        v_pu_boxed_1265_,
        v_declName_1257_,
        v_a_1258_,
        v_a_1259_,
        v_a_1260_,
        v_a_1261_,
        v_a_1262_,
        v_a_1263_,
    );
    lean_dec(v_a_1263_);
    lean_dec_ref(v_a_1262_);
    lean_dec(v_a_1261_);
    lean_dec_ref(v_a_1260_);
    lean_dec(v_a_1259_);
    lean_dec_ref(v_a_1258_);
    lean_dec(v_declName_1257_);
    return v_res_1266_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts___boxed(
    mut v_pu_1267_: *mut LeanObject,
    mut v_code_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v_a_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1276_ = (lean_unbox(v_pu_1267_) as u8);
    v_res_1277_ =
        l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConsts(
            v_pu_boxed_1276_,
            v_code_1268_,
            v_a_1269_,
            v_a_1270_,
            v_a_1271_,
            v_a_1272_,
            v_a_1273_,
            v_a_1274_,
        );
    lean_dec(v_a_1274_);
    lean_dec_ref(v_a_1273_);
    lean_dec(v_a_1272_);
    lean_dec_ref(v_a_1271_);
    lean_dec(v_a_1270_);
    lean_dec_ref(v_a_1269_);
    lean_dec_ref(v_code_1268_);
    return v_res_1277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1___boxed(
    mut v_pu_1278_: *mut LeanObject,
    mut v_pu_1279_: *mut LeanObject,
    mut v_as_1280_: *mut LeanObject,
    mut v_i_1281_: *mut LeanObject,
    mut v_stop_1282_: *mut LeanObject,
    mut v_b_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1291_: u8 = 0;
    let mut v_pu_boxed_1292_: u8 = 0;
    let mut v_i_boxed_1293_: usize = 0;
    let mut v_stop_boxed_1294_: usize = 0;
    let mut v_res_1295_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1291_ = (lean_unbox(v_pu_1278_) as u8);
    v_pu_boxed_1292_ = (lean_unbox(v_pu_1279_) as u8);
    v_i_boxed_1293_ = lean_unbox_usize(v_i_1281_);
    lean_dec(v_i_1281_);
    v_stop_boxed_1294_ = lean_unbox_usize(v_stop_1282_);
    lean_dec(v_stop_1282_);
    v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0_spec__1(v_pu_boxed_1291_, v_pu_boxed_1292_, v_as_1280_, v_i_boxed_1293_, v_stop_boxed_1294_, v_b_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
    lean_dec(v___y_1289_);
    lean_dec_ref(v___y_1288_);
    lean_dec(v___y_1287_);
    lean_dec_ref(v___y_1286_);
    lean_dec(v___y_1285_);
    lean_dec_ref(v___y_1284_);
    lean_dec_ref(v_as_1280_);
    return v_res_1295_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process___boxed(
    mut v_pu_1296_: *mut LeanObject,
    mut v_decl_1297_: *mut LeanObject,
    mut v_a_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
    mut v_a_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1305_: u8 = 0;
    let mut v_res_1306_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1305_ = (lean_unbox(v_pu_1296_) as u8);
    v_res_1306_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(
        v_pu_boxed_1305_,
        v_decl_1297_,
        v_a_1298_,
        v_a_1299_,
        v_a_1300_,
        v_a_1301_,
        v_a_1302_,
        v_a_1303_,
    );
    lean_dec(v_a_1303_);
    lean_dec_ref(v_a_1302_);
    lean_dec(v_a_1301_);
    lean_dec_ref(v_a_1300_);
    lean_dec(v_a_1299_);
    lean_dec_ref(v_a_1298_);
    return v_res_1306_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0___boxed(
    mut v_pu_1307_: *mut LeanObject,
    mut v_pu_1308_: *mut LeanObject,
    mut v_c_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1317_: u8 = 0;
    let mut v_pu_boxed_1318_: u8 = 0;
    let mut v_res_1319_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1317_ = (lean_unbox(v_pu_1307_) as u8);
    v_pu_boxed_1318_ = (lean_unbox(v_pu_1308_) as u8);
    v_res_1319_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__0(v_pu_boxed_1317_, v_pu_boxed_1318_, v_c_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
    lean_dec(v___y_1315_);
    lean_dec_ref(v___y_1314_);
    lean_dec(v___y_1313_);
    lean_dec_ref(v___y_1312_);
    lean_dec(v___y_1311_);
    lean_dec_ref(v___y_1310_);
    lean_dec_ref(v_c_1309_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(
    mut v_pu_1320_: u8,
    mut v_f_1321_: *mut LeanObject,
    mut v_v_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1330_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___redArg(v_f_1321_, v_v_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
    return v___x_1330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3___boxed(
    mut v_pu_1331_: *mut LeanObject,
    mut v_f_1332_: *mut LeanObject,
    mut v_v_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1341_: u8 = 0;
    let mut v_res_1342_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1341_ = (lean_unbox(v_pu_1331_) as u8);
    v_res_1342_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__3(v_pu_boxed_1341_, v_f_1332_, v_v_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
    lean_dec(v___y_1339_);
    lean_dec_ref(v___y_1338_);
    lean_dec(v___y_1337_);
    lean_dec_ref(v___y_1336_);
    lean_dec(v___y_1335_);
    lean_dec_ref(v___y_1334_);
    return v_res_1342_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(
    mut v_00_u03b2_1343_: *mut LeanObject,
    mut v_m_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
) -> u8 {
    let mut v___x_1346_: u8 = 0;
    v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___redArg(v_m_1344_, v_a_1345_);
    return v___x_1346_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1___boxed(
    mut v_00_u03b2_1347_: *mut LeanObject,
    mut v_m_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1350_: u8 = 0;
    let mut v_r_1351_: *mut LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1(v_00_u03b2_1347_, v_m_1348_, v_a_1349_);
    lean_dec(v_a_1349_);
    lean_dec_ref(v_m_1348_);
    v_r_1351_ = lean_box((v_res_1350_) as usize);
    return v_r_1351_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2(
    mut v_00_u03b2_1352_: *mut LeanObject,
    mut v_m_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_b_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2___redArg(v_m_1353_, v_a_1354_, v_b_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(
    mut v_00_u03b2_1357_: *mut LeanObject,
    mut v_m_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___redArg(v_m_1358_, v_a_1359_);
    return v___x_1360_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5___boxed(
    mut v_00_u03b2_1361_: *mut LeanObject,
    mut v_m_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1364_: *mut LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5(v_00_u03b2_1361_, v_m_1362_, v_a_1363_);
    lean_dec(v_a_1363_);
    lean_dec_ref(v_m_1362_);
    return v_res_1364_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(
    mut v_00_u03b2_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_x_1367_: *mut LeanObject,
) -> u8 {
    let mut v___x_1368_: u8 = 0;
    v___x_1368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_1366_, v_x_1367_);
    return v___x_1368_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___boxed(
    mut v_00_u03b2_1369_: *mut LeanObject,
    mut v_a_1370_: *mut LeanObject,
    mut v_x_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1372_: u8 = 0;
    let mut v_r_1373_: *mut LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3(v_00_u03b2_1369_, v_a_1370_, v_x_1371_);
    lean_dec(v_x_1371_);
    lean_dec(v_a_1370_);
    v_r_1373_ = lean_box((v_res_1372_) as usize);
    return v_r_1373_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5(
    mut v_00_u03b2_1374_: *mut LeanObject,
    mut v_data_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_data_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(
    mut v_00_u03b2_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_x_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___redArg(v_a_1378_, v_x_1379_);
    return v___x_1380_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9___boxed(
    mut v_00_u03b2_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_x_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_visitConst_spec__5_spec__9(v_00_u03b2_1381_, v_a_1382_, v_x_1383_);
    lean_dec(v_x_1383_);
    lean_dec(v_a_1382_);
    return v_res_1384_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8(
    mut v_00_u03b2_1385_: *mut LeanObject,
    mut v_i_1386_: *mut LeanObject,
    mut v_source_1387_: *mut LeanObject,
    mut v_target_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v___x_1389_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8___redArg(v_i_1386_, v_source_1387_, v_target_1388_);
    return v___x_1389_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10(
    mut v_00_u03b2_1390_: *mut LeanObject,
    mut v_x_1391_: *mut LeanObject,
    mut v_x_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg(v_x_1391_, v_x_1392_);
    return v___x_1393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(
    mut v_pu_1394_: u8,
    mut v_as_1395_: *mut LeanObject,
    mut v_i_1396_: usize,
    mut v_stop_1397_: usize,
    mut v_b_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: usize = 0;
    let mut v___x_1411_: usize = 0;
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1406_ = lean_usize_dec_eq(v_i_1396_, v_stop_1397_);
                if v___x_1406_ == 0 {
                    v___x_1407_ = lean_array_uget_borrowed(v_as_1395_, v_i_1396_);
                    lean_inc(v___x_1407_);
                    v___x_1408_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process(v_pu_1394_, v___x_1407_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
                    if lean_obj_tag(v___x_1408_) == 0 {
                        v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
                        lean_inc(v_a_1409_);
                        lean_dec_ref_known(v___x_1408_, 1);
                        v___x_1410_ = 1usize;
                        v___x_1411_ = lean_usize_add(v_i_1396_, v___x_1410_);
                        v_i_1396_ = v___x_1411_;
                        v_b_1398_ = v_a_1409_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1408_;
                    }
                } else {
                    v___x_1413_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1413_, 0, v_b_1398_);
                    return v___x_1413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0___boxed(
    mut v_pu_1414_: *mut LeanObject,
    mut v_as_1415_: *mut LeanObject,
    mut v_i_1416_: *mut LeanObject,
    mut v_stop_1417_: *mut LeanObject,
    mut v_b_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1426_: u8 = 0;
    let mut v_i_boxed_1427_: usize = 0;
    let mut v_stop_boxed_1428_: usize = 0;
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1426_ = (lean_unbox(v_pu_1414_) as u8);
    v_i_boxed_1427_ = lean_unbox_usize(v_i_1416_);
    lean_dec(v_i_1416_);
    v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1417_);
    lean_dec(v_stop_1417_);
    v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_boxed_1426_, v_as_1415_, v_i_boxed_1427_, v_stop_boxed_1428_, v_b_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
    lean_dec(v___y_1424_);
    lean_dec_ref(v___y_1423_);
    lean_dec(v___y_1422_);
    lean_dec_ref(v___y_1421_);
    lean_dec(v___y_1420_);
    lean_dec_ref(v___y_1419_);
    lean_dec_ref(v_as_1415_);
    return v_res_1429_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(
    mut v_pu_1430_: u8,
    mut v_decls_1431_: *mut LeanObject,
    mut v_a_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
    mut v_a_1434_: *mut LeanObject,
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
    mut v_a_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u8 = 0;
    v___x_1439_ = lean_unsigned_to_nat(0);
    v___x_1440_ = lean_array_get_size(v_decls_1431_);
    v___x_1441_ = lean_box(0);
    v___x_1442_ = lean_nat_dec_lt(v___x_1439_, v___x_1440_);
    if v___x_1442_ == 0 {
        let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
        v___x_1443_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1443_, 0, v___x_1441_);
        return v___x_1443_;
    } else {
        let mut v___x_1444_: u8 = 0;
        v___x_1444_ = lean_nat_dec_le(v___x_1440_, v___x_1440_);
        if v___x_1444_ == 0 {
            if v___x_1442_ == 0 {
                let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
                v___x_1445_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1445_, 0, v___x_1441_);
                return v___x_1445_;
            } else {
                let mut v___x_1446_: usize = 0;
                let mut v___x_1447_: usize = 0;
                let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
                v___x_1446_ = 0usize;
                v___x_1447_ = lean_usize_of_nat(v___x_1440_);
                v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_1430_, v_decls_1431_, v___x_1446_, v___x_1447_, v___x_1441_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
                return v___x_1448_;
            }
        } else {
            let mut v___x_1449_: usize = 0;
            let mut v___x_1450_: usize = 0;
            let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
            v___x_1449_ = 0usize;
            v___x_1450_ = lean_usize_of_nat(v___x_1440_);
            v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go_spec__0(v_pu_1430_, v_decls_1431_, v___x_1449_, v___x_1450_, v___x_1441_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
            return v___x_1451_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go___boxed(
    mut v_pu_1452_: *mut LeanObject,
    mut v_decls_1453_: *mut LeanObject,
    mut v_a_1454_: *mut LeanObject,
    mut v_a_1455_: *mut LeanObject,
    mut v_a_1456_: *mut LeanObject,
    mut v_a_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v_a_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1461_: u8 = 0;
    let mut v_res_1462_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1461_ = (lean_unbox(v_pu_1452_) as u8);
    v_res_1462_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(
        v_pu_boxed_1461_,
        v_decls_1453_,
        v_a_1454_,
        v_a_1455_,
        v_a_1456_,
        v_a_1457_,
        v_a_1458_,
        v_a_1459_,
    );
    lean_dec(v_a_1459_);
    lean_dec_ref(v_a_1458_);
    lean_dec(v_a_1457_);
    lean_dec_ref(v_a_1456_);
    lean_dec(v_a_1455_);
    lean_dec_ref(v_a_1454_);
    lean_dec_ref(v_decls_1453_);
    return v_res_1462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(
    mut v_sz_1463_: usize,
    mut v_i_1464_: usize,
    mut v_bs_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1466_: u8 = 0;
    let mut v_v_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: usize = 0;
    let mut v___x_1474_: usize = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1466_ = lean_usize_dec_lt(v_i_1464_, v_sz_1463_);
                if v___x_1466_ == 0 {
                    return v_bs_1465_;
                } else {
                    v_v_1467_ = lean_array_uget(v_bs_1465_, v_i_1464_);
                    v_toSignature_1468_ = lean_ctor_get(v_v_1467_, 0);
                    v_name_1469_ = lean_ctor_get(v_toSignature_1468_, 0);
                    lean_inc(v_name_1469_);
                    v___x_1470_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1471_ = lean_array_uset(v_bs_1465_, v_i_1464_, v___x_1470_);
                    v___x_1472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1472_, 0, v_name_1469_);
                    lean_ctor_set(v___x_1472_, 1, v_v_1467_);
                    v___x_1473_ = 1usize;
                    v___x_1474_ = lean_usize_add(v_i_1464_, v___x_1473_);
                    v___x_1475_ = lean_array_uset(v_bs_x27_1471_, v_i_1464_, v___x_1472_);
                    v_i_1464_ = v___x_1474_;
                    v_bs_1465_ = v___x_1475_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0___boxed(
    mut v_sz_1477_: *mut LeanObject,
    mut v_i_1478_: *mut LeanObject,
    mut v_bs_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1480_: usize = 0;
    let mut v_i_boxed_1481_: usize = 0;
    let mut v_res_1482_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1477_);
    lean_dec(v_sz_1477_);
    v_i_boxed_1481_ = lean_unbox_usize(v_i_1478_);
    lean_dec(v_i_1478_);
    v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_boxed_1480_, v_i_boxed_1481_, v_bs_1479_);
    return v_res_1482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(
    mut v_a_1483_: *mut LeanObject,
    mut v_b_1484_: *mut LeanObject,
    mut v_x_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1485_) == 0 {
                    lean_dec(v_b_1484_);
                    lean_dec(v_a_1483_);
                    return v_x_1485_;
                } else {
                    v_key_1486_ = lean_ctor_get(v_x_1485_, 0);
                    v_value_1487_ = lean_ctor_get(v_x_1485_, 1);
                    v_tail_1488_ = lean_ctor_get(v_x_1485_, 2);
                    v_isSharedCheck_1500_ = (!lean_is_exclusive(v_x_1485_)) as u8;
                    if v_isSharedCheck_1500_ == 0 {
                        v___x_1490_ = v_x_1485_;
                        v_isShared_1491_ = v_isSharedCheck_1500_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1488_);
                        lean_inc(v_value_1487_);
                        lean_inc(v_key_1486_);
                        lean_dec(v_x_1485_);
                        v___x_1490_ = lean_box(0);
                        v_isShared_1491_ = v_isSharedCheck_1500_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1492_ = lean_name_eq(v_key_1486_, v_a_1483_);
                if v___x_1492_ == 0 {
                    v___x_1493_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_1483_, v_b_1484_, v_tail_1488_);
                    if v_isShared_1491_ == 0 {
                        lean_ctor_set(v___x_1490_, 2, v___x_1493_);
                        v___x_1495_ = v___x_1490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_key_1486_);
                        lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_value_1487_);
                        lean_ctor_set(v_reuseFailAlloc_1496_, 2, v___x_1493_);
                        v___x_1495_ = v_reuseFailAlloc_1496_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1487_);
                    lean_dec(v_key_1486_);
                    if v_isShared_1491_ == 0 {
                        lean_ctor_set(v___x_1490_, 1, v_b_1484_);
                        lean_ctor_set(v___x_1490_, 0, v_a_1483_);
                        v___x_1498_ = v___x_1490_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1483_);
                        lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_b_1484_);
                        lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_tail_1488_);
                        v___x_1498_ = v_reuseFailAlloc_1499_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1495_;
            }
            3 => {
                return v___x_1498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(
    mut v_m_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_b_1503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: u64 = 0;
    let mut v___x_1512_: u64 = 0;
    let mut v___x_1513_: u64 = 0;
    let mut v_fold_1514_: u64 = 0;
    let mut v___x_1515_: u64 = 0;
    let mut v___x_1516_: u64 = 0;
    let mut v___x_1517_: u64 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v_bkt_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: u8 = 0;
    let mut v_val_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u64 = 0;
    let mut v_hash_1550_: u64 = 0;
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1504_ = lean_ctor_get(v_m_1501_, 0);
                v_buckets_1505_ = lean_ctor_get(v_m_1501_, 1);
                v_isSharedCheck_1551_ = (!lean_is_exclusive(v_m_1501_)) as u8;
                if v_isSharedCheck_1551_ == 0 {
                    v___x_1507_ = v_m_1501_;
                    v_isShared_1508_ = v_isSharedCheck_1551_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1505_);
                    lean_inc(v_size_1504_);
                    lean_dec(v_m_1501_);
                    v___x_1507_ = lean_box(0);
                    v_isShared_1508_ = v_isSharedCheck_1551_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1509_ = lean_array_get_size(v_buckets_1505_);
                if lean_obj_tag(v_a_1502_) == 0 {
                    v___x_1549_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_1511_ = v___x_1549_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1550_ = lean_ctor_get_uint64(
                        v_a_1502_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1511_ = v_hash_1550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1512_ = 32u64;
                v___x_1513_ = lean_uint64_shift_right(v___y_1511_, v___x_1512_);
                v_fold_1514_ = lean_uint64_xor(v___y_1511_, v___x_1513_);
                v___x_1515_ = 16u64;
                v___x_1516_ = lean_uint64_shift_right(v_fold_1514_, v___x_1515_);
                v___x_1517_ = lean_uint64_xor(v_fold_1514_, v___x_1516_);
                v___x_1518_ = lean_uint64_to_usize(v___x_1517_);
                v___x_1519_ = lean_usize_of_nat(v___x_1509_);
                v___x_1520_ = 1usize;
                v___x_1521_ = lean_usize_sub(v___x_1519_, v___x_1520_);
                v___x_1522_ = lean_usize_land(v___x_1518_, v___x_1521_);
                v_bkt_1523_ = lean_array_uget_borrowed(v_buckets_1505_, v___x_1522_);
                v___x_1524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__1_spec__3___redArg(v_a_1502_, v_bkt_1523_);
                if v___x_1524_ == 0 {
                    v___x_1525_ = lean_unsigned_to_nat(1);
                    v_size_x27_1526_ = lean_nat_add(v_size_1504_, v___x_1525_);
                    lean_dec(v_size_1504_);
                    lean_inc(v_bkt_1523_);
                    v___x_1527_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1527_, 0, v_a_1502_);
                    lean_ctor_set(v___x_1527_, 1, v_b_1503_);
                    lean_ctor_set(v___x_1527_, 2, v_bkt_1523_);
                    v_buckets_x27_1528_ =
                        lean_array_uset(v_buckets_1505_, v___x_1522_, v___x_1527_);
                    v___x_1529_ = lean_unsigned_to_nat(4);
                    v___x_1530_ = lean_nat_mul(v_size_x27_1526_, v___x_1529_);
                    v___x_1531_ = lean_unsigned_to_nat(3);
                    v___x_1532_ = lean_nat_div(v___x_1530_, v___x_1531_);
                    lean_dec(v___x_1530_);
                    v___x_1533_ = lean_array_get_size(v_buckets_x27_1528_);
                    v___x_1534_ = lean_nat_dec_le(v___x_1532_, v___x_1533_);
                    lean_dec(v___x_1532_);
                    if v___x_1534_ == 0 {
                        v_val_1535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_process_spec__2_spec__5___redArg(v_buckets_x27_1528_);
                        if v_isShared_1508_ == 0 {
                            lean_ctor_set(v___x_1507_, 1, v_val_1535_);
                            lean_ctor_set(v___x_1507_, 0, v_size_x27_1526_);
                            v___x_1537_ = v___x_1507_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_size_x27_1526_);
                            lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_val_1535_);
                            v___x_1537_ = v_reuseFailAlloc_1538_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1508_ == 0 {
                            lean_ctor_set(v___x_1507_, 1, v_buckets_x27_1528_);
                            lean_ctor_set(v___x_1507_, 0, v_size_x27_1526_);
                            v___x_1540_ = v___x_1507_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_size_x27_1526_);
                            lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_buckets_x27_1528_);
                            v___x_1540_ = v_reuseFailAlloc_1541_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1523_);
                    v___x_1542_ = lean_box(0);
                    v_buckets_x27_1543_ =
                        lean_array_uset(v_buckets_1505_, v___x_1522_, v___x_1542_);
                    v___x_1544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_1502_, v_b_1503_, v_bkt_1523_);
                    v___x_1545_ = lean_array_uset(v_buckets_x27_1543_, v___x_1522_, v___x_1544_);
                    if v_isShared_1508_ == 0 {
                        lean_ctor_set(v___x_1507_, 1, v___x_1545_);
                        v___x_1547_ = v___x_1507_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_size_1504_);
                        lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1545_);
                        v___x_1547_ = v_reuseFailAlloc_1548_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1537_;
            }
            4 => {
                return v___x_1540_;
            }
            5 => {
                return v___x_1547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(
    mut v_as_1552_: *mut LeanObject,
    mut v_sz_1553_: usize,
    mut v_i_1554_: usize,
    mut v_b_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1556_: u8 = 0;
    let mut v_a_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1556_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
                if v___x_1556_ == 0 {
                    return v_b_1555_;
                } else {
                    v_a_1557_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
                    v_fst_1558_ = lean_ctor_get(v_a_1557_, 0);
                    v_snd_1559_ = lean_ctor_get(v_a_1557_, 1);
                    lean_inc(v_snd_1559_);
                    lean_inc(v_fst_1558_);
                    v_r_1560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_b_1555_, v_fst_1558_, v_snd_1559_);
                    v___x_1561_ = 1usize;
                    v___x_1562_ = lean_usize_add(v_i_1554_, v___x_1561_);
                    v_i_1554_ = v___x_1562_;
                    v_b_1555_ = v_r_1560_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2___boxed(
    mut v_as_1564_: *mut LeanObject,
    mut v_sz_1565_: *mut LeanObject,
    mut v_i_1566_: *mut LeanObject,
    mut v_b_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1568_: usize = 0;
    let mut v_i_boxed_1569_: usize = 0;
    let mut v_res_1570_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1565_);
    lean_dec(v_sz_1565_);
    v_i_boxed_1569_ = lean_unbox_usize(v_i_1566_);
    lean_dec(v_i_1566_);
    v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_as_1564_, v_sz_boxed_1568_, v_i_boxed_1569_, v_b_1567_);
    lean_dec_ref(v_as_1564_);
    return v_res_1570_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(
    mut v_m_1571_: *mut LeanObject,
    mut v_l_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1573_: usize = 0;
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1573_ = lean_array_size(v_l_1572_);
    v___x_1574_ = 0usize;
    v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__2(v_l_1572_, v_sz_1573_, v___x_1574_, v_m_1571_);
    return v___x_1575_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1___boxed(
    mut v_m_1576_: *mut LeanObject,
    mut v_l_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v_m_1576_, v_l_1577_);
    lean_dec_ref(v_l_1577_);
    return v_res_1578_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0()
-> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    v___x_1579_ = lean_box(0);
    v___x_1580_ = lean_unsigned_to_nat(16);
    v___x_1581_ = lean_mk_array(v___x_1580_, v___x_1579_);
    return v___x_1581_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1()
-> *mut LeanObject {
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1582_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0_once
        ),
        _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__0,
    );
    v___x_1583_ = lean_unsigned_to_nat(0);
    v___x_1584_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1584_, 0, v___x_1583_);
    lean_ctor_set(v___x_1584_, 1, v___x_1582_);
    return v___x_1584_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(
    mut v_pu_1585_: u8,
    mut v_decls_1586_: *mut LeanObject,
    mut v_a_1587_: *mut LeanObject,
    mut v_a_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1606_: usize = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declsMap_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v_unused_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = lean_unsigned_to_nat(0);
                v___x_1593_ = lean_box(0);
                v___x_1594_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___closed__1);
                v___x_1595_ = lean_array_get_size(v_decls_1586_);
                v___x_1596_ = lean_unsigned_to_nat(4);
                v___x_1597_ = lean_nat_mul(v___x_1595_, v___x_1596_);
                v___x_1598_ = lean_unsigned_to_nat(3);
                v___x_1599_ = lean_nat_div(v___x_1597_, v___x_1598_);
                lean_dec(v___x_1597_);
                v___x_1600_ = l_Nat_nextPowerOfTwo(v___x_1599_);
                lean_dec(v___x_1599_);
                v___x_1601_ = lean_mk_array(v___x_1600_, v___x_1593_);
                v___x_1602_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1602_, 0, v___x_1592_);
                lean_ctor_set(v___x_1602_, 1, v___x_1601_);
                v___x_1603_ = lean_mk_empty_array_with_capacity(v___x_1595_);
                v___x_1604_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                lean_ctor_set(v___x_1604_, 1, v___x_1603_);
                v___x_1605_ = lean_st_mk_ref(v___x_1604_);
                v_sz_1606_ = lean_array_size(v_decls_1586_);
                v___x_1607_ = 0usize;
                lean_inc_ref(v_decls_1586_);
                v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__0(v_sz_1606_, v___x_1607_, v_decls_1586_);
                v_declsMap_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1(v___x_1594_, v___x_1608_);
                lean_dec_ref(v___x_1608_);
                v___x_1610_ =
                    l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_go(
                        v_pu_1585_,
                        v_decls_1586_,
                        v_declsMap_1609_,
                        v___x_1605_,
                        v_a_1587_,
                        v_a_1588_,
                        v_a_1589_,
                        v_a_1590_,
                    );
                lean_dec_ref(v_declsMap_1609_);
                lean_dec_ref(v_decls_1586_);
                if lean_obj_tag(v___x_1610_) == 0 {
                    v_isSharedCheck_1619_ = (!lean_is_exclusive(v___x_1610_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v_unused_1620_ = lean_ctor_get(v___x_1610_, 0);
                        lean_dec(v_unused_1620_);
                        v___x_1612_ = v___x_1610_;
                        v_isShared_1613_ = v_isSharedCheck_1619_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1610_);
                        v___x_1612_ = lean_box(0);
                        v_isShared_1613_ = v_isSharedCheck_1619_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1605_);
                    v_a_1621_ = lean_ctor_get(v___x_1610_, 0);
                    v_isSharedCheck_1628_ = (!lean_is_exclusive(v___x_1610_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1610_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1621_);
                        lean_dec(v___x_1610_);
                        v___x_1623_ = lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1614_ = lean_st_ref_get(v___x_1605_);
                lean_dec(v___x_1605_);
                v_order_1615_ = lean_ctor_get(v___x_1614_, 1);
                lean_inc_ref(v_order_1615_);
                lean_dec(v___x_1614_);
                if v_isShared_1613_ == 0 {
                    lean_ctor_set(v___x_1612_, 0, v_order_1615_);
                    v___x_1617_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_order_1615_);
                    v___x_1617_ = v_reuseFailAlloc_1618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1617_;
            }
            3 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort___boxed(
    mut v_pu_1629_: *mut LeanObject,
    mut v_decls_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1636_: u8 = 0;
    let mut v_res_1637_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1636_ = (lean_unbox(v_pu_1629_) as u8);
    v_res_1637_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(
        v_pu_boxed_1636_,
        v_decls_1630_,
        v_a_1631_,
        v_a_1632_,
        v_a_1633_,
        v_a_1634_,
    );
    lean_dec(v_a_1634_);
    lean_dec_ref(v_a_1633_);
    lean_dec(v_a_1632_);
    lean_dec_ref(v_a_1631_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1(
    mut v_00_u03b2_1638_: *mut LeanObject,
    mut v_m_1639_: *mut LeanObject,
    mut v_a_1640_: *mut LeanObject,
    mut v_b_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1___redArg(v_m_1639_, v_a_1640_, v_b_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
    mut v_b_1645_: *mut LeanObject,
    mut v_x_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort_spec__1_spec__1_spec__2___redArg(v_a_1644_, v_b_1645_, v_x_1646_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toposortDecls(
    mut v_pu_1648_: u8,
    mut v_decls_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(
        v_pu_1648_,
        v_decls_1649_,
        v_a_1650_,
        v_a_1651_,
        v_a_1652_,
        v_a_1653_,
    );
    return v___x_1655_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toposortDecls___boxed(
    mut v_pu_1656_: *mut LeanObject,
    mut v_decls_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_a_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
    mut v_a_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1663_: u8 = 0;
    let mut v_res_1664_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1663_ = (lean_unbox(v_pu_1656_) as u8);
    v_res_1664_ = l_Lean_Compiler_LCNF_toposortDecls(
        v_pu_boxed_1663_,
        v_decls_1657_,
        v_a_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
    );
    lean_dec(v_a_1661_);
    lean_dec_ref(v_a_1660_);
    lean_dec(v_a_1659_);
    lean_dec_ref(v_a_1658_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toposortPass___lam__0(
    mut v___x_1665_: u8,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    v___x_1672_ = l___private_Lean_Compiler_LCNF_Toposort_0__Lean_Compiler_LCNF_toposort(
        v___x_1665_,
        v___y_1666_,
        v___y_1667_,
        v___y_1668_,
        v___y_1669_,
        v___y_1670_,
    );
    return v___x_1672_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed(
    mut v___x_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_28__boxed_1680_: u8 = 0;
    let mut v_res_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_28__boxed_1680_ = (lean_unbox(v___x_1673_) as u8);
    v_res_1681_ = l_Lean_Compiler_LCNF_toposortPass___lam__0(
        v___x_28__boxed_1680_,
        v___y_1674_,
        v___y_1675_,
        v___y_1676_,
        v___y_1677_,
        v___y_1678_,
    );
    lean_dec(v___y_1678_);
    lean_dec_ref(v___y_1677_);
    lean_dec(v___y_1676_);
    lean_dec_ref(v___y_1675_);
    return v_res_1681_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toposortPass___closed__2() -> u8 {
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: u8 = 0;
    v___x_1685_ = 2;
    v___x_1686_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toposortPass___closed__3() -> *mut LeanObject {
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1687_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__2_once),
        _init_l_Lean_Compiler_LCNF_toposortPass___closed__2,
    );
    v___x_1688_ = lean_box((v___x_1687_) as usize);
    v___f_1689_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_toposortPass___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_1689_, 0, v___x_1688_);
    return v___f_1689_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toposortPass___closed__4() -> *mut LeanObject {
    let mut v___f_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v___f_1690_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__3_once),
        _init_l_Lean_Compiler_LCNF_toposortPass___closed__3,
    );
    v___x_1691_ = l_Lean_Compiler_LCNF_toposortPass___closed__1;
    v___x_1692_ = 0;
    v___x_1693_ = 2;
    v___x_1694_ = lean_unsigned_to_nat(0);
    v___x_1695_ = lean_alloc_ctor(0, 3, (3) as u32);
    lean_ctor_set(v___x_1695_, 0, v___x_1694_);
    lean_ctor_set(v___x_1695_, 1, v___x_1691_);
    lean_ctor_set(v___x_1695_, 2, v___f_1690_);
    lean_ctor_set_uint8(
        v___x_1695_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_1693_,
    );
    lean_ctor_set_uint8(
        v___x_1695_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_1693_,
    );
    lean_ctor_set_uint8(
        v___x_1695_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
        v___x_1692_,
    );
    return v___x_1695_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toposortPass() -> *mut LeanObject {
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v___x_1696_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toposortPass___closed__4_once),
        _init_l_Lean_Compiler_LCNF_toposortPass___closed__4,
    );
    return v___x_1696_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Toposort(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_toposortPass = _init_l_Lean_Compiler_LCNF_toposortPass();
    lean_mark_persistent(l_Lean_Compiler_LCNF_toposortPass);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Toposort(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Toposort(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Toposort(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Toposort(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Toposort(builtin);
}
