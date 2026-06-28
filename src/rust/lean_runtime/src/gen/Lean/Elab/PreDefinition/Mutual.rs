// Lean compiler output
// Module: Lean.Elab.PreDefinition.Mutual
// Imports: Lean.Elab.PreDefinition.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::CoreM::{l_Lean_diagnostics, l_Lean_enableRealizationsForConst};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::DefView::l_Lean_Elab_DefKind_isTheorem;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    initialize_Lean_Elab_PreDefinition_Basic, l_Lean_Elab_PreDefinition_filterAttrs,
    l_Lean_Elab_abstractNestedProofs, l_Lean_Elab_addNonRec, l_Lean_Elab_addNonRec___boxed,
    l_Lean_Elab_applyAttributesOf, l_Lean_Elab_eraseRecAppSyntax,
    l_Lean_Elab_instInhabitedPreDefinition_default,
    runtime_initialize_Lean_Elab_PreDefinition_Basic,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_saveEqnAffectingOptions;
use crate::r#gen::Lean::ReducibilityAttrs::{
    l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore,
    l_Lean_allowUnsafeReducibility,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 0,
        ],
    };
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value)
                as *mut LeanObject,
            5229394285883816413 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value) as *mut LeanObject,7045040058828669725 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value) as *mut LeanObject,2616510057874194026 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value) as *mut LeanObject,1015365147026633853 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value) as *mut LeanObject,11290700302157177994 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(
    mut v_opts_772_: *mut LeanObject,
    mut v_opt_773_: *mut LeanObject,
) -> u8 {
    let mut v_name_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v_name_774_ = lean_ctor_get(v_opt_773_, 0);
    v_defValue_775_ = lean_ctor_get(v_opt_773_, 1);
    v_map_776_ = lean_ctor_get(v_opts_772_, 0);
    v___x_777_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_776_,
            v_name_774_,
        );
    if lean_obj_tag(v___x_777_) == 0 {
        let mut v___x_778_: u8 = 0;
        v___x_778_ = (lean_unbox(v_defValue_775_) as u8);
        return v___x_778_;
    } else {
        let mut v_val_779_: *mut LeanObject = core::ptr::null_mut();
        v_val_779_ = lean_ctor_get(v___x_777_, 0);
        lean_inc(v_val_779_);
        lean_dec_ref_known(v___x_777_, 1);
        if lean_obj_tag(v_val_779_) == 1 {
            let mut v_v_780_: u8 = 0;
            v_v_780_ = lean_ctor_get_uint8(v_val_779_, 0 as u32);
            lean_dec_ref_known(v_val_779_, 0);
            return v_v_780_;
        } else {
            let mut v___x_781_: u8 = 0;
            lean_dec(v_val_779_);
            v___x_781_ = (lean_unbox(v_defValue_775_) as u8);
            return v___x_781_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(
    mut v_opts_782_: *mut LeanObject,
    mut v_opt_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: u8 = 0;
    let mut v_r_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(
        v_opts_782_,
        v_opt_783_,
    );
    lean_dec_ref(v_opt_783_);
    lean_dec_ref(v_opts_782_);
    v_r_785_ = lean_box((v_res_784_) as usize);
    return v_r_785_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(
    mut v_opts_786_: *mut LeanObject,
    mut v_opt_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    v_name_788_ = lean_ctor_get(v_opt_787_, 0);
    v_defValue_789_ = lean_ctor_get(v_opt_787_, 1);
    v_map_790_ = lean_ctor_get(v_opts_786_, 0);
    v___x_791_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_790_,
            v_name_788_,
        );
    if lean_obj_tag(v___x_791_) == 0 {
        lean_inc(v_defValue_789_);
        return v_defValue_789_;
    } else {
        let mut v_val_792_: *mut LeanObject = core::ptr::null_mut();
        v_val_792_ = lean_ctor_get(v___x_791_, 0);
        lean_inc(v_val_792_);
        lean_dec_ref_known(v___x_791_, 1);
        if lean_obj_tag(v_val_792_) == 3 {
            let mut v_v_793_: *mut LeanObject = core::ptr::null_mut();
            v_v_793_ = lean_ctor_get(v_val_792_, 0);
            lean_inc(v_v_793_);
            lean_dec_ref_known(v_val_792_, 1);
            return v_v_793_;
        } else {
            lean_dec(v_val_792_);
            lean_inc(v_defValue_789_);
            return v_defValue_789_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(
    mut v_opts_794_: *mut LeanObject,
    mut v_opt_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_796_: *mut LeanObject = core::ptr::null_mut();
    v_res_796_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(
        v_opts_794_,
        v_opt_795_,
    );
    lean_dec_ref(v_opt_795_);
    lean_dec_ref(v_opts_794_);
    return v_res_796_;
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(
    mut v_attr_800_: *mut LeanObject,
) -> u8 {
    let mut v_name_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    v_name_801_ = lean_ctor_get(v_attr_800_, 0);
    v___x_802_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1;
    v___x_803_ = lean_name_eq(v_name_801_, v___x_802_);
    if v___x_803_ == 0 {
        let mut v___x_804_: u8 = 0;
        v___x_804_ = 1;
        return v___x_804_;
    } else {
        let mut v___x_805_: u8 = 0;
        v___x_805_ = 0;
        return v___x_805_;
    }
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(
    mut v_attr_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_807_: u8 = 0;
    let mut v_r_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(v_attr_806_);
    lean_dec_ref(v_attr_806_);
    v_r_808_ = lean_box((v_res_807_) as usize);
    return v_r_808_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(
    mut v_flag_809_: u8,
    mut v___y_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_824_: u8 = 0;
    let mut v_assignment_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_830_: u8 = 0;
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut v_isSharedCheck_841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_812_ = lean_st_ref_take(v___y_810_);
                v_infoState_813_ = lean_ctor_get(v___x_812_, 7);
                v_env_814_ = lean_ctor_get(v___x_812_, 0);
                v_nextMacroScope_815_ = lean_ctor_get(v___x_812_, 1);
                v_ngen_816_ = lean_ctor_get(v___x_812_, 2);
                v_auxDeclNGen_817_ = lean_ctor_get(v___x_812_, 3);
                v_traceState_818_ = lean_ctor_get(v___x_812_, 4);
                v_cache_819_ = lean_ctor_get(v___x_812_, 5);
                v_messages_820_ = lean_ctor_get(v___x_812_, 6);
                v_snapshotTasks_821_ = lean_ctor_get(v___x_812_, 8);
                v_isSharedCheck_841_ = (!lean_is_exclusive(v___x_812_)) as u8;
                if v_isSharedCheck_841_ == 0 {
                    v___x_823_ = v___x_812_;
                    v_isShared_824_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_821_);
                    lean_inc(v_infoState_813_);
                    lean_inc(v_messages_820_);
                    lean_inc(v_cache_819_);
                    lean_inc(v_traceState_818_);
                    lean_inc(v_auxDeclNGen_817_);
                    lean_inc(v_ngen_816_);
                    lean_inc(v_nextMacroScope_815_);
                    lean_inc(v_env_814_);
                    lean_dec(v___x_812_);
                    v___x_823_ = lean_box(0);
                    v_isShared_824_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_assignment_825_ = lean_ctor_get(v_infoState_813_, 0);
                v_lazyAssignment_826_ = lean_ctor_get(v_infoState_813_, 1);
                v_trees_827_ = lean_ctor_get(v_infoState_813_, 2);
                v_isSharedCheck_840_ = (!lean_is_exclusive(v_infoState_813_)) as u8;
                if v_isSharedCheck_840_ == 0 {
                    v___x_829_ = v_infoState_813_;
                    v_isShared_830_ = v_isSharedCheck_840_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_827_);
                    lean_inc(v_lazyAssignment_826_);
                    lean_inc(v_assignment_825_);
                    lean_dec(v_infoState_813_);
                    v___x_829_ = lean_box(0);
                    v_isShared_830_ = v_isSharedCheck_840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_830_ == 0 {
                    v___x_832_ = v___x_829_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_839_, 0, v_assignment_825_);
                    lean_ctor_set(v_reuseFailAlloc_839_, 1, v_lazyAssignment_826_);
                    lean_ctor_set(v_reuseFailAlloc_839_, 2, v_trees_827_);
                    v___x_832_ = v_reuseFailAlloc_839_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_832_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_flag_809_,
                );
                if v_isShared_824_ == 0 {
                    lean_ctor_set(v___x_823_, 7, v___x_832_);
                    v___x_834_ = v___x_823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_838_, 0, v_env_814_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 1, v_nextMacroScope_815_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 2, v_ngen_816_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 3, v_auxDeclNGen_817_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 4, v_traceState_818_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 5, v_cache_819_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 6, v_messages_820_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 7, v___x_832_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 8, v_snapshotTasks_821_);
                    v___x_834_ = v_reuseFailAlloc_838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_835_ = lean_st_ref_set(v___y_810_, v___x_834_);
                v___x_836_ = lean_box(0);
                v___x_837_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_837_, 0, v___x_836_);
                return v___x_837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg___boxed(
    mut v_flag_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
    mut v___y_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_845_: u8 = 0;
    let mut v_res_846_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_845_ = (lean_unbox(v_flag_842_) as u8);
    v_res_846_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_boxed_845_, v___y_843_);
    lean_dec(v___y_843_);
    return v_res_846_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(
    mut v_flag_847_: u8,
    mut v_x_848_: *mut LeanObject,
    mut v___y_849_: *mut LeanObject,
    mut v___y_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_858_: u8 = 0;
    let mut v_a_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_864_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_868_: u8 = 0;
    let mut v_unused_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v_unused_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_856_ = lean_st_ref_get(v___y_854_);
                v_infoState_857_ = lean_ctor_get(v___x_856_, 7);
                lean_inc_ref(v_infoState_857_);
                lean_dec(v___x_856_);
                v_enabled_858_ = lean_ctor_get_uint8(
                    v_infoState_857_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_857_);
                v___x_870_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_847_, v___y_854_);
                lean_dec_ref(v___x_870_);
                lean_inc(v___y_854_);
                lean_inc_ref(v___y_853_);
                lean_inc(v___y_852_);
                lean_inc_ref(v___y_851_);
                lean_inc(v___y_850_);
                lean_inc_ref(v___y_849_);
                v___x_871_ = lean_apply_7(
                    v_x_848_,
                    v___y_849_,
                    v___y_850_,
                    v___y_851_,
                    v___y_852_,
                    v___y_853_,
                    v___y_854_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_871_) == 0 {
                    v_a_872_ = lean_ctor_get(v___x_871_, 0);
                    lean_inc(v_a_872_);
                    lean_dec_ref_known(v___x_871_, 1);
                    v___x_873_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_858_, v___y_854_);
                    v_isSharedCheck_880_ = (!lean_is_exclusive(v___x_873_)) as u8;
                    if v_isSharedCheck_880_ == 0 {
                        v_unused_881_ = lean_ctor_get(v___x_873_, 0);
                        lean_dec(v_unused_881_);
                        v___x_875_ = v___x_873_;
                        v_isShared_876_ = v_isSharedCheck_880_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_873_);
                        v___x_875_ = lean_box(0);
                        v_isShared_876_ = v_isSharedCheck_880_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_882_ = lean_ctor_get(v___x_871_, 0);
                    lean_inc(v_a_882_);
                    lean_dec_ref_known(v___x_871_, 1);
                    v_a_860_ = v_a_882_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_861_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_858_, v___y_854_);
                v_isSharedCheck_868_ = (!lean_is_exclusive(v___x_861_)) as u8;
                if v_isSharedCheck_868_ == 0 {
                    v_unused_869_ = lean_ctor_get(v___x_861_, 0);
                    lean_dec(v_unused_869_);
                    v___x_863_ = v___x_861_;
                    v_isShared_864_ = v_isSharedCheck_868_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_861_);
                    v___x_863_ = lean_box(0);
                    v_isShared_864_ = v_isSharedCheck_868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_864_ == 0 {
                    lean_ctor_set_tag(v___x_863_, 1);
                    lean_ctor_set(v___x_863_, 0, v_a_860_);
                    v___x_866_ = v___x_863_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_860_);
                    v___x_866_ = v_reuseFailAlloc_867_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_866_;
            }
            4 => {
                if v_isShared_876_ == 0 {
                    lean_ctor_set(v___x_875_, 0, v_a_872_);
                    v___x_878_ = v___x_875_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_872_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg___boxed(
    mut v_flag_883_: *mut LeanObject,
    mut v_x_884_: *mut LeanObject,
    mut v___y_885_: *mut LeanObject,
    mut v___y_886_: *mut LeanObject,
    mut v___y_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
    mut v___y_889_: *mut LeanObject,
    mut v___y_890_: *mut LeanObject,
    mut v___y_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_892_: u8 = 0;
    let mut v_res_893_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_892_ = (lean_unbox(v_flag_883_) as u8);
    v_res_893_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_boxed_892_, v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
    lean_dec(v___y_890_);
    lean_dec_ref(v___y_889_);
    lean_dec(v___y_888_);
    lean_dec_ref(v___y_887_);
    lean_dec(v___y_886_);
    lean_dec_ref(v___y_885_);
    return v_res_893_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(
    mut v_a_894_: *mut LeanObject,
    mut v_a_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v_declName_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_894_) == 0 {
                    v___x_896_ = l_List_reverse___redArg(v_a_895_);
                    return v___x_896_;
                } else {
                    v_head_897_ = lean_ctor_get(v_a_894_, 0);
                    v_tail_898_ = lean_ctor_get(v_a_894_, 1);
                    v_isSharedCheck_907_ = (!lean_is_exclusive(v_a_894_)) as u8;
                    if v_isSharedCheck_907_ == 0 {
                        v___x_900_ = v_a_894_;
                        v_isShared_901_ = v_isSharedCheck_907_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_898_);
                        lean_inc(v_head_897_);
                        lean_dec(v_a_894_);
                        v___x_900_ = lean_box(0);
                        v_isShared_901_ = v_isSharedCheck_907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_declName_902_ = lean_ctor_get(v_head_897_, 3);
                lean_inc(v_declName_902_);
                lean_dec(v_head_897_);
                if v_isShared_901_ == 0 {
                    lean_ctor_set(v___x_900_, 1, v_a_895_);
                    lean_ctor_set(v___x_900_, 0, v_declName_902_);
                    v___x_904_ = v___x_900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_906_, 0, v_declName_902_);
                    lean_ctor_set(v_reuseFailAlloc_906_, 1, v_a_895_);
                    v___x_904_ = v_reuseFailAlloc_906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_894_ = v_tail_898_;
                v_a_895_ = v___x_904_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(
    mut v_o_911_: *mut LeanObject,
    mut v_k_912_: *mut LeanObject,
    mut v_v_913_: u8,
) -> *mut LeanObject {
    let mut v_map_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_915_: u8 = 0;
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_914_ = lean_ctor_get(v_o_911_, 0);
                v_hasTrace_915_ = lean_ctor_get_uint8(
                    v_o_911_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_929_ = (!lean_is_exclusive(v_o_911_)) as u8;
                if v_isSharedCheck_929_ == 0 {
                    v___x_917_ = v_o_911_;
                    v_isShared_918_ = v_isSharedCheck_929_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_914_);
                    lean_dec(v_o_911_);
                    v___x_917_ = lean_box(0);
                    v_isShared_918_ = v_isSharedCheck_929_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_919_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_919_, 0 as u32, v_v_913_);
                lean_inc(v_k_912_);
                v___x_920_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_912_, v___x_919_, v_map_914_);
                if v_hasTrace_915_ == 0 {
                    v___x_921_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1;
                    v___x_922_ = l_Lean_Name_isPrefixOf(v___x_921_, v_k_912_);
                    lean_dec(v_k_912_);
                    if v_isShared_918_ == 0 {
                        lean_ctor_set(v___x_917_, 0, v___x_920_);
                        v___x_924_ = v___x_917_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_920_);
                        v___x_924_ = v_reuseFailAlloc_925_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_912_);
                    if v_isShared_918_ == 0 {
                        lean_ctor_set(v___x_917_, 0, v___x_920_);
                        v___x_927_ = v___x_917_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_920_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_928_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_915_,
                        );
                        v___x_927_ = v_reuseFailAlloc_928_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_924_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_922_,
                );
                return v___x_924_;
            }
            3 => {
                return v___x_927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(
    mut v_o_930_: *mut LeanObject,
    mut v_k_931_: *mut LeanObject,
    mut v_v_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_933_: u8 = 0;
    let mut v_res_934_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_933_ = (lean_unbox(v_v_932_) as u8);
    v_res_934_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_o_930_, v_k_931_, v_v_boxed_933_);
    return v_res_934_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(
    mut v_opts_935_: *mut LeanObject,
    mut v_opt_936_: *mut LeanObject,
    mut v_val_937_: u8,
) -> *mut LeanObject {
    let mut v_name_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    v_name_938_ = lean_ctor_get(v_opt_936_, 0);
    lean_inc(v_name_938_);
    lean_dec_ref(v_opt_936_);
    v___x_939_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_opts_935_, v_name_938_, v_val_937_);
    return v___x_939_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(
    mut v_opts_940_: *mut LeanObject,
    mut v_opt_941_: *mut LeanObject,
    mut v_val_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_943_: u8 = 0;
    let mut v_res_944_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_943_ = (lean_unbox(v_val_942_) as u8);
    v_res_944_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(
        v_opts_940_,
        v_opt_941_,
        v_val_boxed_943_,
    );
    return v_res_944_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(
    mut v_docCtx_945_: *mut LeanObject,
    mut v_declNames_946_: *mut LeanObject,
    mut v_cacheProofs_947_: u8,
    mut v_as_948_: *mut LeanObject,
    mut v_i_949_: usize,
    mut v_stop_950_: usize,
    mut v_b_951_: *mut LeanObject,
    mut v___y_952_: *mut LeanObject,
    mut v___y_953_: *mut LeanObject,
    mut v___y_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: usize = 0;
    let mut v___x_965_: usize = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_959_ = lean_usize_dec_eq(v_i_949_, v_stop_950_);
                if v___x_959_ == 0 {
                    v___x_960_ = 1;
                    v___x_961_ = lean_array_uget_borrowed(v_as_948_, v_i_949_);
                    lean_inc(v_declNames_946_);
                    lean_inc(v___x_961_);
                    lean_inc_ref(v_docCtx_945_);
                    v___x_962_ = l_Lean_Elab_addNonRec(
                        v_docCtx_945_,
                        v___x_961_,
                        v___x_959_,
                        v_declNames_946_,
                        v_cacheProofs_947_,
                        v___x_959_,
                        v___x_960_,
                        v___y_952_,
                        v___y_953_,
                        v___y_954_,
                        v___y_955_,
                        v___y_956_,
                        v___y_957_,
                    );
                    if lean_obj_tag(v___x_962_) == 0 {
                        v_a_963_ = lean_ctor_get(v___x_962_, 0);
                        lean_inc(v_a_963_);
                        lean_dec_ref_known(v___x_962_, 1);
                        v___x_964_ = 1usize;
                        v___x_965_ = lean_usize_add(v_i_949_, v___x_964_);
                        v_i_949_ = v___x_965_;
                        v_b_951_ = v_a_963_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declNames_946_);
                        lean_dec_ref(v_docCtx_945_);
                        return v___x_962_;
                    }
                } else {
                    lean_dec(v_declNames_946_);
                    lean_dec_ref(v_docCtx_945_);
                    v___x_967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_967_, 0, v_b_951_);
                    return v___x_967_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(
    mut v_docCtx_968_: *mut LeanObject,
    mut v_declNames_969_: *mut LeanObject,
    mut v_cacheProofs_970_: *mut LeanObject,
    mut v_as_971_: *mut LeanObject,
    mut v_i_972_: *mut LeanObject,
    mut v_stop_973_: *mut LeanObject,
    mut v_b_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
    mut v___y_976_: *mut LeanObject,
    mut v___y_977_: *mut LeanObject,
    mut v___y_978_: *mut LeanObject,
    mut v___y_979_: *mut LeanObject,
    mut v___y_980_: *mut LeanObject,
    mut v___y_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cacheProofs_boxed_982_: u8 = 0;
    let mut v_i_boxed_983_: usize = 0;
    let mut v_stop_boxed_984_: usize = 0;
    let mut v_res_985_: *mut LeanObject = core::ptr::null_mut();
    v_cacheProofs_boxed_982_ = (lean_unbox(v_cacheProofs_970_) as u8);
    v_i_boxed_983_ = lean_unbox_usize(v_i_972_);
    lean_dec(v_i_972_);
    v_stop_boxed_984_ = lean_unbox_usize(v_stop_973_);
    lean_dec(v_stop_973_);
    v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_968_, v_declNames_969_, v_cacheProofs_boxed_982_, v_as_971_, v_i_boxed_983_, v_stop_boxed_984_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
    lean_dec(v___y_980_);
    lean_dec_ref(v___y_979_);
    lean_dec(v___y_978_);
    lean_dec_ref(v___y_977_);
    lean_dec(v___y_976_);
    lean_dec_ref(v___y_975_);
    lean_dec_ref(v_as_971_);
    return v_res_985_;
}
pub unsafe fn _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1() -> *mut LeanObject {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2() -> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v___x_988_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once),
        _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1,
    );
    v___x_989_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_989_, 0, v___x_988_);
    return v___x_989_;
}
pub unsafe fn _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3() -> *mut LeanObject {
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_990_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once),
        _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2,
    );
    v___x_991_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_991_, 0, v___x_990_);
    lean_ctor_set(v___x_991_, 1, v___x_990_);
    return v___x_991_;
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefsFromUnary(
    mut v_docCtx_992_: *mut LeanObject,
    mut v_preDefs_993_: *mut LeanObject,
    mut v_preDefsNonrec_994_: *mut LeanObject,
    mut v_unaryPreDefNonRec_995_: *mut LeanObject,
    mut v_cacheProofs_996_: u8,
    mut v_a_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
    mut v_a_999_: *mut LeanObject,
    mut v_a_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
    mut v_a_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1022_: u8 = 0;
    let mut v_inheritedTraceOptions_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v_preDefNonRec_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declNames_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut v_fileName_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1048_: u8 = 0;
    let mut v_inheritedTraceOptions_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: u8 = 0;
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: usize = 0;
    let mut v___x_1076_: usize = 0;
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: usize = 0;
    let mut v___x_1079_: usize = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1081_: u8 = 0;
    let mut v_unused_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_unused_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_1004_ = lean_ctor_get(v_unaryPreDefNonRec_995_, 3);
                v___x_1005_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                v___x_1006_ = lean_unsigned_to_nat(0);
                v___x_1007_ = lean_array_get_borrowed(v___x_1005_, v_preDefs_993_, v___x_1006_);
                v_declName_1008_ = lean_ctor_get(v___x_1007_, 3);
                v___x_1009_ = lean_st_ref_get(v_a_1002_);
                v_fileName_1010_ = lean_ctor_get(v_a_1001_, 0);
                v_fileMap_1011_ = lean_ctor_get(v_a_1001_, 1);
                v_options_1012_ = lean_ctor_get(v_a_1001_, 2);
                v_currRecDepth_1013_ = lean_ctor_get(v_a_1001_, 3);
                v_ref_1014_ = lean_ctor_get(v_a_1001_, 5);
                v_currNamespace_1015_ = lean_ctor_get(v_a_1001_, 6);
                v_openDecls_1016_ = lean_ctor_get(v_a_1001_, 7);
                v_initHeartbeats_1017_ = lean_ctor_get(v_a_1001_, 8);
                v_maxHeartbeats_1018_ = lean_ctor_get(v_a_1001_, 9);
                v_quotContext_1019_ = lean_ctor_get(v_a_1001_, 10);
                v_currMacroScope_1020_ = lean_ctor_get(v_a_1001_, 11);
                v_cancelTk_x3f_1021_ = lean_ctor_get(v_a_1001_, 12);
                v_suppressElabErrors_1022_ = lean_ctor_get_uint8(
                    v_a_1001_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1023_ = lean_ctor_get(v_a_1001_, 13);
                v_env_1024_ = lean_ctor_get(v___x_1009_, 0);
                lean_inc_ref(v_env_1024_);
                lean_dec(v___x_1009_);
                v___f_1025_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0;
                v___x_1026_ = lean_name_eq(v_declName_1004_, v_declName_1008_);
                v_preDefNonRec_1027_ =
                    l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_995_, v___f_1025_);
                v___x_1028_ = lean_array_to_list(v_preDefs_993_);
                v___x_1029_ = lean_box(0);
                v_declNames_1030_ =
                    l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(
                        v___x_1028_,
                        v___x_1029_,
                    );
                v___x_1031_ = l_Lean_allowUnsafeReducibility;
                v___x_1032_ = 1;
                lean_inc_ref(v_options_1012_);
                v___x_1033_ =
                    l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(
                        v_options_1012_,
                        v___x_1031_,
                        v___x_1032_,
                    );
                v___x_1034_ = l_Lean_diagnostics;
                v___x_1035_ =
                    l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(
                        v___x_1033_,
                        v___x_1034_,
                    );
                v___x_1109_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1024_);
                lean_dec_ref(v_env_1024_);
                if v___x_1109_ == 0 {
                    if v___x_1035_ == 0 {
                        v_fileName_1037_ = v_fileName_1010_;
                        v_fileMap_1038_ = v_fileMap_1011_;
                        v_currRecDepth_1039_ = v_currRecDepth_1013_;
                        v_ref_1040_ = v_ref_1014_;
                        v_currNamespace_1041_ = v_currNamespace_1015_;
                        v_openDecls_1042_ = v_openDecls_1016_;
                        v_initHeartbeats_1043_ = v_initHeartbeats_1017_;
                        v_maxHeartbeats_1044_ = v_maxHeartbeats_1018_;
                        v_quotContext_1045_ = v_quotContext_1019_;
                        v_currMacroScope_1046_ = v_currMacroScope_1020_;
                        v_cancelTk_x3f_1047_ = v_cancelTk_x3f_1021_;
                        v_suppressElabErrors_1048_ = v_suppressElabErrors_1022_;
                        v_inheritedTraceOptions_1049_ = v_inheritedTraceOptions_1023_;
                        v___y_1050_ = v_a_1002_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1088_ = v___x_1109_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_1088_ = v___x_1035_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_1051_ = l_Lean_maxRecDepth;
                v___x_1052_ =
                    l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(
                        v___x_1033_,
                        v___x_1051_,
                    );
                lean_inc_ref(v_inheritedTraceOptions_1049_);
                lean_inc(v_cancelTk_x3f_1047_);
                lean_inc(v_currMacroScope_1046_);
                lean_inc(v_quotContext_1045_);
                lean_inc(v_maxHeartbeats_1044_);
                lean_inc(v_initHeartbeats_1043_);
                lean_inc(v_openDecls_1042_);
                lean_inc(v_currNamespace_1041_);
                lean_inc(v_ref_1040_);
                lean_inc(v_currRecDepth_1039_);
                lean_inc_ref(v_fileMap_1038_);
                lean_inc_ref(v_fileName_1037_);
                v___x_1053_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1053_, 0, v_fileName_1037_);
                lean_ctor_set(v___x_1053_, 1, v_fileMap_1038_);
                lean_ctor_set(v___x_1053_, 2, v___x_1033_);
                lean_ctor_set(v___x_1053_, 3, v_currRecDepth_1039_);
                lean_ctor_set(v___x_1053_, 4, v___x_1052_);
                lean_ctor_set(v___x_1053_, 5, v_ref_1040_);
                lean_ctor_set(v___x_1053_, 6, v_currNamespace_1041_);
                lean_ctor_set(v___x_1053_, 7, v_openDecls_1042_);
                lean_ctor_set(v___x_1053_, 8, v_initHeartbeats_1043_);
                lean_ctor_set(v___x_1053_, 9, v_maxHeartbeats_1044_);
                lean_ctor_set(v___x_1053_, 10, v_quotContext_1045_);
                lean_ctor_set(v___x_1053_, 11, v_currMacroScope_1046_);
                lean_ctor_set(v___x_1053_, 12, v_cancelTk_x3f_1047_);
                lean_ctor_set(v___x_1053_, 13, v_inheritedTraceOptions_1049_);
                lean_ctor_set_uint8(
                    v___x_1053_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_1035_,
                );
                lean_ctor_set_uint8(
                    v___x_1053_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1048_,
                );
                if v___x_1026_ == 0 {
                    v_declName_1054_ = lean_ctor_get(v_preDefNonRec_1027_, 3);
                    lean_inc(v_declName_1054_);
                    v___x_1055_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1055_, 0, v_declName_1054_);
                    lean_ctor_set(v___x_1055_, 1, v___x_1029_);
                    v___x_1056_ = lean_box((v___x_1026_) as usize);
                    v___x_1057_ = lean_box((v_cacheProofs_996_) as usize);
                    v___x_1058_ = lean_box((v___x_1026_) as usize);
                    v___x_1059_ = lean_box((v___x_1032_) as usize);
                    lean_inc_ref(v_docCtx_992_);
                    v___x_1060_ = lean_alloc_closure(
                        l_Lean_Elab_addNonRec___boxed as *mut core::ffi::c_void,
                        14,
                        7,
                    );
                    lean_closure_set(v___x_1060_, 0, v_docCtx_992_);
                    lean_closure_set(v___x_1060_, 1, v_preDefNonRec_1027_);
                    lean_closure_set(v___x_1060_, 2, v___x_1056_);
                    lean_closure_set(v___x_1060_, 3, v___x_1055_);
                    lean_closure_set(v___x_1060_, 4, v___x_1057_);
                    lean_closure_set(v___x_1060_, 5, v___x_1058_);
                    lean_closure_set(v___x_1060_, 6, v___x_1059_);
                    v___x_1061_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_1026_, v___x_1060_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v___x_1053_, v___y_1050_);
                    if lean_obj_tag(v___x_1061_) == 0 {
                        v_isSharedCheck_1081_ = (!lean_is_exclusive(v___x_1061_)) as u8;
                        if v_isSharedCheck_1081_ == 0 {
                            v_unused_1082_ = lean_ctor_get(v___x_1061_, 0);
                            lean_dec(v_unused_1082_);
                            v___x_1063_ = v___x_1061_;
                            v_isShared_1064_ = v_isSharedCheck_1081_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1061_);
                            v___x_1063_ = lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1081_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1053_, 14);
                        lean_dec(v_declNames_1030_);
                        lean_dec_ref(v_docCtx_992_);
                        return v___x_1061_;
                    }
                } else {
                    lean_dec(v_declNames_1030_);
                    v_declName_1083_ = lean_ctor_get(v_preDefNonRec_1027_, 3);
                    lean_inc(v_declName_1083_);
                    v___x_1084_ = 0;
                    v___x_1085_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1085_, 0, v_declName_1083_);
                    lean_ctor_set(v___x_1085_, 1, v___x_1029_);
                    v___x_1086_ = l_Lean_Elab_addNonRec(
                        v_docCtx_992_,
                        v_preDefNonRec_1027_,
                        v___x_1084_,
                        v___x_1085_,
                        v_cacheProofs_996_,
                        v___x_1084_,
                        v___x_1032_,
                        v_a_997_,
                        v_a_998_,
                        v_a_999_,
                        v_a_1000_,
                        v___x_1053_,
                        v___y_1050_,
                    );
                    lean_dec_ref_known(v___x_1053_, 14);
                    return v___x_1086_;
                }
            }
            2 => {
                v___x_1065_ = lean_array_get_size(v_preDefsNonrec_994_);
                v___x_1066_ = lean_box(0);
                v___x_1067_ = lean_nat_dec_lt(v___x_1006_, v___x_1065_);
                if v___x_1067_ == 0 {
                    lean_dec_ref_known(v___x_1053_, 14);
                    lean_dec(v_declNames_1030_);
                    lean_dec_ref(v_docCtx_992_);
                    if v_isShared_1064_ == 0 {
                        lean_ctor_set(v___x_1063_, 0, v___x_1066_);
                        v___x_1069_ = v___x_1063_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
                        v___x_1069_ = v_reuseFailAlloc_1070_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1071_ = lean_nat_dec_le(v___x_1065_, v___x_1065_);
                    if v___x_1071_ == 0 {
                        if v___x_1067_ == 0 {
                            lean_dec_ref_known(v___x_1053_, 14);
                            lean_dec(v_declNames_1030_);
                            lean_dec_ref(v_docCtx_992_);
                            if v_isShared_1064_ == 0 {
                                lean_ctor_set(v___x_1063_, 0, v___x_1066_);
                                v___x_1073_ = v___x_1063_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1066_);
                                v___x_1073_ = v_reuseFailAlloc_1074_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1063_);
                            v___x_1075_ = 0usize;
                            v___x_1076_ = lean_usize_of_nat(v___x_1065_);
                            v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_992_, v_declNames_1030_, v_cacheProofs_996_, v_preDefsNonrec_994_, v___x_1075_, v___x_1076_, v___x_1066_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v___x_1053_, v___y_1050_);
                            lean_dec_ref_known(v___x_1053_, 14);
                            return v___x_1077_;
                        }
                    } else {
                        lean_del_object(v___x_1063_);
                        v___x_1078_ = 0usize;
                        v___x_1079_ = lean_usize_of_nat(v___x_1065_);
                        v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_992_, v_declNames_1030_, v_cacheProofs_996_, v_preDefsNonrec_994_, v___x_1078_, v___x_1079_, v___x_1066_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v___x_1053_, v___y_1050_);
                        lean_dec_ref_known(v___x_1053_, 14);
                        return v___x_1080_;
                    }
                }
            }
            3 => {
                return v___x_1069_;
            }
            4 => {
                return v___x_1073_;
            }
            5 => {
                if v___y_1088_ == 0 {
                    v___x_1089_ = lean_st_ref_take(v_a_1002_);
                    v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
                    v_nextMacroScope_1091_ = lean_ctor_get(v___x_1089_, 1);
                    v_ngen_1092_ = lean_ctor_get(v___x_1089_, 2);
                    v_auxDeclNGen_1093_ = lean_ctor_get(v___x_1089_, 3);
                    v_traceState_1094_ = lean_ctor_get(v___x_1089_, 4);
                    v_messages_1095_ = lean_ctor_get(v___x_1089_, 6);
                    v_infoState_1096_ = lean_ctor_get(v___x_1089_, 7);
                    v_snapshotTasks_1097_ = lean_ctor_get(v___x_1089_, 8);
                    v_isSharedCheck_1107_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                    if v_isSharedCheck_1107_ == 0 {
                        v_unused_1108_ = lean_ctor_get(v___x_1089_, 5);
                        lean_dec(v_unused_1108_);
                        v___x_1099_ = v___x_1089_;
                        v_isShared_1100_ = v_isSharedCheck_1107_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1097_);
                        lean_inc(v_infoState_1096_);
                        lean_inc(v_messages_1095_);
                        lean_inc(v_traceState_1094_);
                        lean_inc(v_auxDeclNGen_1093_);
                        lean_inc(v_ngen_1092_);
                        lean_inc(v_nextMacroScope_1091_);
                        lean_inc(v_env_1090_);
                        lean_dec(v___x_1089_);
                        v___x_1099_ = lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1107_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_fileName_1037_ = v_fileName_1010_;
                    v_fileMap_1038_ = v_fileMap_1011_;
                    v_currRecDepth_1039_ = v_currRecDepth_1013_;
                    v_ref_1040_ = v_ref_1014_;
                    v_currNamespace_1041_ = v_currNamespace_1015_;
                    v_openDecls_1042_ = v_openDecls_1016_;
                    v_initHeartbeats_1043_ = v_initHeartbeats_1017_;
                    v_maxHeartbeats_1044_ = v_maxHeartbeats_1018_;
                    v_quotContext_1045_ = v_quotContext_1019_;
                    v_currMacroScope_1046_ = v_currMacroScope_1020_;
                    v_cancelTk_x3f_1047_ = v_cancelTk_x3f_1021_;
                    v_suppressElabErrors_1048_ = v_suppressElabErrors_1022_;
                    v_inheritedTraceOptions_1049_ = v_inheritedTraceOptions_1023_;
                    v___y_1050_ = v_a_1002_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_1101_ = l_Lean_Kernel_enableDiag(v_env_1090_, v___x_1035_);
                v___x_1102_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once
                    ),
                    _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3,
                );
                if v_isShared_1100_ == 0 {
                    lean_ctor_set(v___x_1099_, 5, v___x_1102_);
                    lean_ctor_set(v___x_1099_, 0, v___x_1101_);
                    v___x_1104_ = v___x_1099_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1101_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_nextMacroScope_1091_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_ngen_1092_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_auxDeclNGen_1093_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_traceState_1094_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 5, v___x_1102_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 6, v_messages_1095_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 7, v_infoState_1096_);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 8, v_snapshotTasks_1097_);
                    v___x_1104_ = v_reuseFailAlloc_1106_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1105_ = lean_st_ref_set(v_a_1002_, v___x_1104_);
                v_fileName_1037_ = v_fileName_1010_;
                v_fileMap_1038_ = v_fileMap_1011_;
                v_currRecDepth_1039_ = v_currRecDepth_1013_;
                v_ref_1040_ = v_ref_1014_;
                v_currNamespace_1041_ = v_currNamespace_1015_;
                v_openDecls_1042_ = v_openDecls_1016_;
                v_initHeartbeats_1043_ = v_initHeartbeats_1017_;
                v_maxHeartbeats_1044_ = v_maxHeartbeats_1018_;
                v_quotContext_1045_ = v_quotContext_1019_;
                v_currMacroScope_1046_ = v_currMacroScope_1020_;
                v_cancelTk_x3f_1047_ = v_cancelTk_x3f_1021_;
                v_suppressElabErrors_1048_ = v_suppressElabErrors_1022_;
                v_inheritedTraceOptions_1049_ = v_inheritedTraceOptions_1023_;
                v___y_1050_ = v_a_1002_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(
    mut v_docCtx_1110_: *mut LeanObject,
    mut v_preDefs_1111_: *mut LeanObject,
    mut v_preDefsNonrec_1112_: *mut LeanObject,
    mut v_unaryPreDefNonRec_1113_: *mut LeanObject,
    mut v_cacheProofs_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cacheProofs_boxed_1122_: u8 = 0;
    let mut v_res_1123_: *mut LeanObject = core::ptr::null_mut();
    v_cacheProofs_boxed_1122_ = (lean_unbox(v_cacheProofs_1114_) as u8);
    v_res_1123_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(
        v_docCtx_1110_,
        v_preDefs_1111_,
        v_preDefsNonrec_1112_,
        v_unaryPreDefNonRec_1113_,
        v_cacheProofs_boxed_1122_,
        v_a_1115_,
        v_a_1116_,
        v_a_1117_,
        v_a_1118_,
        v_a_1119_,
        v_a_1120_,
    );
    lean_dec(v_a_1120_);
    lean_dec_ref(v_a_1119_);
    lean_dec(v_a_1118_);
    lean_dec_ref(v_a_1117_);
    lean_dec(v_a_1116_);
    lean_dec_ref(v_a_1115_);
    lean_dec_ref(v_preDefsNonrec_1112_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(
    mut v_flag_1124_: u8,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_1124_, v___y_1130_);
    return v___x_1132_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(
    mut v_flag_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_1141_: u8 = 0;
    let mut v_res_1142_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_1141_ = (lean_unbox(v_flag_1133_) as u8);
    v_res_1142_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_1141_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
    lean_dec(v___y_1139_);
    lean_dec_ref(v___y_1138_);
    lean_dec(v___y_1137_);
    lean_dec_ref(v___y_1136_);
    lean_dec(v___y_1135_);
    lean_dec_ref(v___y_1134_);
    return v_res_1142_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(
    mut v_00_u03b1_1143_: *mut LeanObject,
    mut v_flag_1144_: u8,
    mut v_x_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
    mut v___y_1149_: *mut LeanObject,
    mut v___y_1150_: *mut LeanObject,
    mut v___y_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_1144_, v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(
    mut v_00_u03b1_1154_: *mut LeanObject,
    mut v_flag_1155_: *mut LeanObject,
    mut v_x_1156_: *mut LeanObject,
    mut v___y_1157_: *mut LeanObject,
    mut v___y_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
    mut v___y_1160_: *mut LeanObject,
    mut v___y_1161_: *mut LeanObject,
    mut v___y_1162_: *mut LeanObject,
    mut v___y_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_1164_: u8 = 0;
    let mut v_res_1165_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_1164_ = (lean_unbox(v_flag_1155_) as u8);
    v_res_1165_ =
        l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(
            v_00_u03b1_1154_,
            v_flag_boxed_1164_,
            v_x_1156_,
            v___y_1157_,
            v___y_1158_,
            v___y_1159_,
            v___y_1160_,
            v___y_1161_,
            v___y_1162_,
        );
    lean_dec(v___y_1162_);
    lean_dec_ref(v___y_1161_);
    lean_dec(v___y_1160_);
    lean_dec_ref(v___y_1159_);
    lean_dec(v___y_1158_);
    lean_dec_ref(v___y_1157_);
    return v_res_1165_;
}
pub unsafe fn l_Lean_Elab_Mutual_cleanPreDef(
    mut v_preDef_1166_: *mut LeanObject,
    mut v_cacheProofs_1167_: u8,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
    mut v_a_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    v___x_1173_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_1166_, v_a_1170_, v_a_1171_);
    if lean_obj_tag(v___x_1173_) == 0 {
        let mut v_a_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
        lean_inc(v_a_1174_);
        lean_dec_ref_known(v___x_1173_, 1);
        v___x_1175_ = l_Lean_Elab_abstractNestedProofs(
            v_a_1174_,
            v_cacheProofs_1167_,
            v_a_1168_,
            v_a_1169_,
            v_a_1170_,
            v_a_1171_,
        );
        return v___x_1175_;
    } else {
        return v___x_1173_;
    }
}
pub unsafe fn l_Lean_Elab_Mutual_cleanPreDef___boxed(
    mut v_preDef_1176_: *mut LeanObject,
    mut v_cacheProofs_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
    mut v_a_1179_: *mut LeanObject,
    mut v_a_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cacheProofs_boxed_1183_: u8 = 0;
    let mut v_res_1184_: *mut LeanObject = core::ptr::null_mut();
    v_cacheProofs_boxed_1183_ = (lean_unbox(v_cacheProofs_1177_) as u8);
    v_res_1184_ = l_Lean_Elab_Mutual_cleanPreDef(
        v_preDef_1176_,
        v_cacheProofs_boxed_1183_,
        v_a_1178_,
        v_a_1179_,
        v_a_1180_,
        v_a_1181_,
    );
    lean_dec(v_a_1181_);
    lean_dec_ref(v_a_1180_);
    lean_dec(v_a_1179_);
    lean_dec_ref(v_a_1178_);
    return v_res_1184_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(
    mut v_as_1185_: *mut LeanObject,
    mut v_sz_1186_: usize,
    mut v_i_1187_: usize,
    mut v_b_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
                if v___x_1192_ == 0 {
                    v___x_1193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1193_, 0, v_b_1188_);
                    return v___x_1193_;
                } else {
                    v_a_1194_ = lean_array_uget_borrowed(v_as_1185_, v_i_1187_);
                    v_declName_1195_ = lean_ctor_get(v_a_1194_, 3);
                    lean_inc(v_declName_1195_);
                    v___x_1196_ = l_Lean_enableRealizationsForConst(
                        v_declName_1195_,
                        v___y_1189_,
                        v___y_1190_,
                    );
                    if lean_obj_tag(v___x_1196_) == 0 {
                        lean_dec_ref_known(v___x_1196_, 1);
                        v___x_1197_ = lean_box(0);
                        v___x_1198_ = 1usize;
                        v___x_1199_ = lean_usize_add(v_i_1187_, v___x_1198_);
                        v_i_1187_ = v___x_1199_;
                        v_b_1188_ = v___x_1197_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1196_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(
    mut v_as_1201_: *mut LeanObject,
    mut v_sz_1202_: *mut LeanObject,
    mut v_i_1203_: *mut LeanObject,
    mut v_b_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1208_: usize = 0;
    let mut v_i_boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1208_ = lean_unbox_usize(v_sz_1202_);
    lean_dec(v_sz_1202_);
    v_i_boxed_1209_ = lean_unbox_usize(v_i_1203_);
    lean_dec(v_i_1203_);
    v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_1201_, v_sz_boxed_1208_, v_i_boxed_1209_, v_b_1204_, v___y_1205_, v___y_1206_);
    lean_dec(v___y_1206_);
    lean_dec_ref(v___y_1205_);
    lean_dec_ref(v_as_1201_);
    return v_res_1210_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(
    mut v_as_1211_: *mut LeanObject,
    mut v_sz_1212_: usize,
    mut v_i_1213_: usize,
    mut v_b_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: usize = 0;
    let mut v___x_1227_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ = lean_usize_dec_lt(v_i_1213_, v_sz_1212_);
                if v___x_1220_ == 0 {
                    v___x_1221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1221_, 0, v_b_1214_);
                    return v___x_1221_;
                } else {
                    v_a_1222_ = lean_array_uget_borrowed(v_as_1211_, v_i_1213_);
                    v_declName_1223_ = lean_ctor_get(v_a_1222_, 3);
                    lean_inc(v_declName_1223_);
                    v___x_1224_ = l_Lean_Meta_saveEqnAffectingOptions(
                        v_declName_1223_,
                        v___y_1215_,
                        v___y_1216_,
                        v___y_1217_,
                        v___y_1218_,
                    );
                    if lean_obj_tag(v___x_1224_) == 0 {
                        lean_dec_ref_known(v___x_1224_, 1);
                        v___x_1225_ = lean_box(0);
                        v___x_1226_ = 1usize;
                        v___x_1227_ = lean_usize_add(v_i_1213_, v___x_1226_);
                        v_i_1213_ = v___x_1227_;
                        v_b_1214_ = v___x_1225_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1224_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(
    mut v_as_1229_: *mut LeanObject,
    mut v_sz_1230_: *mut LeanObject,
    mut v_i_1231_: *mut LeanObject,
    mut v_b_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1238_: usize = 0;
    let mut v_i_boxed_1239_: usize = 0;
    let mut v_res_1240_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1230_);
    lean_dec(v_sz_1230_);
    v_i_boxed_1239_ = lean_unbox_usize(v_i_1231_);
    lean_dec(v_i_1231_);
    v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_1229_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
    lean_dec(v___y_1236_);
    lean_dec_ref(v___y_1235_);
    lean_dec(v___y_1234_);
    lean_dec_ref(v___y_1233_);
    lean_dec_ref(v_as_1229_);
    return v_res_1240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(
    mut v_as_1241_: *mut LeanObject,
    mut v_sz_1242_: usize,
    mut v_i_1243_: usize,
    mut v_b_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1252_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
                if v___x_1252_ == 0 {
                    v___x_1253_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1253_, 0, v_b_1244_);
                    return v___x_1253_;
                } else {
                    v_a_1254_ = lean_array_uget_borrowed(v_as_1241_, v_i_1243_);
                    v___x_1255_ = lean_unsigned_to_nat(1);
                    v___x_1256_ = lean_mk_empty_array_with_capacity(v___x_1255_);
                    lean_inc(v_a_1254_);
                    v___x_1257_ = lean_array_push(v___x_1256_, v_a_1254_);
                    v___x_1258_ = 1;
                    v___x_1259_ = l_Lean_Elab_applyAttributesOf(
                        v___x_1257_,
                        v___x_1258_,
                        v___y_1245_,
                        v___y_1246_,
                        v___y_1247_,
                        v___y_1248_,
                        v___y_1249_,
                        v___y_1250_,
                    );
                    lean_dec_ref(v___x_1257_);
                    if lean_obj_tag(v___x_1259_) == 0 {
                        lean_dec_ref_known(v___x_1259_, 1);
                        v___x_1260_ = lean_box(0);
                        v___x_1261_ = 1usize;
                        v___x_1262_ = lean_usize_add(v_i_1243_, v___x_1261_);
                        v_i_1243_ = v___x_1262_;
                        v_b_1244_ = v___x_1260_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1259_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(
    mut v_as_1264_: *mut LeanObject,
    mut v_sz_1265_: *mut LeanObject,
    mut v_i_1266_: *mut LeanObject,
    mut v_b_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1275_: usize = 0;
    let mut v_i_boxed_1276_: usize = 0;
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1275_ = lean_unbox_usize(v_sz_1265_);
    lean_dec(v_sz_1265_);
    v_i_boxed_1276_ = lean_unbox_usize(v_i_1266_);
    lean_dec(v_i_1266_);
    v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_1264_, v_sz_boxed_1275_, v_i_boxed_1276_, v_b_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
    lean_dec(v___y_1273_);
    lean_dec_ref(v___y_1272_);
    lean_dec(v___y_1271_);
    lean_dec_ref(v___y_1270_);
    lean_dec(v___y_1269_);
    lean_dec_ref(v___y_1268_);
    lean_dec_ref(v_as_1264_);
    return v_res_1277_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once),
        _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2,
    );
    v___x_1279_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1279_, 0, v___x_1278_);
    lean_ctor_set(v___x_1279_, 1, v___x_1278_);
    lean_ctor_set(v___x_1279_, 2, v___x_1278_);
    lean_ctor_set(v___x_1279_, 3, v___x_1278_);
    lean_ctor_set(v___x_1279_, 4, v___x_1278_);
    lean_ctor_set(v___x_1279_, 5, v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(
    mut v_declName_1280_: *mut LeanObject,
    mut v_s_1281_: u8,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_unused_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1322_: u8 = 0;
    let mut v_unused_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = lean_st_ref_take(v___y_1283_);
                v_env_1286_ = lean_ctor_get(v___x_1285_, 0);
                v_nextMacroScope_1287_ = lean_ctor_get(v___x_1285_, 1);
                v_ngen_1288_ = lean_ctor_get(v___x_1285_, 2);
                v_auxDeclNGen_1289_ = lean_ctor_get(v___x_1285_, 3);
                v_traceState_1290_ = lean_ctor_get(v___x_1285_, 4);
                v_messages_1291_ = lean_ctor_get(v___x_1285_, 6);
                v_infoState_1292_ = lean_ctor_get(v___x_1285_, 7);
                v_snapshotTasks_1293_ = lean_ctor_get(v___x_1285_, 8);
                v_isSharedCheck_1322_ = (!lean_is_exclusive(v___x_1285_)) as u8;
                if v_isSharedCheck_1322_ == 0 {
                    v_unused_1323_ = lean_ctor_get(v___x_1285_, 5);
                    lean_dec(v_unused_1323_);
                    v___x_1295_ = v___x_1285_;
                    v_isShared_1296_ = v_isSharedCheck_1322_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1293_);
                    lean_inc(v_infoState_1292_);
                    lean_inc(v_messages_1291_);
                    lean_inc(v_traceState_1290_);
                    lean_inc(v_auxDeclNGen_1289_);
                    lean_inc(v_ngen_1288_);
                    lean_inc(v_nextMacroScope_1287_);
                    lean_inc(v_env_1286_);
                    lean_dec(v___x_1285_);
                    v___x_1295_ = lean_box(0);
                    v_isShared_1296_ = v_isSharedCheck_1322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1297_ = 0;
                v___x_1298_ = lean_box(0);
                v___x_1299_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_1286_,
                    v_declName_1280_,
                    v_s_1281_,
                    v___x_1297_,
                    v___x_1298_,
                );
                v___x_1300_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once
                    ),
                    _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3,
                );
                if v_isShared_1296_ == 0 {
                    lean_ctor_set(v___x_1295_, 5, v___x_1300_);
                    lean_ctor_set(v___x_1295_, 0, v___x_1299_);
                    v___x_1302_ = v___x_1295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1299_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1287_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1288_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1289_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1290_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 5, v___x_1300_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_messages_1291_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1293_);
                    v___x_1302_ = v_reuseFailAlloc_1321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1303_ = lean_st_ref_set(v___y_1283_, v___x_1302_);
                v___x_1304_ = lean_st_ref_take(v___y_1282_);
                v_mctx_1305_ = lean_ctor_get(v___x_1304_, 0);
                v_zetaDeltaFVarIds_1306_ = lean_ctor_get(v___x_1304_, 2);
                v_postponed_1307_ = lean_ctor_get(v___x_1304_, 3);
                v_diag_1308_ = lean_ctor_get(v___x_1304_, 4);
                v_isSharedCheck_1319_ = (!lean_is_exclusive(v___x_1304_)) as u8;
                if v_isSharedCheck_1319_ == 0 {
                    v_unused_1320_ = lean_ctor_get(v___x_1304_, 1);
                    lean_dec(v_unused_1320_);
                    v___x_1310_ = v___x_1304_;
                    v_isShared_1311_ = v_isSharedCheck_1319_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1308_);
                    lean_inc(v_postponed_1307_);
                    lean_inc(v_zetaDeltaFVarIds_1306_);
                    lean_inc(v_mctx_1305_);
                    lean_dec(v___x_1304_);
                    v___x_1310_ = lean_box(0);
                    v_isShared_1311_ = v_isSharedCheck_1319_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1312_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
                if v_isShared_1311_ == 0 {
                    lean_ctor_set(v___x_1310_, 1, v___x_1312_);
                    v___x_1314_ = v___x_1310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_mctx_1305_);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1312_);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_zetaDeltaFVarIds_1306_);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_postponed_1307_);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_diag_1308_);
                    v___x_1314_ = v_reuseFailAlloc_1318_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1315_ = lean_st_ref_set(v___y_1282_, v___x_1314_);
                v___x_1316_ = lean_box(0);
                v___x_1317_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v___x_1316_);
                return v___x_1317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(
    mut v_declName_1324_: *mut LeanObject,
    mut v_s_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1329_ = (lean_unbox(v_s_1325_) as u8);
    v_res_1330_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_1324_, v_s_boxed_1329_, v___y_1326_, v___y_1327_);
    lean_dec(v___y_1327_);
    lean_dec(v___y_1326_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(
    mut v_declName_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: u8 = 0;
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = 2;
    v___x_1340_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_1331_, v___x_1339_, v___y_1335_, v___y_1337_);
    return v___x_1340_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(
    mut v_declName_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1349_: *mut LeanObject = core::ptr::null_mut();
    v_res_1349_ =
        l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(
            v_declName_1341_,
            v___y_1342_,
            v___y_1343_,
            v___y_1344_,
            v___y_1345_,
            v___y_1346_,
            v___y_1347_,
        );
    lean_dec(v___y_1347_);
    lean_dec_ref(v___y_1346_);
    lean_dec(v___y_1345_);
    lean_dec_ref(v___y_1344_);
    lean_dec(v___y_1343_);
    lean_dec_ref(v___y_1342_);
    return v_res_1349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(
    mut v_as_1362_: *mut LeanObject,
    mut v_i_1363_: usize,
    mut v_stop_1364_: usize,
) -> u8 {
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: usize = 0;
    let mut v___x_1378_: usize = 0;
    let mut v___x_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1365_ = lean_usize_dec_eq(v_i_1363_, v_stop_1364_);
                if v___x_1365_ == 0 {
                    v___x_1366_ = lean_array_uget_borrowed(v_as_1362_, v_i_1363_);
                    v_name_1367_ = lean_ctor_get(v___x_1366_, 0);
                    v___x_1368_ = 1;
                    v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1;
                    v___x_1370_ = lean_name_eq(v_name_1367_, v___x_1369_);
                    if v___x_1370_ == 0 {
                        v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3;
                        v___x_1372_ = lean_name_eq(v_name_1367_, v___x_1371_);
                        if v___x_1372_ == 0 {
                            v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5;
                            v___x_1374_ = lean_name_eq(v_name_1367_, v___x_1373_);
                            if v___x_1374_ == 0 {
                                v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7;
                                v___x_1376_ = lean_name_eq(v_name_1367_, v___x_1375_);
                                if v___x_1376_ == 0 {
                                    v___x_1377_ = 1usize;
                                    v___x_1378_ = lean_usize_add(v_i_1363_, v___x_1377_);
                                    v_i_1363_ = v___x_1378_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_1368_;
                                }
                            } else {
                                return v___x_1368_;
                            }
                        } else {
                            return v___x_1368_;
                        }
                    } else {
                        return v___x_1368_;
                    }
                } else {
                    v___x_1380_ = 0;
                    return v___x_1380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(
    mut v_as_1381_: *mut LeanObject,
    mut v_i_1382_: *mut LeanObject,
    mut v_stop_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1384_: usize = 0;
    let mut v_stop_boxed_1385_: usize = 0;
    let mut v_res_1386_: u8 = 0;
    let mut v_r_1387_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1384_ = lean_unbox_usize(v_i_1382_);
    lean_dec(v_i_1382_);
    v_stop_boxed_1385_ = lean_unbox_usize(v_stop_1383_);
    lean_dec(v_stop_1383_);
    v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_as_1381_, v_i_boxed_1384_, v_stop_boxed_1385_);
    lean_dec_ref(v_as_1381_);
    v_r_1387_ = lean_box((v_res_1386_) as usize);
    return v_r_1387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(
    mut v_as_1388_: *mut LeanObject,
    mut v_sz_1389_: usize,
    mut v_i_1390_: usize,
    mut v_b_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
    mut v___y_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: usize = 0;
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1407_: u8 = 0;
    let mut v_modifiers_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: u8 = 0;
    let mut v_declName_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_attrs_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: usize = 0;
    let mut v___x_1420_: usize = 0;
    let mut v___x_1421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1404_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
                if v___x_1404_ == 0 {
                    v___x_1405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1405_, 0, v_b_1391_);
                    return v___x_1405_;
                } else {
                    v_a_1406_ = lean_array_uget_borrowed(v_as_1388_, v_i_1390_);
                    v_kind_1407_ = lean_ctor_get_uint8(
                        v_a_1406_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    );
                    v_modifiers_1408_ = lean_ctor_get(v_a_1406_, 2);
                    v___x_1409_ = lean_box(0);
                    v___x_1414_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1407_);
                    if v___x_1414_ == 0 {
                        v_attrs_1415_ = lean_ctor_get(v_modifiers_1408_, 2);
                        v___x_1416_ = lean_unsigned_to_nat(0);
                        v___x_1417_ = lean_array_get_size(v_attrs_1415_);
                        v___x_1418_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
                        if v___x_1418_ == 0 {
                            v___y_1411_ = v___x_1414_;
                            state = 2;
                            continue;
                        } else {
                            if v___x_1418_ == 0 {
                                v___y_1411_ = v___x_1414_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1419_ = 0usize;
                                v___x_1420_ = lean_usize_of_nat(v___x_1417_);
                                v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_attrs_1415_, v___x_1419_, v___x_1420_);
                                v___y_1411_ = v___x_1421_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_a_1400_ = v___x_1409_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1401_ = 1usize;
                v___x_1402_ = lean_usize_add(v_i_1390_, v___x_1401_);
                v_i_1390_ = v___x_1402_;
                v_b_1391_ = v_a_1400_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1411_ == 0 {
                    v_declName_1412_ = lean_ctor_get(v_a_1406_, 3);
                    lean_inc(v_declName_1412_);
                    v___x_1413_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_1412_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
                    if lean_obj_tag(v___x_1413_) == 0 {
                        lean_dec_ref_known(v___x_1413_, 1);
                        v_a_1400_ = v___x_1409_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_1413_;
                    }
                } else {
                    v_a_1400_ = v___x_1409_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(
    mut v_as_1422_: *mut LeanObject,
    mut v_sz_1423_: *mut LeanObject,
    mut v_i_1424_: *mut LeanObject,
    mut v_b_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1433_: usize = 0;
    let mut v_i_boxed_1434_: usize = 0;
    let mut v_res_1435_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1423_);
    lean_dec(v_sz_1423_);
    v_i_boxed_1434_ = lean_unbox_usize(v_i_1424_);
    lean_dec(v_i_1424_);
    v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_1422_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
    lean_dec(v___y_1431_);
    lean_dec_ref(v___y_1430_);
    lean_dec(v___y_1429_);
    lean_dec_ref(v___y_1428_);
    lean_dec(v___y_1427_);
    lean_dec_ref(v___y_1426_);
    lean_dec_ref(v_as_1422_);
    return v_res_1435_;
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefAttributes(
    mut v_preDefs_1436_: *mut LeanObject,
    mut v_a_1437_: *mut LeanObject,
    mut v_a_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
    mut v_a_1441_: *mut LeanObject,
    mut v_a_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1450_: usize = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut v_unused_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1444_ = lean_box(0);
                v_sz_1445_ = lean_array_size(v_preDefs_1436_);
                v___x_1446_ = 0usize;
                v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_1436_, v_sz_1445_, v___x_1446_, v___x_1444_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
                if lean_obj_tag(v___x_1447_) == 0 {
                    lean_dec_ref_known(v___x_1447_, 1);
                    v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_1436_, v_sz_1445_, v___x_1446_, v___x_1444_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
                    if lean_obj_tag(v___x_1448_) == 0 {
                        lean_dec_ref_known(v___x_1448_, 1);
                        lean_inc_ref(v_preDefs_1436_);
                        v___x_1449_ = l_Array_reverse___redArg(v_preDefs_1436_);
                        v_sz_1450_ = lean_array_size(v___x_1449_);
                        v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_1449_, v_sz_1450_, v___x_1446_, v___x_1444_, v_a_1441_, v_a_1442_);
                        lean_dec_ref(v___x_1449_);
                        if lean_obj_tag(v___x_1451_) == 0 {
                            lean_dec_ref_known(v___x_1451_, 1);
                            v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_1436_, v_sz_1445_, v___x_1446_, v___x_1444_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
                            lean_dec_ref(v_preDefs_1436_);
                            if lean_obj_tag(v___x_1452_) == 0 {
                                v_isSharedCheck_1459_ = (!lean_is_exclusive(v___x_1452_)) as u8;
                                if v_isSharedCheck_1459_ == 0 {
                                    v_unused_1460_ = lean_ctor_get(v___x_1452_, 0);
                                    lean_dec(v_unused_1460_);
                                    v___x_1454_ = v___x_1452_;
                                    v_isShared_1455_ = v_isSharedCheck_1459_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_1452_);
                                    v___x_1454_ = lean_box(0);
                                    v_isShared_1455_ = v_isSharedCheck_1459_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                return v___x_1452_;
                            }
                        } else {
                            lean_dec_ref(v_preDefs_1436_);
                            return v___x_1451_;
                        }
                    } else {
                        lean_dec_ref(v_preDefs_1436_);
                        return v___x_1448_;
                    }
                } else {
                    lean_dec_ref(v_preDefs_1436_);
                    return v___x_1447_;
                }
            }
            1 => {
                if v_isShared_1455_ == 0 {
                    lean_ctor_set(v___x_1454_, 0, v___x_1444_);
                    v___x_1457_ = v___x_1454_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1444_);
                    v___x_1457_ = v_reuseFailAlloc_1458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Mutual_addPreDefAttributes___boxed(
    mut v_preDefs_1461_: *mut LeanObject,
    mut v_a_1462_: *mut LeanObject,
    mut v_a_1463_: *mut LeanObject,
    mut v_a_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
    mut v_a_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v_a_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1469_: *mut LeanObject = core::ptr::null_mut();
    v_res_1469_ = l_Lean_Elab_Mutual_addPreDefAttributes(
        v_preDefs_1461_,
        v_a_1462_,
        v_a_1463_,
        v_a_1464_,
        v_a_1465_,
        v_a_1466_,
        v_a_1467_,
    );
    lean_dec(v_a_1467_);
    lean_dec_ref(v_a_1466_);
    lean_dec(v_a_1465_);
    lean_dec_ref(v_a_1464_);
    lean_dec(v_a_1463_);
    lean_dec_ref(v_a_1462_);
    return v_res_1469_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(
    mut v_declName_1470_: *mut LeanObject,
    mut v_s_1471_: u8,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_1470_, v_s_1471_, v___y_1475_, v___y_1477_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(
    mut v_declName_1480_: *mut LeanObject,
    mut v_s_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1489_: u8 = 0;
    let mut v_res_1490_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1489_ = (lean_unbox(v_s_1481_) as u8);
    v_res_1490_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_1480_, v_s_boxed_1489_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
    lean_dec(v___y_1487_);
    lean_dec_ref(v___y_1486_);
    lean_dec(v___y_1485_);
    lean_dec_ref(v___y_1484_);
    lean_dec(v___y_1483_);
    lean_dec_ref(v___y_1482_);
    return v_res_1490_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(
    mut v_as_1491_: *mut LeanObject,
    mut v_sz_1492_: usize,
    mut v_i_1493_: usize,
    mut v_b_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_1491_, v_sz_1492_, v_i_1493_, v_b_1494_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
    return v___x_1502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(
    mut v_as_1503_: *mut LeanObject,
    mut v_sz_1504_: *mut LeanObject,
    mut v_i_1505_: *mut LeanObject,
    mut v_b_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1514_: usize = 0;
    let mut v_i_boxed_1515_: usize = 0;
    let mut v_res_1516_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1514_ = lean_unbox_usize(v_sz_1504_);
    lean_dec(v_sz_1504_);
    v_i_boxed_1515_ = lean_unbox_usize(v_i_1505_);
    lean_dec(v_i_1505_);
    v_res_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_1503_, v_sz_boxed_1514_, v_i_boxed_1515_, v_b_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
    lean_dec(v___y_1512_);
    lean_dec_ref(v___y_1511_);
    lean_dec(v___y_1510_);
    lean_dec_ref(v___y_1509_);
    lean_dec(v___y_1508_);
    lean_dec_ref(v___y_1507_);
    lean_dec_ref(v_as_1503_);
    return v_res_1516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(
    mut v_as_1517_: *mut LeanObject,
    mut v_sz_1518_: usize,
    mut v_i_1519_: usize,
    mut v_b_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
    mut v___y_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_1517_, v_sz_1518_, v_i_1519_, v_b_1520_, v___y_1525_, v___y_1526_);
    return v___x_1528_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(
    mut v_as_1529_: *mut LeanObject,
    mut v_sz_1530_: *mut LeanObject,
    mut v_i_1531_: *mut LeanObject,
    mut v_b_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1540_: usize = 0;
    let mut v_i_boxed_1541_: usize = 0;
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1540_ = lean_unbox_usize(v_sz_1530_);
    lean_dec(v_sz_1530_);
    v_i_boxed_1541_ = lean_unbox_usize(v_i_1531_);
    lean_dec(v_i_1531_);
    v_res_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_1529_, v_sz_boxed_1540_, v_i_boxed_1541_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
    lean_dec(v___y_1538_);
    lean_dec_ref(v___y_1537_);
    lean_dec(v___y_1536_);
    lean_dec_ref(v___y_1535_);
    lean_dec(v___y_1534_);
    lean_dec_ref(v___y_1533_);
    lean_dec_ref(v_as_1529_);
    return v_res_1542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Mutual(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_Mutual(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Mutual(builtin);
}
