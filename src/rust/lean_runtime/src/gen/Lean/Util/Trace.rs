// Lean compiler output
// Module: Lean.Util.Trace
// Imports: Lean.Elab.Exception Lean.Log
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_instMonadExceptOf___redArg___lam__1, l_StateT_instMonadExceptOf___redArg___lam__3,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
};
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Hashable::l_instHashableProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::String::Hashable::l_String_instHashableRaw_hash___boxed;
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringFormat___lam__0;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getId, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef, l_MonadExcept_ofExcept___redArg,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_String_toRawSubstring_x27,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqRaw___boxed,
    l_instMonadExceptOfMonadExceptOf___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IO::{
    l_BaseIO_toIO___boxed, l_IO_getNumHeartbeats___boxed, l_IO_monoNanosNow___boxed,
    l_IO_println___boxed, l_instMonadExceptOfEIO,
};
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_KVMap_instValueBool, l_Lean_KVMap_instValueNat, l_Lean_KVMap_instValueString,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Option_get___redArg, l_Lean_Option_get_x3f___redArg, lean_register_option,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_forIn___redArg,
    l_Lean_PersistentArray_isEmpty___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Elab::Exception::{
    initialize_Lean_Elab_Exception, l_Lean_Elab_mkMessageCore,
    runtime_initialize_Lean_Elab_Exception,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_toMessageData;
use crate::r#gen::Lean::Log::{initialize_Lean_Log, runtime_initialize_Lean_Log};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_format___boxed, l_Lean_MessageData_nil,
    l_Lean_instInhabitedMessageData_default, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::MonadCache::l_Lean_MonadCacheT_instMonadExceptOf___redArg;
use crate::r#gen::Lean::Util::Sorry::l_Lean_Expr_hasSyntheticSorry;
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_string_utf8_byte_size, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_float, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_float, lean_unsigned_to_nat,
};
static mut l_Lean_instInhabitedTraceElem_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedTraceElem_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceElem_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceElem: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedTraceState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedTraceState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedTraceState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceState_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceState: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value
        ) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value
        ) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value
        ) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        105, 110, 104, 101, 114, 105, 116, 101, 100, 84, 114, 97, 99, 101, 79, 112, 116, 105, 111,
        110, 115, 46, 103, 101, 116, 0,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        105, 110, 104, 101, 114, 105, 116, 101, 100, 84, 114, 97, 99, 101, 79, 112, 116, 105, 111,
        110, 115, 0,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [103, 101, 116, 0],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value)
        as *mut LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value
        ) as *mut LeanObject,
        18248147900842368367 as *mut LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value
        ) as *mut LeanObject,
        17564138194259293689 as *mut LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_printTraces___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instToStringFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_printTraces___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_printTraces___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_resetTraceState___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_resetTraceState___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resetTraceState___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_resetTraceState___redArg___closed__0_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_checkTraceOption___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_checkTraceOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject;
pub static l_Lean_checkTraceOption___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_checkTraceOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_checkTraceOption___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_addTrace___redArg___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___redArg___lam__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___redArg___lam__0___closed__1_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_addTrace___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___redArg___lam__0___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_addTrace___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 102, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: LeanStringObject<99> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 99, m_capacity: 99, m_length: 98, m_data: [97, 99, 116, 105, 118, 97, 116, 101, 32, 110, 101, 115, 116, 101, 100, 32, 116, 114, 97, 99, 101, 115, 32, 119, 105, 116, 104, 32, 101, 120, 101, 99, 117, 116, 105, 111, 110, 32, 116, 105, 109, 101, 32, 97, 98, 111, 118, 101, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 32, 97, 110, 100, 32, 97, 110, 110, 111, 116, 97, 116, 101, 32, 119, 105, 116, 104, 32, 116, 105, 109, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject,3029557009233611192 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: LeanStringObject<130> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 130, m_capacity: 130, m_length: 129, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 105, 110, 32, 109, 105, 108, 108, 105, 115, 101, 99, 111, 110, 100, 115, 32, 40, 111, 114, 32, 104, 101, 97, 114, 116, 98, 101, 97, 116, 115, 32, 105, 102, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 46, 117, 115, 101, 72, 101, 97, 114, 116, 98, 101, 97, 116, 115, 96, 32, 105, 115, 32, 116, 114, 117, 101, 41, 44, 32, 116, 114, 97, 99, 101, 115, 32, 98, 101, 108, 111, 119, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 98, 101, 32, 97, 99, 116, 105, 118, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 10 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject,9872414562944363921 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 115, 101, 72, 101, 97, 114, 116, 98, 101, 97, 116, 115, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject,3582102001749243616 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 109, 101, 97, 115, 117, 114, 101, 32, 97, 110, 100, 32, 114, 101, 112, 111, 114, 116, 32, 104, 101, 97, 114, 116, 98, 101, 97, 116, 115, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 115, 101, 99, 111, 110, 100, 115, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject,4070060546168584281 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 117, 116, 112, 117, 116, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject,4936720448426421523 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: LeanStringObject<86> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [111, 117, 116, 112, 117, 116, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 96, 32, 100, 97, 116, 97, 32, 105, 110, 32, 70, 105, 114, 101, 102, 111, 120, 32, 80, 114, 111, 102, 105, 108, 101, 114, 45, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 102, 111, 114, 109, 97, 116, 32, 116, 111, 32, 103, 105, 118, 101, 110, 32, 102, 105, 108, 101, 32, 112, 97, 116, 104, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject,16374006435548021562 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 101, 114, 118, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject,9644734713936406706 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: LeanStringObject<126> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [115, 101, 114, 118, 101, 32, 116, 104, 101, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 96, 32, 100, 97, 116, 97, 32, 111, 118, 101, 114, 32, 72, 84, 84, 80, 32, 97, 110, 100, 32, 111, 112, 101, 110, 32, 105, 116, 32, 105, 110, 32, 96, 104, 116, 116, 112, 115, 58, 47, 47, 112, 114, 111, 102, 105, 108, 101, 114, 46, 102, 105, 114, 101, 102, 111, 120, 46, 99, 111, 109, 96, 59, 32, 98, 108, 111, 99, 107, 115, 32, 117, 110, 116, 105, 108, 32, 105, 110, 116, 101, 114, 114, 117, 112, 116, 101, 100, 32, 119, 105, 116, 104, 32, 67, 116, 114, 108, 43, 67, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject,5084970274551519787 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,5412095016269638404 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject,4936720448426421523 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject,12287765182031389121 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: LeanStringObject<232> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 232, m_capacity: 232, m_length: 231, m_data: [105, 102, 32, 102, 97, 108, 115, 101, 44, 32, 108, 105, 109, 105, 116, 32, 116, 101, 120, 116, 32, 105, 110, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 115, 32, 116, 111, 32, 116, 114, 97, 99, 101, 32, 99, 108, 97, 115, 115, 32, 110, 97, 109, 101, 32, 97, 110, 100, 32, 96, 84, 114, 97, 99, 101, 68, 97, 116, 97, 46, 116, 97, 103, 96, 44, 32, 105, 102, 32, 97, 110, 121, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 119, 104, 101, 110, 32, 119, 101, 32, 97, 114, 101, 32, 105, 110, 116, 101, 114, 101, 115, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 116, 105, 109, 101, 32, 116, 97, 107, 101, 110, 32, 98, 121, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 115, 117, 98, 115, 121, 115, 116, 101, 109, 115, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 115, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 116, 104, 101, 32, 99, 111, 109, 109, 111, 110, 32, 99, 97, 115, 101, 46, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut LeanObject,10644982123717200237 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut LeanObject,15799939003794391761 as *mut LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut LeanObject,16374006435548021562 as *mut LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject,15606591623558354660 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0: f64 =
    0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_monoNanosNow___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_getNumHeartbeats___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_trace_profiler_threshold_unitAdjusted___closed__0: f64 = 0.0;
static mut l_Lean_instMonadAlwaysExceptEIO___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instMonadAlwaysExceptEIO___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_bombEmoji___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 2,
    m_data: [240, 159, 146, 165, 239, 184, 143, 0],
};
static mut l_Lean_bombEmoji___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_bombEmoji___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_bombEmoji: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_bombEmoji___closed__0_value) as *mut LeanObject;
pub static l_Lean_checkEmoji___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 2,
    m_data: [226, 156, 133, 239, 184, 143, 0],
};
static mut l_Lean_checkEmoji___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_checkEmoji___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_checkEmoji: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_checkEmoji___closed__0_value) as *mut LeanObject;
pub static l_Lean_crossEmoji___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 2,
    m_data: [226, 157, 140, 239, 184, 143, 0],
};
static mut l_Lean_crossEmoji___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_crossEmoji___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_crossEmoji: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_crossEmoji___closed__0_value) as *mut LeanObject;
pub static l_Lean_instExceptToTraceResultBool___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instExceptToTraceResultBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instExceptToTraceResultBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_instExceptToTraceResultOption___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instExceptToTraceResultOption___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instExceptToTraceResultOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultOption___closed__0_value) as *mut LeanObject;
pub static l_Lean_instExceptToTraceResultExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instExceptToTraceResultExpr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instExceptToTraceResultExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_instExceptToTraceResult___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instExceptToTraceResult___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instExceptToTraceResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResult___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_withTraceNode_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_withTraceNode_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withTraceNode_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withTraceNode_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_registerTraceClass___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__1_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_registerTraceClass___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__1_value) as *mut LeanObject;
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
            ) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerTraceClass___auto__1___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__1_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerTraceClass___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__3_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_registerTraceClass___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__3_value) as *mut LeanObject;
static mut l_Lean_registerTraceClass___auto__1___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerTraceClass___auto__1___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_registerTraceClass___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerTraceClass___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l_Lean_registerTraceClass___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___closed__0_value) as *mut LeanObject;
pub static l_Lean_registerTraceClass___closed__1_value: LeanStringObject<59> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        101, 110, 97, 98, 108, 101, 47, 100, 105, 115, 97, 98, 108, 101, 32, 116, 114, 97, 99, 105,
        110, 103, 32, 102, 111, 114, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 109, 111,
        100, 117, 108, 101, 32, 97, 110, 100, 32, 115, 117, 98, 109, 111, 100, 117, 108, 101, 115,
        0,
    ],
};
static mut l_Lean_registerTraceClass___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 111, 73, 102, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 102, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 111, 73, 102, 80, 114, 111, 112, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value:
    LeanStringObject<15> = LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value)
            as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 101, 115, 116, 101, 100, 65, 99, 116, 105, 111, 110, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 144, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value:
    LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 105, 115, 84, 114, 97, 99, 105, 110, 103, 69, 110, 97, 98, 108, 101,
        100, 70, 111, 114, 0,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 115, 84, 114, 97, 99, 105, 110, 103, 69, 110, 97, 98, 108, 101, 100, 70, 111, 114, 0,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 104, 101, 110, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 111, 69, 120, 112, 114, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 97, 100, 100, 84, 114, 97, 99, 101, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 100, 100, 84, 114, 97, 99, 101, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value)
            as *mut LeanObject,
        4570674678924417756 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [100, 111, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value)
            as *mut LeanObject,
        3326968124746134365 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value)
            as *mut LeanObject,
        940684074193935882 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 111, 76, 101, 116, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value)
            as *mut LeanObject,
        14774476768116910908 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 101, 116, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value)
            as *mut LeanObject,
        17404204824591055365 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 101, 116, 68, 101, 99, 108, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value)
            as *mut LeanObject,
        8036185514257755965 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value)
            as *mut LeanObject,
        17116161260408496210 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 101, 116, 73, 100, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value)
            as *mut LeanObject,
        13708106407786339395 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 108, 115, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value)
            as *mut LeanObject,
        17601562613467935004 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value)
            as *mut LeanObject,
        9368229134555052249 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100,
        0,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value)
            as *mut LeanObject,
        14298422259736409839 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value:
    LeanStringObject<15> = LeanStringObject {
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
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value)
            as *mut LeanObject,
        5346268661279150583 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value)
            as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
            as *mut LeanObject,
        11510953549444071797 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
            as *mut LeanObject,
        491622604497152460 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)
            as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 77, 33, 95, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value)
        as *mut LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value)
            as *mut LeanObject,
        13317951319906582257 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 33, 0],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value)
        as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            100, 111, 69, 108, 101, 109, 84, 114, 97, 99, 101, 91, 95, 93, 95, 95, 0,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value) as *mut LeanObject;
static l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value)
                as *mut LeanObject,
            2825612102870995038 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [116, 114, 97, 99, 101, 91, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value)
                as *mut LeanObject,
            393173242845875278 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value)
                as *mut LeanObject,
            18163029821153688220 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value) as *mut LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value) as *mut LeanObject;
pub static mut l_Lean_doElemTrace_x5b___x5d____: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value) as *mut LeanObject;
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_String_instHashableRaw_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHashableProd___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_addTraceAsMessages___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_addTraceAsMessages___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_addTraceAsMessages___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_addTraceAsMessages___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_addTraceAsMessages___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_addTraceAsMessages___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,16213016488940853032 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,11246366368068211756 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,8857498384450530577 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9067059375846622420 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,16991972533670276437 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,4136137159096495612 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,15300736648833417205 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut LeanObject,7375598387208490336 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,13915489522383829438 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject,5175429902338115595 as *mut LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_instInhabitedTraceElem_default___closed__0() -> *mut LeanObject {
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Lean_instInhabitedMessageData_default;
    v___x_3712_ = lean_box(0);
    v___x_3713_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3713_, 0, v___x_3712_);
    lean_ctor_set(v___x_3713_, 1, v___x_3711_);
    return v___x_3713_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceElem_default() -> *mut LeanObject {
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    v___x_3714_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceElem_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceElem_default___closed__0_once),
        _init_l_Lean_instInhabitedTraceElem_default___closed__0,
    );
    return v___x_3714_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceElem() -> *mut LeanObject {
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_instInhabitedTraceElem_default;
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__0() -> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = lean_unsigned_to_nat(32);
    v___x_3717_ = lean_mk_empty_array_with_capacity(v___x_3716_);
    v___x_3718_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3718_, 0, v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__1() -> *mut LeanObject {
    let mut v___x_3719_: usize = 0;
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    v___x_3719_ = 5usize;
    v___x_3720_ = lean_unsigned_to_nat(0);
    v___x_3721_ = lean_unsigned_to_nat(32);
    v___x_3722_ = lean_mk_empty_array_with_capacity(v___x_3721_);
    v___x_3723_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__0_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__0,
    );
    v___x_3724_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3724_, 0, v___x_3723_);
    lean_ctor_set(v___x_3724_, 1, v___x_3722_);
    lean_ctor_set(v___x_3724_, 2, v___x_3720_);
    lean_ctor_set(v___x_3724_, 3, v___x_3720_);
    lean_ctor_set_usize(v___x_3724_, 4, v___x_3719_);
    return v___x_3724_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__2() -> *mut LeanObject {
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u64 = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    v___x_3725_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__1,
    );
    v___x_3726_ = 0u64;
    v___x_3727_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_3727_, 0, v___x_3725_);
    lean_ctor_set_uint64(
        v___x_3727_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3726_,
    );
    return v___x_3727_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default() -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v___x_3728_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__2,
    );
    return v___x_3728_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState() -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_instInhabitedTraceState_default;
    return v___x_3729_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    v___x_3730_ = lean_box(0);
    v___x_3731_ = lean_unsigned_to_nat(16);
    v___x_3732_ = lean_mk_array(v___x_3731_, v___x_3730_);
    return v___x_3732_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
    v___x_3734_ = lean_unsigned_to_nat(0);
    v___x_3735_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3735_, 0, v___x_3734_);
    lean_ctor_set(v___x_3735_, 1, v___x_3733_);
    return v___x_3735_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    v___x_3737_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
    v___x_3738_ = lean_st_mk_ref(v___x_3737_);
    v___x_3739_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3739_, 0, v___x_3738_);
    return v___x_3739_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(
    mut v_a_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
    return v_res_3741_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    v___x_3768_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10;
    v___x_3769_ = l_Lean_mkAtom(v___x_3768_);
    return v___x_3769_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    v___x_3770_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12,
    );
    v___x_3771_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_3772_ = lean_array_push(v___x_3771_, v___x_3770_);
    return v___x_3772_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15()
-> *mut LeanObject {
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14;
    v___x_3775_ = lean_string_utf8_byte_size(v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16()
-> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15,
    );
    v___x_3777_ = lean_unsigned_to_nat(0);
    v___x_3778_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14;
    v___x_3779_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3779_, 0, v___x_3778_);
    lean_ctor_set(v___x_3779_, 1, v___x_3777_);
    lean_ctor_set(v___x_3779_, 2, v___x_3776_);
    return v___x_3779_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    v___x_3785_ = lean_box(0);
    v___x_3786_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19;
    v___x_3787_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16,
    );
    v___x_3788_ = lean_box(2);
    v___x_3789_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_3789_, 0, v___x_3788_);
    lean_ctor_set(v___x_3789_, 1, v___x_3787_);
    lean_ctor_set(v___x_3789_, 2, v___x_3786_);
    lean_ctor_set(v___x_3789_, 3, v___x_3785_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    v___x_3790_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20,
    );
    v___x_3791_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13,
    );
    v___x_3792_ = lean_array_push(v___x_3791_, v___x_3790_);
    return v___x_3792_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    v___x_3793_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21,
    );
    v___x_3794_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11;
    v___x_3795_ = lean_box(2);
    v___x_3796_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3796_, 0, v___x_3795_);
    lean_ctor_set(v___x_3796_, 1, v___x_3794_);
    lean_ctor_set(v___x_3796_, 2, v___x_3793_);
    return v___x_3796_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    v___x_3797_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22,
    );
    v___x_3798_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_3799_ = lean_array_push(v___x_3798_, v___x_3797_);
    return v___x_3799_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    v___x_3800_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23,
    );
    v___x_3801_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
    v___x_3802_ = lean_box(2);
    v___x_3803_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3803_, 0, v___x_3802_);
    lean_ctor_set(v___x_3803_, 1, v___x_3801_);
    lean_ctor_set(v___x_3803_, 2, v___x_3800_);
    return v___x_3803_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    v___x_3804_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24,
    );
    v___x_3805_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_3806_ = lean_array_push(v___x_3805_, v___x_3804_);
    return v___x_3806_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    v___x_3807_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25,
    );
    v___x_3808_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7;
    v___x_3809_ = lean_box(2);
    v___x_3810_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    lean_ctor_set(v___x_3810_, 1, v___x_3808_);
    lean_ctor_set(v___x_3810_, 2, v___x_3807_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27()
-> *mut LeanObject {
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3811_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26,
    );
    v___x_3812_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_3813_ = lean_array_push(v___x_3812_, v___x_3811_);
    return v___x_3813_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28()
-> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    v___x_3814_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27,
    );
    v___x_3815_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4;
    v___x_3816_ = lean_box(2);
    v___x_3817_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3817_, 0, v___x_3816_);
    lean_ctor_set(v___x_3817_, 1, v___x_3815_);
    lean_ctor_set(v___x_3817_, 2, v___x_3814_);
    return v___x_3817_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam() -> *mut LeanObject {
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    v___x_3818_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28,
    );
    return v___x_3818_;
}
pub unsafe fn l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(
    mut v_modifyTraceState_3819_: *mut LeanObject,
    mut v_inst_3820_: *mut LeanObject,
    mut v_f_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    v___x_3822_ = lean_apply_1(v_modifyTraceState_3819_, v_f_3821_);
    v___x_3823_ = lean_apply_2(v_inst_3820_, lean_box(0), v___x_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_instMonadTraceOfMonadLift___redArg(
    mut v_inst_3824_: *mut LeanObject,
    mut v_inst_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___f_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_modifyTraceState_3826_ = lean_ctor_get(v_inst_3825_, 0);
                v_getTraceState_3827_ = lean_ctor_get(v_inst_3825_, 1);
                v_getInheritedTraceOptions_3828_ = lean_ctor_get(v_inst_3825_, 2);
                v_isSharedCheck_3838_ = (!lean_is_exclusive(v_inst_3825_)) as u8;
                if v_isSharedCheck_3838_ == 0 {
                    v___x_3830_ = v_inst_3825_;
                    v_isShared_3831_ = v_isSharedCheck_3838_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_getInheritedTraceOptions_3828_);
                    lean_inc(v_getTraceState_3827_);
                    lean_inc(v_modifyTraceState_3826_);
                    lean_dec(v_inst_3825_);
                    v___x_3830_ = lean_box(0);
                    v_isShared_3831_ = v_isSharedCheck_3838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_3824_, 2);
                v___f_3832_ = lean_alloc_closure(
                    l_Lean_instMonadTraceOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3832_, 0, v_modifyTraceState_3826_);
                lean_closure_set(v___f_3832_, 1, v_inst_3824_);
                v___x_3833_ = lean_apply_2(v_inst_3824_, lean_box(0), v_getTraceState_3827_);
                v___x_3834_ =
                    lean_apply_2(v_inst_3824_, lean_box(0), v_getInheritedTraceOptions_3828_);
                if v_isShared_3831_ == 0 {
                    lean_ctor_set(v___x_3830_, 2, v___x_3834_);
                    lean_ctor_set(v___x_3830_, 1, v___x_3833_);
                    lean_ctor_set(v___x_3830_, 0, v___f_3832_);
                    v___x_3836_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___f_3832_);
                    lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3833_);
                    lean_ctor_set(v_reuseFailAlloc_3837_, 2, v___x_3834_);
                    v___x_3836_ = v_reuseFailAlloc_3837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadTraceOfMonadLift(
    mut v_m_3839_: *mut LeanObject,
    mut v_n_3840_: *mut LeanObject,
    mut v_inst_3841_: *mut LeanObject,
    mut v_inst_3842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    v___x_3843_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_3841_, v_inst_3842_);
    return v___x_3843_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__0(
    mut v_toPure_3844_: *mut LeanObject,
    mut v_____s_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    v___x_3846_ = lean_box(0);
    v___x_3847_ = lean_apply_2(v_toPure_3844_, lean_box(0), v___x_3846_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__1(
    mut v___x_3848_: *mut LeanObject,
    mut v_toPure_3849_: *mut LeanObject,
    mut v_r_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    v___x_3851_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3851_, 0, v___x_3848_);
    v___x_3852_ = lean_apply_2(v_toPure_3849_, lean_box(0), v___x_3851_);
    return v___x_3852_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__2(
    mut v___f_3853_: *mut LeanObject,
    mut v_inst_3854_: *mut LeanObject,
    mut v_toBind_3855_: *mut LeanObject,
    mut v___f_3856_: *mut LeanObject,
    mut v_____do__lift_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = lean_alloc_closure(l_IO_println___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_3858_, 0, lean_box(0));
    lean_closure_set(v___x_3858_, 1, v___f_3853_);
    lean_closure_set(v___x_3858_, 2, v_____do__lift_3857_);
    v___x_3859_ = lean_apply_2(v_inst_3854_, lean_box(0), v___x_3858_);
    v___x_3860_ = lean_apply_4(
        v_toBind_3855_,
        lean_box(0),
        lean_box(0),
        v___x_3859_,
        v___f_3856_,
    );
    return v___x_3860_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__3(
    mut v_inst_3861_: *mut LeanObject,
    mut v_toBind_3862_: *mut LeanObject,
    mut v___f_3863_: *mut LeanObject,
    mut v_x_3864_: *mut LeanObject,
    mut v_____s_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    v_msg_3866_ = lean_ctor_get(v_x_3864_, 1);
    lean_inc_ref(v_msg_3866_);
    lean_dec_ref(v_x_3864_);
    v___x_3867_ = lean_box(0);
    v___x_3868_ = lean_alloc_closure(
        l_Lean_MessageData_format___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_3868_, 0, v_msg_3866_);
    lean_closure_set(v___x_3868_, 1, v___x_3867_);
    v___x_3869_ = lean_alloc_closure(l_BaseIO_toIO___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_3869_, 0, lean_box(0));
    lean_closure_set(v___x_3869_, 1, v___x_3868_);
    v___x_3870_ = lean_apply_2(v_inst_3861_, lean_box(0), v___x_3869_);
    v___x_3871_ = lean_apply_4(
        v_toBind_3862_,
        lean_box(0),
        lean_box(0),
        v___x_3870_,
        v___f_3863_,
    );
    return v___x_3871_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__4(
    mut v_toPure_3872_: *mut LeanObject,
    mut v___f_3873_: *mut LeanObject,
    mut v_inst_3874_: *mut LeanObject,
    mut v_toBind_3875_: *mut LeanObject,
    mut v_inst_3876_: *mut LeanObject,
    mut v___f_3877_: *mut LeanObject,
    mut v_____do__lift_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_traces_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    v_traces_3879_ = lean_ctor_get(v_____do__lift_3878_, 0);
    v___x_3880_ = lean_box(0);
    v___f_3881_ = lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3881_, 0, v___x_3880_);
    lean_closure_set(v___f_3881_, 1, v_toPure_3872_);
    lean_inc_n(v_toBind_3875_, 2);
    lean_inc(v_inst_3874_);
    v___f_3882_ = lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_3882_, 0, v___f_3873_);
    lean_closure_set(v___f_3882_, 1, v_inst_3874_);
    lean_closure_set(v___f_3882_, 2, v_toBind_3875_);
    lean_closure_set(v___f_3882_, 3, v___f_3881_);
    v___f_3883_ = lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3883_, 0, v_inst_3874_);
    lean_closure_set(v___f_3883_, 1, v_toBind_3875_);
    lean_closure_set(v___f_3883_, 2, v___f_3882_);
    v___x_3884_ = l_Lean_PersistentArray_forIn___redArg(
        v_inst_3876_,
        v_traces_3879_,
        v___x_3880_,
        v___f_3883_,
    );
    v___x_3885_ = lean_apply_4(
        v_toBind_3875_,
        lean_box(0),
        lean_box(0),
        v___x_3884_,
        v___f_3877_,
    );
    return v___x_3885_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__4___boxed(
    mut v_toPure_3886_: *mut LeanObject,
    mut v___f_3887_: *mut LeanObject,
    mut v_inst_3888_: *mut LeanObject,
    mut v_toBind_3889_: *mut LeanObject,
    mut v_inst_3890_: *mut LeanObject,
    mut v___f_3891_: *mut LeanObject,
    mut v_____do__lift_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3893_: *mut LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Lean_printTraces___redArg___lam__4(
        v_toPure_3886_,
        v___f_3887_,
        v_inst_3888_,
        v_toBind_3889_,
        v_inst_3890_,
        v___f_3891_,
        v_____do__lift_3892_,
    );
    lean_dec_ref(v_____do__lift_3892_);
    return v_res_3893_;
}
pub unsafe fn l_Lean_printTraces___redArg(
    mut v_inst_3895_: *mut LeanObject,
    mut v_inst_3896_: *mut LeanObject,
    mut v_inst_3897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3898_ = lean_ctor_get(v_inst_3895_, 0);
    v_toBind_3899_ = lean_ctor_get(v_inst_3895_, 1);
    lean_inc_n(v_toBind_3899_, 2);
    v_getTraceState_3900_ = lean_ctor_get(v_inst_3896_, 1);
    lean_inc(v_getTraceState_3900_);
    lean_dec_ref(v_inst_3896_);
    v_toPure_3901_ = lean_ctor_get(v_toApplicative_3898_, 1);
    lean_inc_n(v_toPure_3901_, 2);
    v___f_3902_ = l_Lean_printTraces___redArg___closed__0;
    v___f_3903_ = lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3903_, 0, v_toPure_3901_);
    v___f_3904_ = lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__4___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3904_, 0, v_toPure_3901_);
    lean_closure_set(v___f_3904_, 1, v___f_3902_);
    lean_closure_set(v___f_3904_, 2, v_inst_3897_);
    lean_closure_set(v___f_3904_, 3, v_toBind_3899_);
    lean_closure_set(v___f_3904_, 4, v_inst_3895_);
    lean_closure_set(v___f_3904_, 5, v___f_3903_);
    v___x_3905_ = lean_apply_4(
        v_toBind_3899_,
        lean_box(0),
        lean_box(0),
        v_getTraceState_3900_,
        v___f_3904_,
    );
    return v___x_3905_;
}
pub unsafe fn l_Lean_printTraces(
    mut v_m_3906_: *mut LeanObject,
    mut v_inst_3907_: *mut LeanObject,
    mut v_inst_3908_: *mut LeanObject,
    mut v_inst_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Lean_printTraces___redArg(v_inst_3907_, v_inst_3908_, v_inst_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Lean_resetTraceState___redArg___lam__0(
    mut v_x_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3912_ = lean_unsigned_to_nat(32);
    v___x_3913_ = lean_mk_empty_array_with_capacity(v___x_3912_);
    lean_dec_ref(v___x_3913_);
    v___x_3914_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__2,
    );
    return v___x_3914_;
}
pub unsafe fn l_Lean_resetTraceState___redArg___lam__0___boxed(
    mut v_x_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3916_: *mut LeanObject = core::ptr::null_mut();
    v_res_3916_ = l_Lean_resetTraceState___redArg___lam__0(v_x_3915_);
    lean_dec_ref(v_x_3915_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_resetTraceState___redArg(
    mut v_inst_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_3919_ = lean_ctor_get(v_inst_3918_, 0);
    lean_inc(v_modifyTraceState_3919_);
    lean_dec_ref(v_inst_3918_);
    v___f_3920_ = l_Lean_resetTraceState___redArg___closed__0;
    v___x_3921_ = lean_apply_1(v_modifyTraceState_3919_, v___f_3920_);
    return v___x_3921_;
}
pub unsafe fn l_Lean_resetTraceState(
    mut v_m_3922_: *mut LeanObject,
    mut v_inst_3923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    v___x_3924_ = l_Lean_resetTraceState___redArg(v_inst_3923_);
    return v___x_3924_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(
    mut v_a_3925_: *mut LeanObject,
    mut v_x_3926_: *mut LeanObject,
) -> u8 {
    let mut v___x_3927_: u8 = 0;
    let mut v_key_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3926_) == 0 {
                    v___x_3927_ = 0;
                    return v___x_3927_;
                } else {
                    v_key_3928_ = lean_ctor_get(v_x_3926_, 0);
                    v_tail_3929_ = lean_ctor_get(v_x_3926_, 2);
                    v___x_3930_ = lean_name_eq(v_key_3928_, v_a_3925_);
                    if v___x_3930_ == 0 {
                        v_x_3926_ = v_tail_3929_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3930_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(
    mut v_a_3932_: *mut LeanObject,
    mut v_x_3933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3934_: u8 = 0;
    let mut v_r_3935_: *mut LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_3932_, v_x_3933_);
    lean_dec(v_x_3933_);
    lean_dec(v_a_3932_);
    v_r_3935_ = lean_box((v_res_3934_) as usize);
    return v_r_3935_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: u64 = 0;
    v___x_3936_ = lean_unsigned_to_nat(1723);
    v___x_3937_ = lean_uint64_of_nat(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(
    mut v_m_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: u64 = 0;
    let mut v___x_3944_: u64 = 0;
    let mut v___x_3945_: u64 = 0;
    let mut v_fold_3946_: u64 = 0;
    let mut v___x_3947_: u64 = 0;
    let mut v___x_3948_: u64 = 0;
    let mut v___x_3949_: u64 = 0;
    let mut v___x_3950_: usize = 0;
    let mut v___x_3951_: usize = 0;
    let mut v___x_3952_: usize = 0;
    let mut v___x_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v___x_3957_: u64 = 0;
    let mut v_hash_3958_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3940_ = lean_ctor_get(v_m_3938_, 1);
                v___x_3941_ = lean_array_get_size(v_buckets_3940_);
                if lean_obj_tag(v_a_3939_) == 0 {
                    v___x_3957_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_3943_ = v___x_3957_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3958_ = lean_ctor_get_uint64(
                        v_a_3939_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3943_ = v_hash_3958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3944_ = 32u64;
                v___x_3945_ = lean_uint64_shift_right(v___y_3943_, v___x_3944_);
                v_fold_3946_ = lean_uint64_xor(v___y_3943_, v___x_3945_);
                v___x_3947_ = 16u64;
                v___x_3948_ = lean_uint64_shift_right(v_fold_3946_, v___x_3947_);
                v___x_3949_ = lean_uint64_xor(v_fold_3946_, v___x_3948_);
                v___x_3950_ = lean_uint64_to_usize(v___x_3949_);
                v___x_3951_ = lean_usize_of_nat(v___x_3941_);
                v___x_3952_ = 1usize;
                v___x_3953_ = lean_usize_sub(v___x_3951_, v___x_3952_);
                v___x_3954_ = lean_usize_land(v___x_3950_, v___x_3953_);
                v___x_3955_ = lean_array_uget_borrowed(v_buckets_3940_, v___x_3954_);
                v___x_3956_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_3939_, v___x_3955_);
                return v___x_3956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(
    mut v_m_3959_: *mut LeanObject,
    mut v_a_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3961_: u8 = 0;
    let mut v_r_3962_: *mut LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_3959_, v_a_3960_);
    lean_dec(v_a_3960_);
    lean_dec_ref(v_m_3959_);
    v_r_3962_ = lean_box((v_res_3961_) as usize);
    return v_r_3962_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
    mut v_inherited_3963_: *mut LeanObject,
    mut v_opts_3964_: *mut LeanObject,
    mut v_opt_3965_: *mut LeanObject,
) -> u8 {
    let mut v_pre_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3970_: u8 = 0;
    let mut v_map_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3971_ = lean_ctor_get(v_opts_3964_, 0);
                v___x_3972_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3971_, v_opt_3965_);
                if lean_obj_tag(v___x_3972_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_3973_ = lean_ctor_get(v___x_3972_, 0);
                    lean_inc(v_val_3973_);
                    lean_dec_ref_known(v___x_3972_, 1);
                    if lean_obj_tag(v_val_3973_) == 1 {
                        v_v_3974_ = lean_ctor_get_uint8(v_val_3973_, 0 as u32);
                        lean_dec_ref_known(v_val_3973_, 0);
                        return v_v_3974_;
                    } else {
                        lean_dec(v_val_3973_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_opt_3965_) == 1 {
                    v_pre_3967_ = lean_ctor_get(v_opt_3965_, 0);
                    v___x_3968_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_3963_, v_opt_3965_);
                    if v___x_3968_ == 0 {
                        return v___x_3968_;
                    } else {
                        v_opt_3965_ = v_pre_3967_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_3970_ = 0;
                    return v___x_3970_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(
    mut v_inherited_3975_: *mut LeanObject,
    mut v_opts_3976_: *mut LeanObject,
    mut v_opt_3977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3978_: u8 = 0;
    let mut v_r_3979_: *mut LeanObject = core::ptr::null_mut();
    v_res_3978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
        v_inherited_3975_,
        v_opts_3976_,
        v_opt_3977_,
    );
    lean_dec(v_opt_3977_);
    lean_dec_ref(v_opts_3976_);
    lean_dec_ref(v_inherited_3975_);
    v_r_3979_ = lean_box((v_res_3978_) as usize);
    return v_r_3979_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(
    mut v_00_u03b2_3980_: *mut LeanObject,
    mut v_m_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
) -> u8 {
    let mut v___x_3983_: u8 = 0;
    v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_3981_, v_a_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(
    mut v_00_u03b2_3984_: *mut LeanObject,
    mut v_m_3985_: *mut LeanObject,
    mut v_a_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: u8 = 0;
    let mut v_r_3988_: *mut LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_3984_, v_m_3985_, v_a_3986_);
    lean_dec(v_a_3986_);
    lean_dec_ref(v_m_3985_);
    v_r_3988_ = lean_box((v_res_3987_) as usize);
    return v_r_3988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(
    mut v_00_u03b2_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_x_3991_: *mut LeanObject,
) -> u8 {
    let mut v___x_3992_: u8 = 0;
    v___x_3992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_3990_, v_x_3991_);
    return v___x_3992_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
    mut v_x_3995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3996_: u8 = 0;
    let mut v_r_3997_: *mut LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_3993_, v_a_3994_, v_x_3995_);
    lean_dec(v_x_3995_);
    lean_dec(v_a_3994_);
    v_r_3997_ = lean_box((v_res_3996_) as usize);
    return v_r_3997_;
}
pub unsafe fn l_Lean_checkTraceOption(
    mut v_inherited_4001_: *mut LeanObject,
    mut v_opts_4002_: *mut LeanObject,
    mut v_cls_4003_: *mut LeanObject,
) -> u8 {
    let mut v_hasTrace_4004_: u8 = 0;
    v_hasTrace_4004_ = lean_ctor_get_uint8(
        v_opts_4002_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4004_ == 0 {
        lean_dec(v_cls_4003_);
        return v_hasTrace_4004_;
    } else {
        let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4007_: u8 = 0;
        v___x_4005_ = l_Lean_checkTraceOption___closed__1;
        v___x_4006_ = l_Lean_Name_append(v___x_4005_, v_cls_4003_);
        v___x_4007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inherited_4001_,
            v_opts_4002_,
            v___x_4006_,
        );
        lean_dec(v___x_4006_);
        return v___x_4007_;
    }
}
pub unsafe fn l_Lean_checkTraceOption___boxed(
    mut v_inherited_4008_: *mut LeanObject,
    mut v_opts_4009_: *mut LeanObject,
    mut v_cls_4010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4011_: u8 = 0;
    let mut v_r_4012_: *mut LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_Lean_checkTraceOption(v_inherited_4008_, v_opts_4009_, v_cls_4010_);
    lean_dec_ref(v_opts_4009_);
    lean_dec_ref(v_inherited_4008_);
    v_r_4012_ = lean_box((v_res_4011_) as usize);
    return v_r_4012_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__0(
    mut v_toPure_4013_: *mut LeanObject,
    mut v_cls_4014_: *mut LeanObject,
    mut v_____do__lift_4015_: *mut LeanObject,
    mut v_____do__lift_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_4017_: u8 = 0;
    v_hasTrace_4017_ = lean_ctor_get_uint8(
        v_____do__lift_4016_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4017_ == 0 {
        let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_cls_4014_);
        v___x_4018_ = lean_box((v_hasTrace_4017_) as usize);
        v___x_4019_ = lean_apply_2(v_toPure_4013_, lean_box(0), v___x_4018_);
        return v___x_4019_;
    } else {
        let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: u8 = 0;
        let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
        v___x_4020_ = l_Lean_checkTraceOption___closed__1;
        v___x_4021_ = l_Lean_Name_append(v___x_4020_, v_cls_4014_);
        v___x_4022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_4015_,
            v_____do__lift_4016_,
            v___x_4021_,
        );
        lean_dec(v___x_4021_);
        v___x_4023_ = lean_box((v___x_4022_) as usize);
        v___x_4024_ = lean_apply_2(v_toPure_4013_, lean_box(0), v___x_4023_);
        return v___x_4024_;
    }
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(
    mut v_toPure_4025_: *mut LeanObject,
    mut v_cls_4026_: *mut LeanObject,
    mut v_____do__lift_4027_: *mut LeanObject,
    mut v_____do__lift_4028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4029_: *mut LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_Lean_isTracingEnabledFor___redArg___lam__0(
        v_toPure_4025_,
        v_cls_4026_,
        v_____do__lift_4027_,
        v_____do__lift_4028_,
    );
    lean_dec_ref(v_____do__lift_4028_);
    lean_dec_ref(v_____do__lift_4027_);
    return v_res_4029_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__1(
    mut v_toPure_4030_: *mut LeanObject,
    mut v_cls_4031_: *mut LeanObject,
    mut v_toBind_4032_: *mut LeanObject,
    mut v_inst_4033_: *mut LeanObject,
    mut v_____do__lift_4034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    v___f_4035_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4035_, 0, v_toPure_4030_);
    lean_closure_set(v___f_4035_, 1, v_cls_4031_);
    lean_closure_set(v___f_4035_, 2, v_____do__lift_4034_);
    v___x_4036_ = lean_apply_4(
        v_toBind_4032_,
        lean_box(0),
        lean_box(0),
        v_inst_4033_,
        v___f_4035_,
    );
    return v___x_4036_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg(
    mut v_inst_4037_: *mut LeanObject,
    mut v_inst_4038_: *mut LeanObject,
    mut v_inst_4039_: *mut LeanObject,
    mut v_cls_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4041_ = lean_ctor_get(v_inst_4037_, 0);
    lean_inc_ref(v_toApplicative_4041_);
    v_toBind_4042_ = lean_ctor_get(v_inst_4037_, 1);
    lean_inc_n(v_toBind_4042_, 2);
    lean_dec_ref(v_inst_4037_);
    v_getInheritedTraceOptions_4043_ = lean_ctor_get(v_inst_4038_, 2);
    lean_inc(v_getInheritedTraceOptions_4043_);
    lean_dec_ref(v_inst_4038_);
    v_toPure_4044_ = lean_ctor_get(v_toApplicative_4041_, 1);
    lean_inc(v_toPure_4044_);
    lean_dec_ref(v_toApplicative_4041_);
    v___f_4045_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4045_, 0, v_toPure_4044_);
    lean_closure_set(v___f_4045_, 1, v_cls_4040_);
    lean_closure_set(v___f_4045_, 2, v_toBind_4042_);
    lean_closure_set(v___f_4045_, 3, v_inst_4039_);
    v___x_4046_ = lean_apply_4(
        v_toBind_4042_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4043_,
        v___f_4045_,
    );
    return v___x_4046_;
}
pub unsafe fn l_Lean_isTracingEnabledFor(
    mut v_m_4047_: *mut LeanObject,
    mut v_inst_4048_: *mut LeanObject,
    mut v_inst_4049_: *mut LeanObject,
    mut v_inst_4050_: *mut LeanObject,
    mut v_cls_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4052_ = lean_ctor_get(v_inst_4048_, 0);
    lean_inc_ref(v_toApplicative_4052_);
    v_toBind_4053_ = lean_ctor_get(v_inst_4048_, 1);
    lean_inc_n(v_toBind_4053_, 2);
    lean_dec_ref(v_inst_4048_);
    v_getInheritedTraceOptions_4054_ = lean_ctor_get(v_inst_4049_, 2);
    lean_inc(v_getInheritedTraceOptions_4054_);
    lean_dec_ref(v_inst_4049_);
    v_toPure_4055_ = lean_ctor_get(v_toApplicative_4052_, 1);
    lean_inc(v_toPure_4055_);
    lean_dec_ref(v_toApplicative_4052_);
    v___f_4056_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4056_, 0, v_toPure_4055_);
    lean_closure_set(v___f_4056_, 1, v_cls_4051_);
    lean_closure_set(v___f_4056_, 2, v_toBind_4053_);
    lean_closure_set(v___f_4056_, 3, v_inst_4050_);
    v___x_4057_ = lean_apply_4(
        v_toBind_4053_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4054_,
        v___f_4056_,
    );
    return v___x_4057_;
}
pub unsafe fn lean_is_trace_class_enabled(
    mut v_opts_4058_: *mut LeanObject,
    mut v_cls_4059_: *mut LeanObject,
) -> u8 {
    let mut v_hasTrace_4061_: u8 = 0;
    v_hasTrace_4061_ = lean_ctor_get_uint8(
        v_opts_4058_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4061_ == 0 {
        lean_dec(v_cls_4059_);
        lean_dec_ref(v_opts_4058_);
        return v_hasTrace_4061_;
    } else {
        let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4066_: u8 = 0;
        v___x_4062_ = l_Lean_inheritedTraceOptions;
        v___x_4063_ = lean_st_ref_get(v___x_4062_);
        v___x_4064_ = l_Lean_checkTraceOption___closed__1;
        v___x_4065_ = l_Lean_Name_append(v___x_4064_, v_cls_4059_);
        v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v___x_4063_,
            v_opts_4058_,
            v___x_4065_,
        );
        lean_dec(v___x_4065_);
        lean_dec_ref(v_opts_4058_);
        lean_dec(v___x_4063_);
        return v___x_4066_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(
    mut v_opts_4067_: *mut LeanObject,
    mut v_cls_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4070_: u8 = 0;
    let mut v_r_4071_: *mut LeanObject = core::ptr::null_mut();
    v_res_4070_ = lean_is_trace_class_enabled(v_opts_4067_, v_cls_4068_);
    v_r_4071_ = lean_box((v_res_4070_) as usize);
    return v_r_4071_;
}
pub unsafe fn l_Lean_getTraces___redArg___lam__0(
    mut v_toPure_4072_: *mut LeanObject,
    mut v_s_4073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_traces_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    v_traces_4074_ = lean_ctor_get(v_s_4073_, 0);
    lean_inc_ref(v_traces_4074_);
    lean_dec_ref(v_s_4073_);
    v___x_4075_ = lean_apply_2(v_toPure_4072_, lean_box(0), v_traces_4074_);
    return v___x_4075_;
}
pub unsafe fn l_Lean_getTraces___redArg(
    mut v_inst_4076_: *mut LeanObject,
    mut v_inst_4077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4078_ = lean_ctor_get(v_inst_4076_, 0);
    lean_inc_ref(v_toApplicative_4078_);
    v_toBind_4079_ = lean_ctor_get(v_inst_4076_, 1);
    lean_inc(v_toBind_4079_);
    lean_dec_ref(v_inst_4076_);
    v_getTraceState_4080_ = lean_ctor_get(v_inst_4077_, 1);
    lean_inc(v_getTraceState_4080_);
    lean_dec_ref(v_inst_4077_);
    v_toPure_4081_ = lean_ctor_get(v_toApplicative_4078_, 1);
    lean_inc(v_toPure_4081_);
    lean_dec_ref(v_toApplicative_4078_);
    v___f_4082_ = lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4082_, 0, v_toPure_4081_);
    v___x_4083_ = lean_apply_4(
        v_toBind_4079_,
        lean_box(0),
        lean_box(0),
        v_getTraceState_4080_,
        v___f_4082_,
    );
    return v___x_4083_;
}
pub unsafe fn l_Lean_getTraces(
    mut v_m_4084_: *mut LeanObject,
    mut v_inst_4085_: *mut LeanObject,
    mut v_inst_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4087_ = lean_ctor_get(v_inst_4085_, 0);
    lean_inc_ref(v_toApplicative_4087_);
    v_toBind_4088_ = lean_ctor_get(v_inst_4085_, 1);
    lean_inc(v_toBind_4088_);
    lean_dec_ref(v_inst_4085_);
    v_getTraceState_4089_ = lean_ctor_get(v_inst_4086_, 1);
    lean_inc(v_getTraceState_4089_);
    lean_dec_ref(v_inst_4086_);
    v_toPure_4090_ = lean_ctor_get(v_toApplicative_4087_, 1);
    lean_inc(v_toPure_4090_);
    lean_dec_ref(v_toApplicative_4087_);
    v___f_4091_ = lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4091_, 0, v_toPure_4090_);
    v___x_4092_ = lean_apply_4(
        v_toBind_4088_,
        lean_box(0),
        lean_box(0),
        v_getTraceState_4089_,
        v___f_4091_,
    );
    return v___x_4092_;
}
pub unsafe fn l_Lean_modifyTraces___redArg___lam__0(
    mut v_f_4093_: *mut LeanObject,
    mut v_s_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_4095_: u64 = 0;
    let mut v_traces_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4095_ = lean_ctor_get_uint64(
                    v_s_4094_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4096_ = lean_ctor_get(v_s_4094_, 0);
                v_isSharedCheck_4104_ = (!lean_is_exclusive(v_s_4094_)) as u8;
                if v_isSharedCheck_4104_ == 0 {
                    v___x_4098_ = v_s_4094_;
                    v_isShared_4099_ = v_isSharedCheck_4104_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_traces_4096_);
                    lean_dec(v_s_4094_);
                    v___x_4098_ = lean_box(0);
                    v_isShared_4099_ = v_isSharedCheck_4104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4100_ = lean_apply_1(v_f_4093_, v_traces_4096_);
                if v_isShared_4099_ == 0 {
                    lean_ctor_set(v___x_4098_, 0, v___x_4100_);
                    v___x_4102_ = v___x_4098_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4103_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4095_,
                    );
                    v___x_4102_ = v_reuseFailAlloc_4103_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_modifyTraces___redArg(
    mut v_inst_4105_: *mut LeanObject,
    mut v_f_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4107_ = lean_ctor_get(v_inst_4105_, 0);
    lean_inc(v_modifyTraceState_4107_);
    lean_dec_ref(v_inst_4105_);
    v___f_4108_ = lean_alloc_closure(
        l_Lean_modifyTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4108_, 0, v_f_4106_);
    v___x_4109_ = lean_apply_1(v_modifyTraceState_4107_, v___f_4108_);
    return v___x_4109_;
}
pub unsafe fn l_Lean_modifyTraces(
    mut v_m_4110_: *mut LeanObject,
    mut v_inst_4111_: *mut LeanObject,
    mut v_f_4112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4113_ = lean_ctor_get(v_inst_4111_, 0);
    lean_inc(v_modifyTraceState_4113_);
    lean_dec_ref(v_inst_4111_);
    v___f_4114_ = lean_alloc_closure(
        l_Lean_modifyTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4114_, 0, v_f_4112_);
    v___x_4115_ = lean_apply_1(v_modifyTraceState_4113_, v___f_4114_);
    return v___x_4115_;
}
pub unsafe fn l_Lean_setTraceState___redArg___lam__0(
    mut v_s_4116_: *mut LeanObject,
    mut v_x_4117_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_4116_);
    return v_s_4116_;
}
pub unsafe fn l_Lean_setTraceState___redArg___lam__0___boxed(
    mut v_s_4118_: *mut LeanObject,
    mut v_x_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4120_: *mut LeanObject = core::ptr::null_mut();
    v_res_4120_ = l_Lean_setTraceState___redArg___lam__0(v_s_4118_, v_x_4119_);
    lean_dec_ref(v_x_4119_);
    lean_dec_ref(v_s_4118_);
    return v_res_4120_;
}
pub unsafe fn l_Lean_setTraceState___redArg(
    mut v_inst_4121_: *mut LeanObject,
    mut v_s_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4123_ = lean_ctor_get(v_inst_4121_, 0);
    lean_inc(v_modifyTraceState_4123_);
    lean_dec_ref(v_inst_4121_);
    v___f_4124_ = lean_alloc_closure(
        l_Lean_setTraceState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4124_, 0, v_s_4122_);
    v___x_4125_ = lean_apply_1(v_modifyTraceState_4123_, v___f_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Lean_setTraceState(
    mut v_m_4126_: *mut LeanObject,
    mut v_inst_4127_: *mut LeanObject,
    mut v_s_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4129_ = lean_ctor_get(v_inst_4127_, 0);
    lean_inc(v_modifyTraceState_4129_);
    lean_dec_ref(v_inst_4127_);
    v___f_4130_ = lean_alloc_closure(
        l_Lean_setTraceState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4130_, 0, v_s_4128_);
    v___x_4131_ = lean_apply_1(v_modifyTraceState_4129_, v___f_4130_);
    return v___x_4131_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(
    mut v_s_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_4133_: u64 = 0;
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_unused_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4133_ = lean_ctor_get_uint64(
                    v_s_4132_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4143_ = (!lean_is_exclusive(v_s_4132_)) as u8;
                if v_isSharedCheck_4143_ == 0 {
                    v_unused_4144_ = lean_ctor_get(v_s_4132_, 0);
                    lean_dec(v_unused_4144_);
                    v___x_4135_ = v_s_4132_;
                    v_isShared_4136_ = v_isSharedCheck_4143_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_4132_);
                    v___x_4135_ = lean_box(0);
                    v_isShared_4136_ = v_isSharedCheck_4143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4137_ = lean_unsigned_to_nat(32);
                v___x_4138_ = lean_mk_empty_array_with_capacity(v___x_4137_);
                lean_dec_ref(v___x_4138_);
                v___x_4139_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_instInhabitedTraceState_default___closed__1_once
                    ),
                    _init_l_Lean_instInhabitedTraceState_default___closed__1,
                );
                if v_isShared_4136_ == 0 {
                    lean_ctor_set(v___x_4135_, 0, v___x_4139_);
                    v___x_4141_ = v___x_4135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4142_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4133_,
                    );
                    v___x_4141_ = v_reuseFailAlloc_4142_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(
    mut v_toPure_4145_: *mut LeanObject,
    mut v_oldTraces_4146_: *mut LeanObject,
    mut v_____r_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    v___x_4148_ = lean_apply_2(v_toPure_4145_, lean_box(0), v_oldTraces_4146_);
    return v___x_4148_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(
    mut v_toPure_4149_: *mut LeanObject,
    mut v_modifyTraceState_4150_: *mut LeanObject,
    mut v___f_4151_: *mut LeanObject,
    mut v_toBind_4152_: *mut LeanObject,
    mut v_oldTraces_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___f_4154_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4154_, 0, v_toPure_4149_);
    lean_closure_set(v___f_4154_, 1, v_oldTraces_4153_);
    v___x_4155_ = lean_apply_1(v_modifyTraceState_4150_, v___f_4151_);
    v___x_4156_ = lean_apply_4(
        v_toBind_4152_,
        lean_box(0),
        lean_box(0),
        v___x_4155_,
        v___f_4154_,
    );
    return v___x_4156_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
    mut v_inst_4158_: *mut LeanObject,
    mut v_inst_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4160_ = lean_ctor_get(v_inst_4158_, 0);
    lean_inc_ref(v_toApplicative_4160_);
    v_toBind_4161_ = lean_ctor_get(v_inst_4158_, 1);
    lean_inc_n(v_toBind_4161_, 3);
    lean_dec_ref(v_inst_4158_);
    v_modifyTraceState_4162_ = lean_ctor_get(v_inst_4159_, 0);
    lean_inc(v_modifyTraceState_4162_);
    v_getTraceState_4163_ = lean_ctor_get(v_inst_4159_, 1);
    lean_inc(v_getTraceState_4163_);
    lean_dec_ref(v_inst_4159_);
    v_toPure_4164_ = lean_ctor_get(v_toApplicative_4160_, 1);
    lean_inc_n(v_toPure_4164_, 2);
    lean_dec_ref(v_toApplicative_4160_);
    v___f_4165_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0;
    v___f_4166_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4166_, 0, v_toPure_4164_);
    lean_closure_set(v___f_4166_, 1, v_modifyTraceState_4162_);
    lean_closure_set(v___f_4166_, 2, v___f_4165_);
    lean_closure_set(v___f_4166_, 3, v_toBind_4161_);
    v___f_4167_ = lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4167_, 0, v_toPure_4164_);
    v___x_4168_ = lean_apply_4(
        v_toBind_4161_,
        lean_box(0),
        lean_box(0),
        v_getTraceState_4163_,
        v___f_4167_,
    );
    v___x_4169_ = lean_apply_4(
        v_toBind_4161_,
        lean_box(0),
        lean_box(0),
        v___x_4168_,
        v___f_4166_,
    );
    return v___x_4169_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces(
    mut v_m_4170_: *mut LeanObject,
    mut v_inst_4171_: *mut LeanObject,
    mut v_inst_4172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    v___x_4173_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_4171_, v_inst_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Lean_addRawTrace___redArg___lam__0(
    mut v_ref_4174_: *mut LeanObject,
    mut v_msg_4175_: *mut LeanObject,
    mut v_s_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_4177_: u64 = 0;
    let mut v_traces_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4177_ = lean_ctor_get_uint64(
                    v_s_4176_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4178_ = lean_ctor_get(v_s_4176_, 0);
                v_isSharedCheck_4187_ = (!lean_is_exclusive(v_s_4176_)) as u8;
                if v_isSharedCheck_4187_ == 0 {
                    v___x_4180_ = v_s_4176_;
                    v_isShared_4181_ = v_isSharedCheck_4187_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_traces_4178_);
                    lean_dec(v_s_4176_);
                    v___x_4180_ = lean_box(0);
                    v_isShared_4181_ = v_isSharedCheck_4187_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4182_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4182_, 0, v_ref_4174_);
                lean_ctor_set(v___x_4182_, 1, v_msg_4175_);
                v___x_4183_ = l_Lean_PersistentArray_push___redArg(v_traces_4178_, v___x_4182_);
                if v_isShared_4181_ == 0 {
                    lean_ctor_set(v___x_4180_, 0, v___x_4183_);
                    v___x_4185_ = v___x_4180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4186_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4177_,
                    );
                    v___x_4185_ = v_reuseFailAlloc_4186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addRawTrace___redArg___lam__1(
    mut v_inst_4188_: *mut LeanObject,
    mut v_ref_4189_: *mut LeanObject,
    mut v_msg_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4191_ = lean_ctor_get(v_inst_4188_, 0);
    lean_inc(v_modifyTraceState_4191_);
    lean_dec_ref(v_inst_4188_);
    v___f_4192_ = lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4192_, 0, v_ref_4189_);
    lean_closure_set(v___f_4192_, 1, v_msg_4190_);
    v___x_4193_ = lean_apply_1(v_modifyTraceState_4191_, v___f_4192_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_addRawTrace___redArg___lam__2(
    mut v_inst_4194_: *mut LeanObject,
    mut v_inst_4195_: *mut LeanObject,
    mut v_msg_4196_: *mut LeanObject,
    mut v_toBind_4197_: *mut LeanObject,
    mut v_ref_4198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    v___f_4199_ = lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4199_, 0, v_inst_4194_);
    lean_closure_set(v___f_4199_, 1, v_ref_4198_);
    v___x_4200_ = lean_apply_1(v_inst_4195_, v_msg_4196_);
    v___x_4201_ = lean_apply_4(
        v_toBind_4197_,
        lean_box(0),
        lean_box(0),
        v___x_4200_,
        v___f_4199_,
    );
    return v___x_4201_;
}
pub unsafe fn l_Lean_addRawTrace___redArg(
    mut v_inst_4202_: *mut LeanObject,
    mut v_inst_4203_: *mut LeanObject,
    mut v_inst_4204_: *mut LeanObject,
    mut v_inst_4205_: *mut LeanObject,
    mut v_msg_4206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4207_ = lean_ctor_get(v_inst_4202_, 1);
    lean_inc_n(v_toBind_4207_, 2);
    lean_dec_ref(v_inst_4202_);
    v_getRef_4208_ = lean_ctor_get(v_inst_4204_, 0);
    lean_inc(v_getRef_4208_);
    lean_dec_ref(v_inst_4204_);
    v___f_4209_ = lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4209_, 0, v_inst_4203_);
    lean_closure_set(v___f_4209_, 1, v_inst_4205_);
    lean_closure_set(v___f_4209_, 2, v_msg_4206_);
    lean_closure_set(v___f_4209_, 3, v_toBind_4207_);
    v___x_4210_ = lean_apply_4(
        v_toBind_4207_,
        lean_box(0),
        lean_box(0),
        v_getRef_4208_,
        v___f_4209_,
    );
    return v___x_4210_;
}
pub unsafe fn l_Lean_addRawTrace(
    mut v_m_4211_: *mut LeanObject,
    mut v_inst_4212_: *mut LeanObject,
    mut v_inst_4213_: *mut LeanObject,
    mut v_inst_4214_: *mut LeanObject,
    mut v_inst_4215_: *mut LeanObject,
    mut v_msg_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_addRawTrace___redArg(
        v_inst_4212_,
        v_inst_4213_,
        v_inst_4214_,
        v_inst_4215_,
        v_msg_4216_,
    );
    return v___x_4217_;
}
pub unsafe fn _init_l_Lean_addTrace___redArg___lam__0___closed__0() -> f64 {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: f64 = 0.0;
    v___x_4218_ = lean_unsigned_to_nat(0);
    v___x_4219_ = lean_float_of_nat(v___x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Lean_addTrace___redArg___lam__0(
    mut v_cls_4223_: *mut LeanObject,
    mut v_msg_4224_: *mut LeanObject,
    mut v_ref_4225_: *mut LeanObject,
    mut v_s_4226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_4227_: u64 = 0;
    let mut v_traces_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: f64 = 0.0;
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4227_ = lean_ctor_get_uint64(
                    v_s_4226_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4228_ = lean_ctor_get(v_s_4226_, 0);
                v_isSharedCheck_4244_ = (!lean_is_exclusive(v_s_4226_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4230_ = v_s_4226_;
                    v_isShared_4231_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_traces_4228_);
                    lean_dec(v_s_4226_);
                    v___x_4230_ = lean_box(0);
                    v_isShared_4231_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4232_ = lean_box(0);
                v___x_4233_ = lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                v___x_4234_ = 0;
                v___x_4235_ = l_Lean_addTrace___redArg___lam__0___closed__1;
                v___x_4236_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4236_, 0, v_cls_4223_);
                lean_ctor_set(v___x_4236_, 1, v___x_4232_);
                lean_ctor_set(v___x_4236_, 2, v___x_4235_);
                lean_ctor_set_float(
                    v___x_4236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4233_,
                );
                lean_ctor_set_float(
                    v___x_4236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4233_,
                );
                lean_ctor_set_uint8(
                    v___x_4236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4234_,
                );
                v___x_4237_ = l_Lean_addTrace___redArg___lam__0___closed__2;
                v___x_4238_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4238_, 0, v___x_4236_);
                lean_ctor_set(v___x_4238_, 1, v_msg_4224_);
                lean_ctor_set(v___x_4238_, 2, v___x_4237_);
                v___x_4239_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v_ref_4225_);
                lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                v___x_4240_ = l_Lean_PersistentArray_push___redArg(v_traces_4228_, v___x_4239_);
                if v_isShared_4231_ == 0 {
                    lean_ctor_set(v___x_4230_, 0, v___x_4240_);
                    v___x_4242_ = v___x_4230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4227_,
                    );
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___redArg___lam__1(
    mut v_inst_4245_: *mut LeanObject,
    mut v_cls_4246_: *mut LeanObject,
    mut v_ref_4247_: *mut LeanObject,
    mut v_msg_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyTraceState_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4249_ = lean_ctor_get(v_inst_4245_, 0);
    lean_inc(v_modifyTraceState_4249_);
    lean_dec_ref(v_inst_4245_);
    v___f_4250_ = lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4250_, 0, v_cls_4246_);
    lean_closure_set(v___f_4250_, 1, v_msg_4248_);
    lean_closure_set(v___f_4250_, 2, v_ref_4247_);
    v___x_4251_ = lean_apply_1(v_modifyTraceState_4249_, v___f_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_addTrace___redArg___lam__2(
    mut v_inst_4252_: *mut LeanObject,
    mut v_cls_4253_: *mut LeanObject,
    mut v_inst_4254_: *mut LeanObject,
    mut v_msg_4255_: *mut LeanObject,
    mut v_toBind_4256_: *mut LeanObject,
    mut v_ref_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___f_4258_ = lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4258_, 0, v_inst_4252_);
    lean_closure_set(v___f_4258_, 1, v_cls_4253_);
    lean_closure_set(v___f_4258_, 2, v_ref_4257_);
    v___x_4259_ = lean_apply_1(v_inst_4254_, v_msg_4255_);
    v___x_4260_ = lean_apply_4(
        v_toBind_4256_,
        lean_box(0),
        lean_box(0),
        v___x_4259_,
        v___f_4258_,
    );
    return v___x_4260_;
}
pub unsafe fn l_Lean_addTrace___redArg(
    mut v_inst_4261_: *mut LeanObject,
    mut v_inst_4262_: *mut LeanObject,
    mut v_inst_4263_: *mut LeanObject,
    mut v_inst_4264_: *mut LeanObject,
    mut v_cls_4265_: *mut LeanObject,
    mut v_msg_4266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4267_ = lean_ctor_get(v_inst_4261_, 1);
    lean_inc_n(v_toBind_4267_, 2);
    lean_dec_ref(v_inst_4261_);
    v_getRef_4268_ = lean_ctor_get(v_inst_4263_, 0);
    lean_inc(v_getRef_4268_);
    lean_dec_ref(v_inst_4263_);
    v___f_4269_ = lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4269_, 0, v_inst_4262_);
    lean_closure_set(v___f_4269_, 1, v_cls_4265_);
    lean_closure_set(v___f_4269_, 2, v_inst_4264_);
    lean_closure_set(v___f_4269_, 3, v_msg_4266_);
    lean_closure_set(v___f_4269_, 4, v_toBind_4267_);
    v___x_4270_ = lean_apply_4(
        v_toBind_4267_,
        lean_box(0),
        lean_box(0),
        v_getRef_4268_,
        v___f_4269_,
    );
    return v___x_4270_;
}
pub unsafe fn l_Lean_addTrace(
    mut v_m_4271_: *mut LeanObject,
    mut v_inst_4272_: *mut LeanObject,
    mut v_inst_4273_: *mut LeanObject,
    mut v_inst_4274_: *mut LeanObject,
    mut v_inst_4275_: *mut LeanObject,
    mut v_cls_4276_: *mut LeanObject,
    mut v_msg_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_addTrace___redArg(
        v_inst_4272_,
        v_inst_4273_,
        v_inst_4274_,
        v_inst_4275_,
        v_cls_4276_,
        v_msg_4277_,
    );
    return v___x_4278_;
}
pub unsafe fn l_Lean_trace___redArg___lam__0(
    mut v_toPure_4279_: *mut LeanObject,
    mut v_msg_4280_: *mut LeanObject,
    mut v_inst_4281_: *mut LeanObject,
    mut v_inst_4282_: *mut LeanObject,
    mut v_inst_4283_: *mut LeanObject,
    mut v_inst_4284_: *mut LeanObject,
    mut v_cls_4285_: *mut LeanObject,
    mut v_____do__lift_4286_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4286_ == 0 {
        let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_cls_4285_);
        lean_dec(v_inst_4284_);
        lean_dec_ref(v_inst_4283_);
        lean_dec_ref(v_inst_4282_);
        lean_dec_ref(v_inst_4281_);
        lean_dec_ref(v_msg_4280_);
        v___x_4287_ = lean_box(0);
        v___x_4288_ = lean_apply_2(v_toPure_4279_, lean_box(0), v___x_4287_);
        return v___x_4288_;
    } else {
        let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_4279_);
        v___x_4289_ = lean_box(0);
        v___x_4290_ = lean_apply_1(v_msg_4280_, v___x_4289_);
        v___x_4291_ = l_Lean_addTrace___redArg(
            v_inst_4281_,
            v_inst_4282_,
            v_inst_4283_,
            v_inst_4284_,
            v_cls_4285_,
            v___x_4290_,
        );
        return v___x_4291_;
    }
}
pub unsafe fn l_Lean_trace___redArg___lam__0___boxed(
    mut v_toPure_4292_: *mut LeanObject,
    mut v_msg_4293_: *mut LeanObject,
    mut v_inst_4294_: *mut LeanObject,
    mut v_inst_4295_: *mut LeanObject,
    mut v_inst_4296_: *mut LeanObject,
    mut v_inst_4297_: *mut LeanObject,
    mut v_cls_4298_: *mut LeanObject,
    mut v_____do__lift_4299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_148__boxed_4300_: u8 = 0;
    let mut v_res_4301_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_148__boxed_4300_ = (lean_unbox(v_____do__lift_4299_) as u8);
    v_res_4301_ = l_Lean_trace___redArg___lam__0(
        v_toPure_4292_,
        v_msg_4293_,
        v_inst_4294_,
        v_inst_4295_,
        v_inst_4296_,
        v_inst_4297_,
        v_cls_4298_,
        v_____do__lift_148__boxed_4300_,
    );
    return v_res_4301_;
}
pub unsafe fn l_Lean_trace___redArg(
    mut v_inst_4302_: *mut LeanObject,
    mut v_inst_4303_: *mut LeanObject,
    mut v_inst_4304_: *mut LeanObject,
    mut v_inst_4305_: *mut LeanObject,
    mut v_inst_4306_: *mut LeanObject,
    mut v_cls_4307_: *mut LeanObject,
    mut v_msg_4308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4309_ = lean_ctor_get(v_inst_4302_, 0);
    v_toBind_4310_ = lean_ctor_get(v_inst_4302_, 1);
    lean_inc_n(v_toBind_4310_, 3);
    v_getInheritedTraceOptions_4311_ = lean_ctor_get(v_inst_4303_, 2);
    lean_inc(v_getInheritedTraceOptions_4311_);
    v_toPure_4312_ = lean_ctor_get(v_toApplicative_4309_, 1);
    lean_inc_n(v_toPure_4312_, 2);
    lean_inc(v_cls_4307_);
    v___f_4313_ = lean_alloc_closure(
        l_Lean_trace___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_4313_, 0, v_toPure_4312_);
    lean_closure_set(v___f_4313_, 1, v_msg_4308_);
    lean_closure_set(v___f_4313_, 2, v_inst_4302_);
    lean_closure_set(v___f_4313_, 3, v_inst_4303_);
    lean_closure_set(v___f_4313_, 4, v_inst_4304_);
    lean_closure_set(v___f_4313_, 5, v_inst_4305_);
    lean_closure_set(v___f_4313_, 6, v_cls_4307_);
    v___f_4314_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4314_, 0, v_toPure_4312_);
    lean_closure_set(v___f_4314_, 1, v_cls_4307_);
    lean_closure_set(v___f_4314_, 2, v_toBind_4310_);
    lean_closure_set(v___f_4314_, 3, v_inst_4306_);
    v___x_4315_ = lean_apply_4(
        v_toBind_4310_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4311_,
        v___f_4314_,
    );
    v___x_4316_ = lean_apply_4(
        v_toBind_4310_,
        lean_box(0),
        lean_box(0),
        v___x_4315_,
        v___f_4313_,
    );
    return v___x_4316_;
}
pub unsafe fn l_Lean_trace(
    mut v_m_4317_: *mut LeanObject,
    mut v_inst_4318_: *mut LeanObject,
    mut v_inst_4319_: *mut LeanObject,
    mut v_inst_4320_: *mut LeanObject,
    mut v_inst_4321_: *mut LeanObject,
    mut v_inst_4322_: *mut LeanObject,
    mut v_cls_4323_: *mut LeanObject,
    mut v_msg_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4325_ = lean_ctor_get(v_inst_4318_, 0);
    v_toBind_4326_ = lean_ctor_get(v_inst_4318_, 1);
    lean_inc_n(v_toBind_4326_, 3);
    v_getInheritedTraceOptions_4327_ = lean_ctor_get(v_inst_4319_, 2);
    lean_inc(v_getInheritedTraceOptions_4327_);
    v_toPure_4328_ = lean_ctor_get(v_toApplicative_4325_, 1);
    lean_inc_n(v_toPure_4328_, 2);
    lean_inc(v_cls_4323_);
    v___f_4329_ = lean_alloc_closure(
        l_Lean_trace___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_4329_, 0, v_toPure_4328_);
    lean_closure_set(v___f_4329_, 1, v_msg_4324_);
    lean_closure_set(v___f_4329_, 2, v_inst_4318_);
    lean_closure_set(v___f_4329_, 3, v_inst_4319_);
    lean_closure_set(v___f_4329_, 4, v_inst_4320_);
    lean_closure_set(v___f_4329_, 5, v_inst_4321_);
    lean_closure_set(v___f_4329_, 6, v_cls_4323_);
    v___f_4330_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4330_, 0, v_toPure_4328_);
    lean_closure_set(v___f_4330_, 1, v_cls_4323_);
    lean_closure_set(v___f_4330_, 2, v_toBind_4326_);
    lean_closure_set(v___f_4330_, 3, v_inst_4322_);
    v___x_4331_ = lean_apply_4(
        v_toBind_4326_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4327_,
        v___f_4330_,
    );
    v___x_4332_ = lean_apply_4(
        v_toBind_4326_,
        lean_box(0),
        lean_box(0),
        v___x_4331_,
        v___f_4329_,
    );
    return v___x_4332_;
}
pub unsafe fn l_Lean_traceM___redArg___lam__0(
    mut v_inst_4333_: *mut LeanObject,
    mut v_inst_4334_: *mut LeanObject,
    mut v_inst_4335_: *mut LeanObject,
    mut v_inst_4336_: *mut LeanObject,
    mut v_cls_4337_: *mut LeanObject,
    mut v_msg_4338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Lean_addTrace___redArg(
        v_inst_4333_,
        v_inst_4334_,
        v_inst_4335_,
        v_inst_4336_,
        v_cls_4337_,
        v_msg_4338_,
    );
    return v___x_4339_;
}
pub unsafe fn l_Lean_traceM___redArg___lam__1(
    mut v_toPure_4340_: *mut LeanObject,
    mut v_toBind_4341_: *mut LeanObject,
    mut v_mkMsg_4342_: *mut LeanObject,
    mut v___f_4343_: *mut LeanObject,
    mut v_____do__lift_4344_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4344_ == 0 {
        let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4343_);
        lean_dec(v_mkMsg_4342_);
        lean_dec(v_toBind_4341_);
        v___x_4345_ = lean_box(0);
        v___x_4346_ = lean_apply_2(v_toPure_4340_, lean_box(0), v___x_4345_);
        return v___x_4346_;
    } else {
        let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_4340_);
        v___x_4347_ = lean_apply_4(
            v_toBind_4341_,
            lean_box(0),
            lean_box(0),
            v_mkMsg_4342_,
            v___f_4343_,
        );
        return v___x_4347_;
    }
}
pub unsafe fn l_Lean_traceM___redArg___lam__1___boxed(
    mut v_toPure_4348_: *mut LeanObject,
    mut v_toBind_4349_: *mut LeanObject,
    mut v_mkMsg_4350_: *mut LeanObject,
    mut v___f_4351_: *mut LeanObject,
    mut v_____do__lift_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_154__boxed_4353_: u8 = 0;
    let mut v_res_4354_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_154__boxed_4353_ = (lean_unbox(v_____do__lift_4352_) as u8);
    v_res_4354_ = l_Lean_traceM___redArg___lam__1(
        v_toPure_4348_,
        v_toBind_4349_,
        v_mkMsg_4350_,
        v___f_4351_,
        v_____do__lift_154__boxed_4353_,
    );
    return v_res_4354_;
}
pub unsafe fn l_Lean_traceM___redArg(
    mut v_inst_4355_: *mut LeanObject,
    mut v_inst_4356_: *mut LeanObject,
    mut v_inst_4357_: *mut LeanObject,
    mut v_inst_4358_: *mut LeanObject,
    mut v_inst_4359_: *mut LeanObject,
    mut v_cls_4360_: *mut LeanObject,
    mut v_mkMsg_4361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4362_ = lean_ctor_get(v_inst_4355_, 0);
    v_toBind_4363_ = lean_ctor_get(v_inst_4355_, 1);
    lean_inc_n(v_toBind_4363_, 4);
    v_getInheritedTraceOptions_4364_ = lean_ctor_get(v_inst_4356_, 2);
    lean_inc(v_getInheritedTraceOptions_4364_);
    v_toPure_4365_ = lean_ctor_get(v_toApplicative_4362_, 1);
    lean_inc_n(v_toPure_4365_, 2);
    lean_inc(v_cls_4360_);
    v___f_4366_ = lean_alloc_closure(
        l_Lean_traceM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4366_, 0, v_inst_4355_);
    lean_closure_set(v___f_4366_, 1, v_inst_4356_);
    lean_closure_set(v___f_4366_, 2, v_inst_4357_);
    lean_closure_set(v___f_4366_, 3, v_inst_4358_);
    lean_closure_set(v___f_4366_, 4, v_cls_4360_);
    v___f_4367_ = lean_alloc_closure(
        l_Lean_traceM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4367_, 0, v_toPure_4365_);
    lean_closure_set(v___f_4367_, 1, v_toBind_4363_);
    lean_closure_set(v___f_4367_, 2, v_mkMsg_4361_);
    lean_closure_set(v___f_4367_, 3, v___f_4366_);
    v___f_4368_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4368_, 0, v_toPure_4365_);
    lean_closure_set(v___f_4368_, 1, v_cls_4360_);
    lean_closure_set(v___f_4368_, 2, v_toBind_4363_);
    lean_closure_set(v___f_4368_, 3, v_inst_4359_);
    v___x_4369_ = lean_apply_4(
        v_toBind_4363_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4364_,
        v___f_4368_,
    );
    v___x_4370_ = lean_apply_4(
        v_toBind_4363_,
        lean_box(0),
        lean_box(0),
        v___x_4369_,
        v___f_4367_,
    );
    return v___x_4370_;
}
pub unsafe fn l_Lean_traceM(
    mut v_m_4371_: *mut LeanObject,
    mut v_inst_4372_: *mut LeanObject,
    mut v_inst_4373_: *mut LeanObject,
    mut v_inst_4374_: *mut LeanObject,
    mut v_inst_4375_: *mut LeanObject,
    mut v_inst_4376_: *mut LeanObject,
    mut v_cls_4377_: *mut LeanObject,
    mut v_mkMsg_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4379_ = lean_ctor_get(v_inst_4372_, 0);
    v_toBind_4380_ = lean_ctor_get(v_inst_4372_, 1);
    lean_inc_n(v_toBind_4380_, 4);
    v_getInheritedTraceOptions_4381_ = lean_ctor_get(v_inst_4373_, 2);
    lean_inc(v_getInheritedTraceOptions_4381_);
    v_toPure_4382_ = lean_ctor_get(v_toApplicative_4379_, 1);
    lean_inc_n(v_toPure_4382_, 2);
    lean_inc(v_cls_4377_);
    v___f_4383_ = lean_alloc_closure(
        l_Lean_traceM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4383_, 0, v_inst_4372_);
    lean_closure_set(v___f_4383_, 1, v_inst_4373_);
    lean_closure_set(v___f_4383_, 2, v_inst_4374_);
    lean_closure_set(v___f_4383_, 3, v_inst_4375_);
    lean_closure_set(v___f_4383_, 4, v_cls_4377_);
    v___f_4384_ = lean_alloc_closure(
        l_Lean_traceM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4384_, 0, v_toPure_4382_);
    lean_closure_set(v___f_4384_, 1, v_toBind_4380_);
    lean_closure_set(v___f_4384_, 2, v_mkMsg_4378_);
    lean_closure_set(v___f_4384_, 3, v___f_4383_);
    v___f_4385_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4385_, 0, v_toPure_4382_);
    lean_closure_set(v___f_4385_, 1, v_cls_4377_);
    lean_closure_set(v___f_4385_, 2, v_toBind_4380_);
    lean_closure_set(v___f_4385_, 3, v_inst_4376_);
    v___x_4386_ = lean_apply_4(
        v_toBind_4380_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_4381_,
        v___f_4385_,
    );
    v___x_4387_ = lean_apply_4(
        v_toBind_4380_,
        lean_box(0),
        lean_box(0),
        v___x_4386_,
        v___f_4384_,
    );
    return v___x_4387_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(
    mut v_x_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_4389_: *mut LeanObject = core::ptr::null_mut();
    v_msg_4389_ = lean_ctor_get(v_x_4388_, 1);
    lean_inc_ref(v_msg_4389_);
    return v_msg_4389_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(
    mut v_x_4390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4391_: *mut LeanObject = core::ptr::null_mut();
    v_res_4391_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_4390_);
    lean_dec_ref(v_x_4390_);
    return v_res_4391_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(
    mut v_ref_4392_: *mut LeanObject,
    mut v_msg_4393_: *mut LeanObject,
    mut v_oldTraces_4394_: *mut LeanObject,
    mut v_s_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_4396_: u64 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4396_ = lean_ctor_get_uint64(
                    v_s_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4405_ = (!lean_is_exclusive(v_s_4395_)) as u8;
                if v_isSharedCheck_4405_ == 0 {
                    v_unused_4406_ = lean_ctor_get(v_s_4395_, 0);
                    lean_dec(v_unused_4406_);
                    v___x_4398_ = v_s_4395_;
                    v_isShared_4399_ = v_isSharedCheck_4405_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_4395_);
                    v___x_4398_ = lean_box(0);
                    v_isShared_4399_ = v_isSharedCheck_4405_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4400_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4400_, 0, v_ref_4392_);
                lean_ctor_set(v___x_4400_, 1, v_msg_4393_);
                v___x_4401_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4394_, v___x_4400_);
                if v_isShared_4399_ == 0 {
                    lean_ctor_set(v___x_4398_, 0, v___x_4401_);
                    v___x_4403_ = v___x_4398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4404_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4396_,
                    );
                    v___x_4403_ = v_reuseFailAlloc_4404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(
    mut v_ref_4407_: *mut LeanObject,
    mut v_oldTraces_4408_: *mut LeanObject,
    mut v_modifyTraceState_4409_: *mut LeanObject,
    mut v_msg_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    v___f_4411_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4411_, 0, v_ref_4407_);
    lean_closure_set(v___f_4411_, 1, v_msg_4410_);
    lean_closure_set(v___f_4411_, 2, v_oldTraces_4408_);
    v___x_4412_ = lean_apply_1(v_modifyTraceState_4409_, v___f_4411_);
    return v___x_4412_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(
    mut v___f_4432_: *mut LeanObject,
    mut v_data_4433_: *mut LeanObject,
    mut v_msg_4434_: *mut LeanObject,
    mut v_inst_4435_: *mut LeanObject,
    mut v_toBind_4436_: *mut LeanObject,
    mut v___f_4437_: *mut LeanObject,
    mut v_____do__lift_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4441_: usize = 0;
    let mut v___x_4442_: usize = 0;
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_4438_);
    v___x_4440_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9;
    v_sz_4441_ = lean_array_size(v___x_4439_);
    v___x_4442_ = 0usize;
    v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4440_,
        v___f_4432_,
        v_sz_4441_,
        v___x_4442_,
        v___x_4439_,
    );
    v_msg_4444_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v_msg_4444_, 0, v_data_4433_);
    lean_ctor_set(v_msg_4444_, 1, v_msg_4434_);
    lean_ctor_set(v_msg_4444_, 2, v___x_4443_);
    v___x_4445_ = lean_apply_1(v_inst_4435_, v_msg_4444_);
    v___x_4446_ = lean_apply_4(
        v_toBind_4436_,
        lean_box(0),
        lean_box(0),
        v___x_4445_,
        v___f_4437_,
    );
    return v___x_4446_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(
    mut v___f_4447_: *mut LeanObject,
    mut v_data_4448_: *mut LeanObject,
    mut v_msg_4449_: *mut LeanObject,
    mut v_inst_4450_: *mut LeanObject,
    mut v_toBind_4451_: *mut LeanObject,
    mut v___f_4452_: *mut LeanObject,
    mut v_____do__lift_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4454_: *mut LeanObject = core::ptr::null_mut();
    v_res_4454_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(
        v___f_4447_,
        v_data_4448_,
        v_msg_4449_,
        v_inst_4450_,
        v_toBind_4451_,
        v___f_4452_,
        v_____do__lift_4453_,
    );
    lean_dec_ref(v_____do__lift_4453_);
    return v_res_4454_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(
    mut v_ref_4455_: *mut LeanObject,
    mut v_withRef_4456_: *mut LeanObject,
    mut v___x_4457_: *mut LeanObject,
    mut v_oldRef_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4459_ = l_Lean_replaceRef(v_ref_4455_, v_oldRef_4458_);
    v___x_4460_ = lean_apply_3(v_withRef_4456_, lean_box(0), v_ref_4459_, v___x_4457_);
    return v___x_4460_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(
    mut v_ref_4461_: *mut LeanObject,
    mut v_withRef_4462_: *mut LeanObject,
    mut v___x_4463_: *mut LeanObject,
    mut v_oldRef_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(
        v_ref_4461_,
        v_withRef_4462_,
        v___x_4463_,
        v_oldRef_4464_,
    );
    lean_dec(v_oldRef_4464_);
    lean_dec(v_ref_4461_);
    return v_res_4465_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(
    mut v_inst_4467_: *mut LeanObject,
    mut v_inst_4468_: *mut LeanObject,
    mut v_inst_4469_: *mut LeanObject,
    mut v_inst_4470_: *mut LeanObject,
    mut v_oldTraces_4471_: *mut LeanObject,
    mut v_data_4472_: *mut LeanObject,
    mut v_ref_4473_: *mut LeanObject,
    mut v_msg_4474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4475_ = lean_ctor_get(v_inst_4467_, 0);
    lean_inc_ref(v_toApplicative_4475_);
    v_toBind_4476_ = lean_ctor_get(v_inst_4467_, 1);
    lean_inc_n(v_toBind_4476_, 4);
    lean_dec_ref(v_inst_4467_);
    v_modifyTraceState_4477_ = lean_ctor_get(v_inst_4468_, 0);
    lean_inc(v_modifyTraceState_4477_);
    v_getTraceState_4478_ = lean_ctor_get(v_inst_4468_, 1);
    lean_inc(v_getTraceState_4478_);
    lean_dec_ref(v_inst_4468_);
    v_toPure_4479_ = lean_ctor_get(v_toApplicative_4475_, 1);
    lean_inc(v_toPure_4479_);
    lean_dec_ref(v_toApplicative_4475_);
    v_getRef_4480_ = lean_ctor_get(v_inst_4469_, 0);
    lean_inc(v_getRef_4480_);
    v_withRef_4481_ = lean_ctor_get(v_inst_4469_, 1);
    lean_inc(v_withRef_4481_);
    lean_dec_ref(v_inst_4469_);
    v___f_4482_ = lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4482_, 0, v_toPure_4479_);
    v___x_4483_ = lean_apply_4(
        v_toBind_4476_,
        lean_box(0),
        lean_box(0),
        v_getTraceState_4478_,
        v___f_4482_,
    );
    v___f_4484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0;
    lean_inc(v_ref_4473_);
    v___f_4485_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4485_, 0, v_ref_4473_);
    lean_closure_set(v___f_4485_, 1, v_oldTraces_4471_);
    lean_closure_set(v___f_4485_, 2, v_modifyTraceState_4477_);
    v___f_4486_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4486_, 0, v___f_4484_);
    lean_closure_set(v___f_4486_, 1, v_data_4472_);
    lean_closure_set(v___f_4486_, 2, v_msg_4474_);
    lean_closure_set(v___f_4486_, 3, v_inst_4470_);
    lean_closure_set(v___f_4486_, 4, v_toBind_4476_);
    lean_closure_set(v___f_4486_, 5, v___f_4485_);
    v___x_4487_ = lean_apply_4(
        v_toBind_4476_,
        lean_box(0),
        lean_box(0),
        v___x_4483_,
        v___f_4486_,
    );
    v___f_4488_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4488_, 0, v_ref_4473_);
    lean_closure_set(v___f_4488_, 1, v_withRef_4481_);
    lean_closure_set(v___f_4488_, 2, v___x_4487_);
    v___x_4489_ = lean_apply_4(
        v_toBind_4476_,
        lean_box(0),
        lean_box(0),
        v_getRef_4480_,
        v___f_4488_,
    );
    return v___x_4489_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode(
    mut v_m_4490_: *mut LeanObject,
    mut v_inst_4491_: *mut LeanObject,
    mut v_inst_4492_: *mut LeanObject,
    mut v_inst_4493_: *mut LeanObject,
    mut v_inst_4494_: *mut LeanObject,
    mut v_oldTraces_4495_: *mut LeanObject,
    mut v_data_4496_: *mut LeanObject,
    mut v_ref_4497_: *mut LeanObject,
    mut v_msg_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    v___x_4499_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(
        v_inst_4491_,
        v_inst_4492_,
        v_inst_4493_,
        v_inst_4494_,
        v_oldTraces_4495_,
        v_data_4496_,
        v_ref_4497_,
        v_msg_4498_,
    );
    return v___x_4499_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(
    mut v_name_4500_: *mut LeanObject,
    mut v_decl_4501_: *mut LeanObject,
    mut v_ref_4502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4518_: u8 = 0;
    let mut v_unused_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4504_ = lean_ctor_get(v_decl_4501_, 0);
                v_descr_4505_ = lean_ctor_get(v_decl_4501_, 1);
                v_deprecation_x3f_4506_ = lean_ctor_get(v_decl_4501_, 2);
                v___x_4507_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4508_ = (lean_unbox(v_defValue_4504_) as u8);
                lean_ctor_set_uint8(v___x_4507_, 0 as u32, v___x_4508_);
                lean_inc(v_deprecation_x3f_4506_);
                lean_inc_ref(v_descr_4505_);
                lean_inc_n(v_name_4500_, 2);
                v___x_4509_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4509_, 0, v_name_4500_);
                lean_ctor_set(v___x_4509_, 1, v_ref_4502_);
                lean_ctor_set(v___x_4509_, 2, v___x_4507_);
                lean_ctor_set(v___x_4509_, 3, v_descr_4505_);
                lean_ctor_set(v___x_4509_, 4, v_deprecation_x3f_4506_);
                v___x_4510_ = lean_register_option(v_name_4500_, v___x_4509_);
                if lean_obj_tag(v___x_4510_) == 0 {
                    v_isSharedCheck_4518_ = (!lean_is_exclusive(v___x_4510_)) as u8;
                    if v_isSharedCheck_4518_ == 0 {
                        v_unused_4519_ = lean_ctor_get(v___x_4510_, 0);
                        lean_dec(v_unused_4519_);
                        v___x_4512_ = v___x_4510_;
                        v_isShared_4513_ = v_isSharedCheck_4518_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4510_);
                        v___x_4512_ = lean_box(0);
                        v_isShared_4513_ = v_isSharedCheck_4518_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_4500_);
                    v_a_4520_ = lean_ctor_get(v___x_4510_, 0);
                    v_isSharedCheck_4527_ = (!lean_is_exclusive(v___x_4510_)) as u8;
                    if v_isSharedCheck_4527_ == 0 {
                        v___x_4522_ = v___x_4510_;
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4520_);
                        lean_dec(v___x_4510_);
                        v___x_4522_ = lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_4504_);
                v___x_4514_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4514_, 0, v_name_4500_);
                lean_ctor_set(v___x_4514_, 1, v_defValue_4504_);
                if v_isShared_4513_ == 0 {
                    lean_ctor_set(v___x_4512_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
                    v___x_4516_ = v_reuseFailAlloc_4517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4516_;
            }
            3 => {
                if v_isShared_4523_ == 0 {
                    v___x_4525_ = v___x_4522_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
                    v___x_4525_ = v_reuseFailAlloc_4526_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4528_: *mut LeanObject,
    mut v_decl_4529_: *mut LeanObject,
    mut v_ref_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4532_: *mut LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_4528_, v_decl_4529_, v_ref_4530_);
    lean_dec_ref(v_decl_4529_);
    return v_res_4532_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    v___x_4548_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4549_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4550_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4551_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4548_, v___x_4549_, v___x_4550_);
    return v___x_4551_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(
    mut v_a_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4553_: *mut LeanObject = core::ptr::null_mut();
    v_res_4553_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
    return v_res_4553_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(
    mut v_name_4554_: *mut LeanObject,
    mut v_decl_4555_: *mut LeanObject,
    mut v_ref_4556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_unused_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4576_: u8 = 0;
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4558_ = lean_ctor_get(v_decl_4555_, 0);
                v_descr_4559_ = lean_ctor_get(v_decl_4555_, 1);
                v_deprecation_x3f_4560_ = lean_ctor_get(v_decl_4555_, 2);
                lean_inc(v_defValue_4558_);
                v___x_4561_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4561_, 0, v_defValue_4558_);
                lean_inc(v_deprecation_x3f_4560_);
                lean_inc_ref(v_descr_4559_);
                lean_inc_n(v_name_4554_, 2);
                v___x_4562_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4562_, 0, v_name_4554_);
                lean_ctor_set(v___x_4562_, 1, v_ref_4556_);
                lean_ctor_set(v___x_4562_, 2, v___x_4561_);
                lean_ctor_set(v___x_4562_, 3, v_descr_4559_);
                lean_ctor_set(v___x_4562_, 4, v_deprecation_x3f_4560_);
                v___x_4563_ = lean_register_option(v_name_4554_, v___x_4562_);
                if lean_obj_tag(v___x_4563_) == 0 {
                    v_isSharedCheck_4571_ = (!lean_is_exclusive(v___x_4563_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v_unused_4572_ = lean_ctor_get(v___x_4563_, 0);
                        lean_dec(v_unused_4572_);
                        v___x_4565_ = v___x_4563_;
                        v_isShared_4566_ = v_isSharedCheck_4571_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4563_);
                        v___x_4565_ = lean_box(0);
                        v_isShared_4566_ = v_isSharedCheck_4571_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_4554_);
                    v_a_4573_ = lean_ctor_get(v___x_4563_, 0);
                    v_isSharedCheck_4580_ = (!lean_is_exclusive(v___x_4563_)) as u8;
                    if v_isSharedCheck_4580_ == 0 {
                        v___x_4575_ = v___x_4563_;
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4573_);
                        lean_dec(v___x_4563_);
                        v___x_4575_ = lean_box(0);
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_4558_);
                v___x_4567_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4567_, 0, v_name_4554_);
                lean_ctor_set(v___x_4567_, 1, v_defValue_4558_);
                if v_isShared_4566_ == 0 {
                    lean_ctor_set(v___x_4565_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4569_;
            }
            3 => {
                if v_isShared_4576_ == 0 {
                    v___x_4578_ = v___x_4575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
                    v___x_4578_ = v_reuseFailAlloc_4579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4581_: *mut LeanObject,
    mut v_decl_4582_: *mut LeanObject,
    mut v_ref_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4585_: *mut LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_4581_, v_decl_4582_, v_ref_4583_);
    lean_dec_ref(v_decl_4582_);
    return v_res_4585_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    v___x_4602_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4603_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4605_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_4602_, v___x_4603_, v___x_4604_);
    return v___x_4605_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(
    mut v_a_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4607_: *mut LeanObject = core::ptr::null_mut();
    v_res_4607_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
    return v_res_4607_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    v___x_4625_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4626_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4627_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4628_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4625_, v___x_4626_, v___x_4627_);
    return v___x_4628_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(
    mut v_a_4629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4630_: *mut LeanObject = core::ptr::null_mut();
    v_res_4630_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
    return v_res_4630_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(
    mut v_name_4631_: *mut LeanObject,
    mut v_decl_4632_: *mut LeanObject,
    mut v_ref_4633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v_unused_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4635_ = lean_ctor_get(v_decl_4632_, 0);
                v_descr_4636_ = lean_ctor_get(v_decl_4632_, 1);
                v_deprecation_x3f_4637_ = lean_ctor_get(v_decl_4632_, 2);
                lean_inc(v_defValue_4635_);
                v___x_4638_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4638_, 0, v_defValue_4635_);
                lean_inc(v_deprecation_x3f_4637_);
                lean_inc_ref(v_descr_4636_);
                lean_inc_n(v_name_4631_, 2);
                v___x_4639_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4639_, 0, v_name_4631_);
                lean_ctor_set(v___x_4639_, 1, v_ref_4633_);
                lean_ctor_set(v___x_4639_, 2, v___x_4638_);
                lean_ctor_set(v___x_4639_, 3, v_descr_4636_);
                lean_ctor_set(v___x_4639_, 4, v_deprecation_x3f_4637_);
                v___x_4640_ = lean_register_option(v_name_4631_, v___x_4639_);
                if lean_obj_tag(v___x_4640_) == 0 {
                    v_isSharedCheck_4648_ = (!lean_is_exclusive(v___x_4640_)) as u8;
                    if v_isSharedCheck_4648_ == 0 {
                        v_unused_4649_ = lean_ctor_get(v___x_4640_, 0);
                        lean_dec(v_unused_4649_);
                        v___x_4642_ = v___x_4640_;
                        v_isShared_4643_ = v_isSharedCheck_4648_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4640_);
                        v___x_4642_ = lean_box(0);
                        v_isShared_4643_ = v_isSharedCheck_4648_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_4631_);
                    v_a_4650_ = lean_ctor_get(v___x_4640_, 0);
                    v_isSharedCheck_4657_ = (!lean_is_exclusive(v___x_4640_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4652_ = v___x_4640_;
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4650_);
                        lean_dec(v___x_4640_);
                        v___x_4652_ = lean_box(0);
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_4635_);
                v___x_4644_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4644_, 0, v_name_4631_);
                lean_ctor_set(v___x_4644_, 1, v_defValue_4635_);
                if v_isShared_4643_ == 0 {
                    lean_ctor_set(v___x_4642_, 0, v___x_4644_);
                    v___x_4646_ = v___x_4642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
                    v___x_4646_ = v_reuseFailAlloc_4647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4646_;
            }
            3 => {
                if v_isShared_4653_ == 0 {
                    v___x_4655_ = v___x_4652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
                    v___x_4655_ = v_reuseFailAlloc_4656_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4658_: *mut LeanObject,
    mut v_decl_4659_: *mut LeanObject,
    mut v_ref_4660_: *mut LeanObject,
    mut v_a_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4662_: *mut LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_4658_, v_decl_4659_, v_ref_4660_);
    lean_dec_ref(v_decl_4659_);
    return v_res_4662_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    v___x_4679_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4681_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4682_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_4679_, v___x_4680_, v___x_4681_);
    return v___x_4682_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(
    mut v_a_4683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4684_: *mut LeanObject = core::ptr::null_mut();
    v_res_4684_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
    return v_res_4684_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4702_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4703_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4704_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4705_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4702_, v___x_4703_, v___x_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(
    mut v_a_4706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4707_: *mut LeanObject = core::ptr::null_mut();
    v_res_4707_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
    return v_res_4707_;
}
pub unsafe fn l_Lean_trace_profiler_isExporting(mut v_opts_4708_: *mut LeanObject) -> u8 {
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    v___x_4709_ = l_Lean_KVMap_instValueBool;
    v___x_4710_ = l_Lean_KVMap_instValueString;
    v___x_4711_ = l_Lean_trace_profiler_output;
    v___x_4712_ = l_Lean_Option_get_x3f___redArg(v___x_4710_, v_opts_4708_, v___x_4711_);
    if lean_obj_tag(v___x_4712_) == 0 {
        let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4715_: u8 = 0;
        v___x_4713_ = l_Lean_trace_profiler_serve;
        v___x_4714_ = l_Lean_Option_get___redArg(v___x_4709_, v_opts_4708_, v___x_4713_);
        v___x_4715_ = (lean_unbox(v___x_4714_) as u8);
        lean_dec(v___x_4714_);
        return v___x_4715_;
    } else {
        let mut v___x_4716_: u8 = 0;
        lean_dec_ref_known(v___x_4712_, 1);
        v___x_4716_ = 1;
        return v___x_4716_;
    }
}
pub unsafe fn l_Lean_trace_profiler_isExporting___boxed(
    mut v_opts_4717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4718_: u8 = 0;
    let mut v_r_4719_: *mut LeanObject = core::ptr::null_mut();
    v_res_4718_ = l_Lean_trace_profiler_isExporting(v_opts_4717_);
    lean_dec_ref(v_opts_4717_);
    v_r_4719_ = lean_box((v_res_4718_) as usize);
    return v_r_4719_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    v___x_4739_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4740_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4741_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4742_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4739_, v___x_4740_, v___x_4741_);
    return v___x_4742_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(
    mut v_a_4743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4744_: *mut LeanObject = core::ptr::null_mut();
    v_res_4744_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
    return v_res_4744_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0()
-> f64 {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: f64 = 0.0;
    v___x_4745_ = lean_unsigned_to_nat(1000000000);
    v___x_4746_ = lean_float_of_nat(v___x_4745_);
    return v___x_4746_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(
    mut v_toApplicative_4747_: *mut LeanObject,
    mut v_start_4748_: *mut LeanObject,
    mut v_a_4749_: *mut LeanObject,
    mut v_stop_4750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: f64 = 0.0;
    let mut v___x_4753_: f64 = 0.0;
    let mut v___x_4754_: f64 = 0.0;
    let mut v___x_4755_: f64 = 0.0;
    let mut v___x_4756_: f64 = 0.0;
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_4751_ = lean_ctor_get(v_toApplicative_4747_, 1);
    lean_inc(v_toPure_4751_);
    lean_dec_ref(v_toApplicative_4747_);
    v___x_4752_ = lean_float_of_nat(v_start_4748_);
    v___x_4753_ = lean_float_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once
        ),
        _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0,
    );
    v___x_4754_ = lean_float_div(v___x_4752_, v___x_4753_);
    v___x_4755_ = lean_float_of_nat(v_stop_4750_);
    v___x_4756_ = lean_float_div(v___x_4755_, v___x_4753_);
    v___x_4757_ = lean_box_float(v___x_4754_);
    v___x_4758_ = lean_box_float(v___x_4756_);
    v___x_4759_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4759_, 0, v___x_4757_);
    lean_ctor_set(v___x_4759_, 1, v___x_4758_);
    v___x_4760_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4760_, 0, v_a_4749_);
    lean_ctor_set(v___x_4760_, 1, v___x_4759_);
    v___x_4761_ = lean_apply_2(v_toPure_4751_, lean_box(0), v___x_4760_);
    return v___x_4761_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(
    mut v_toApplicative_4762_: *mut LeanObject,
    mut v_start_4763_: *mut LeanObject,
    mut v_toBind_4764_: *mut LeanObject,
    mut v___x_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    v___f_4767_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4767_, 0, v_toApplicative_4762_);
    lean_closure_set(v___f_4767_, 1, v_start_4763_);
    lean_closure_set(v___f_4767_, 2, v_a_4766_);
    v___x_4768_ = lean_apply_4(
        v_toBind_4764_,
        lean_box(0),
        lean_box(0),
        v___x_4765_,
        v___f_4767_,
    );
    return v___x_4768_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(
    mut v_toApplicative_4769_: *mut LeanObject,
    mut v_toBind_4770_: *mut LeanObject,
    mut v___x_4771_: *mut LeanObject,
    mut v_act_4772_: *mut LeanObject,
    mut v_start_4773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_4770_);
    v___f_4774_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4774_, 0, v_toApplicative_4769_);
    lean_closure_set(v___f_4774_, 1, v_start_4773_);
    lean_closure_set(v___f_4774_, 2, v_toBind_4770_);
    lean_closure_set(v___f_4774_, 3, v___x_4771_);
    v___x_4775_ = lean_apply_4(
        v_toBind_4770_,
        lean_box(0),
        lean_box(0),
        v_act_4772_,
        v___f_4774_,
    );
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(
    mut v_toApplicative_4776_: *mut LeanObject,
    mut v_start_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_stop_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: f64 = 0.0;
    let mut v___x_4782_: f64 = 0.0;
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_4780_ = lean_ctor_get(v_toApplicative_4776_, 1);
    lean_inc(v_toPure_4780_);
    lean_dec_ref(v_toApplicative_4776_);
    v___x_4781_ = lean_float_of_nat(v_start_4777_);
    v___x_4782_ = lean_float_of_nat(v_stop_4779_);
    v___x_4783_ = lean_box_float(v___x_4781_);
    v___x_4784_ = lean_box_float(v___x_4782_);
    v___x_4785_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4785_, 0, v___x_4783_);
    lean_ctor_set(v___x_4785_, 1, v___x_4784_);
    v___x_4786_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4786_, 0, v_a_4778_);
    lean_ctor_set(v___x_4786_, 1, v___x_4785_);
    v___x_4787_ = lean_apply_2(v_toPure_4780_, lean_box(0), v___x_4786_);
    return v___x_4787_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(
    mut v_toApplicative_4788_: *mut LeanObject,
    mut v_start_4789_: *mut LeanObject,
    mut v_toBind_4790_: *mut LeanObject,
    mut v___x_4791_: *mut LeanObject,
    mut v_a_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    v___f_4793_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4793_, 0, v_toApplicative_4788_);
    lean_closure_set(v___f_4793_, 1, v_start_4789_);
    lean_closure_set(v___f_4793_, 2, v_a_4792_);
    v___x_4794_ = lean_apply_4(
        v_toBind_4790_,
        lean_box(0),
        lean_box(0),
        v___x_4791_,
        v___f_4793_,
    );
    return v___x_4794_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(
    mut v_toApplicative_4795_: *mut LeanObject,
    mut v_toBind_4796_: *mut LeanObject,
    mut v___x_4797_: *mut LeanObject,
    mut v_act_4798_: *mut LeanObject,
    mut v_start_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_4796_);
    v___f_4800_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4800_, 0, v_toApplicative_4795_);
    lean_closure_set(v___f_4800_, 1, v_start_4799_);
    lean_closure_set(v___f_4800_, 2, v_toBind_4796_);
    lean_closure_set(v___f_4800_, 3, v___x_4797_);
    v___x_4801_ = lean_apply_4(
        v_toBind_4796_,
        lean_box(0),
        lean_box(0),
        v_act_4798_,
        v___f_4800_,
    );
    return v___x_4801_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(
    mut v_inst_4804_: *mut LeanObject,
    mut v_inst_4805_: *mut LeanObject,
    mut v_opts_4806_: *mut LeanObject,
    mut v_act_4807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    v___x_4808_ = l_Lean_KVMap_instValueBool;
    v___x_4809_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4810_ = l_Lean_Option_get___redArg(v___x_4808_, v_opts_4806_, v___x_4809_);
    v___x_4811_ = (lean_unbox(v___x_4810_) as u8);
    lean_dec(v___x_4810_);
    if v___x_4811_ == 0 {
        let mut v_toApplicative_4812_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4812_ = lean_ctor_get(v_inst_4804_, 0);
        lean_inc_ref(v_toApplicative_4812_);
        v_toBind_4813_ = lean_ctor_get(v_inst_4804_, 1);
        lean_inc_n(v_toBind_4813_, 2);
        lean_dec_ref(v_inst_4804_);
        v___x_4814_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_4815_ = lean_apply_2(v_inst_4805_, lean_box(0), v___x_4814_);
        lean_inc(v___x_4815_);
        v___f_4816_ = lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_4816_, 0, v_toApplicative_4812_);
        lean_closure_set(v___f_4816_, 1, v_toBind_4813_);
        lean_closure_set(v___f_4816_, 2, v___x_4815_);
        lean_closure_set(v___f_4816_, 3, v_act_4807_);
        v___x_4817_ = lean_apply_4(
            v_toBind_4813_,
            lean_box(0),
            lean_box(0),
            v___x_4815_,
            v___f_4816_,
        );
        return v___x_4817_;
    } else {
        let mut v_toApplicative_4818_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4818_ = lean_ctor_get(v_inst_4804_, 0);
        lean_inc_ref(v_toApplicative_4818_);
        v_toBind_4819_ = lean_ctor_get(v_inst_4804_, 1);
        lean_inc_n(v_toBind_4819_, 2);
        lean_dec_ref(v_inst_4804_);
        v___x_4820_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_4821_ = lean_apply_2(v_inst_4805_, lean_box(0), v___x_4820_);
        lean_inc(v___x_4821_);
        v___f_4822_ = lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_4822_, 0, v_toApplicative_4818_);
        lean_closure_set(v___f_4822_, 1, v_toBind_4819_);
        lean_closure_set(v___f_4822_, 2, v___x_4821_);
        lean_closure_set(v___f_4822_, 3, v_act_4807_);
        v___x_4823_ = lean_apply_4(
            v_toBind_4819_,
            lean_box(0),
            lean_box(0),
            v___x_4821_,
            v___f_4822_,
        );
        return v___x_4823_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(
    mut v_inst_4824_: *mut LeanObject,
    mut v_inst_4825_: *mut LeanObject,
    mut v_opts_4826_: *mut LeanObject,
    mut v_act_4827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4828_: *mut LeanObject = core::ptr::null_mut();
    v_res_4828_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(
        v_inst_4824_,
        v_inst_4825_,
        v_opts_4826_,
        v_act_4827_,
    );
    lean_dec_ref(v_opts_4826_);
    return v_res_4828_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop(
    mut v_00_u03b1_4829_: *mut LeanObject,
    mut v_m_4830_: *mut LeanObject,
    mut v_inst_4831_: *mut LeanObject,
    mut v_inst_4832_: *mut LeanObject,
    mut v_opts_4833_: *mut LeanObject,
    mut v_act_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: u8 = 0;
    v___x_4835_ = l_Lean_KVMap_instValueBool;
    v___x_4836_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4837_ = l_Lean_Option_get___redArg(v___x_4835_, v_opts_4833_, v___x_4836_);
    v___x_4838_ = (lean_unbox(v___x_4837_) as u8);
    lean_dec(v___x_4837_);
    if v___x_4838_ == 0 {
        let mut v_toApplicative_4839_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4839_ = lean_ctor_get(v_inst_4831_, 0);
        lean_inc_ref(v_toApplicative_4839_);
        v_toBind_4840_ = lean_ctor_get(v_inst_4831_, 1);
        lean_inc_n(v_toBind_4840_, 2);
        lean_dec_ref(v_inst_4831_);
        v___x_4841_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_4842_ = lean_apply_2(v_inst_4832_, lean_box(0), v___x_4841_);
        lean_inc(v___x_4842_);
        v___f_4843_ = lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_4843_, 0, v_toApplicative_4839_);
        lean_closure_set(v___f_4843_, 1, v_toBind_4840_);
        lean_closure_set(v___f_4843_, 2, v___x_4842_);
        lean_closure_set(v___f_4843_, 3, v_act_4834_);
        v___x_4844_ = lean_apply_4(
            v_toBind_4840_,
            lean_box(0),
            lean_box(0),
            v___x_4842_,
            v___f_4843_,
        );
        return v___x_4844_;
    } else {
        let mut v_toApplicative_4845_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4845_ = lean_ctor_get(v_inst_4831_, 0);
        lean_inc_ref(v_toApplicative_4845_);
        v_toBind_4846_ = lean_ctor_get(v_inst_4831_, 1);
        lean_inc_n(v_toBind_4846_, 2);
        lean_dec_ref(v_inst_4831_);
        v___x_4847_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_4848_ = lean_apply_2(v_inst_4832_, lean_box(0), v___x_4847_);
        lean_inc(v___x_4848_);
        v___f_4849_ = lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_4849_, 0, v_toApplicative_4845_);
        lean_closure_set(v___f_4849_, 1, v_toBind_4846_);
        lean_closure_set(v___f_4849_, 2, v___x_4848_);
        lean_closure_set(v___f_4849_, 3, v_act_4834_);
        v___x_4850_ = lean_apply_4(
            v_toBind_4846_,
            lean_box(0),
            lean_box(0),
            v___x_4848_,
            v___f_4849_,
        );
        return v___x_4850_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(
    mut v_00_u03b1_4851_: *mut LeanObject,
    mut v_m_4852_: *mut LeanObject,
    mut v_inst_4853_: *mut LeanObject,
    mut v_inst_4854_: *mut LeanObject,
    mut v_opts_4855_: *mut LeanObject,
    mut v_act_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4857_: *mut LeanObject = core::ptr::null_mut();
    v_res_4857_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(
        v_00_u03b1_4851_,
        v_m_4852_,
        v_inst_4853_,
        v_inst_4854_,
        v_opts_4855_,
        v_act_4856_,
    );
    lean_dec_ref(v_opts_4855_);
    return v_res_4857_;
}
pub unsafe fn _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0() -> f64 {
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: f64 = 0.0;
    v___x_4858_ = lean_unsigned_to_nat(1000);
    v___x_4859_ = lean_float_of_nat(v___x_4858_);
    return v___x_4859_;
}
pub unsafe fn l_Lean_trace_profiler_threshold_unitAdjusted(mut v_o_4860_: *mut LeanObject) -> f64 {
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: u8 = 0;
    v___x_4861_ = l_Lean_KVMap_instValueBool;
    v___x_4862_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4863_ = l_Lean_Option_get___redArg(v___x_4861_, v_o_4860_, v___x_4862_);
    v___x_4864_ = (lean_unbox(v___x_4863_) as u8);
    lean_dec(v___x_4863_);
    if v___x_4864_ == 0 {
        let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4868_: f64 = 0.0;
        let mut v___x_4869_: f64 = 0.0;
        let mut v___x_4870_: f64 = 0.0;
        v___x_4865_ = l_Lean_KVMap_instValueNat;
        v___x_4866_ = l_Lean_trace_profiler_threshold;
        v___x_4867_ = l_Lean_Option_get___redArg(v___x_4865_, v_o_4860_, v___x_4866_);
        v___x_4868_ = lean_float_of_nat(v___x_4867_);
        v___x_4869_ = lean_float_once(
            core::ptr::addr_of_mut!(l_Lean_trace_profiler_threshold_unitAdjusted___closed__0),
            core::ptr::addr_of_mut!(l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once),
            _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0,
        );
        v___x_4870_ = lean_float_div(v___x_4868_, v___x_4869_);
        return v___x_4870_;
    } else {
        let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4874_: f64 = 0.0;
        v___x_4871_ = l_Lean_KVMap_instValueNat;
        v___x_4872_ = l_Lean_trace_profiler_threshold;
        v___x_4873_ = l_Lean_Option_get___redArg(v___x_4871_, v_o_4860_, v___x_4872_);
        v___x_4874_ = lean_float_of_nat(v___x_4873_);
        return v___x_4874_;
    }
}
pub unsafe fn l_Lean_trace_profiler_threshold_unitAdjusted___boxed(
    mut v_o_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4876_: f64 = 0.0;
    let mut v_r_4877_: *mut LeanObject = core::ptr::null_mut();
    v_res_4876_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_4875_);
    lean_dec_ref(v_o_4875_);
    v_r_4877_ = lean_box_float(v_res_4876_);
    return v_r_4877_;
}
pub unsafe fn _init_l_Lean_instMonadAlwaysExceptEIO___closed__0() -> *mut LeanObject {
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    v___x_4878_ = l_instMonadExceptOfEIO(lean_box(0));
    return v___x_4878_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptEIO(
    mut v_00_u03b5_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    v___x_4880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instMonadAlwaysExceptEIO___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instMonadAlwaysExceptEIO___closed__0_once),
        _init_l_Lean_instMonadAlwaysExceptEIO___closed__0,
    );
    return v___x_4880_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateT___redArg(
    mut v_inst_4881_: *mut LeanObject,
    mut v_always_4882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_always_4882_);
    v___f_4883_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_4883_, 0, v_always_4882_);
    lean_closure_set(v___f_4883_, 1, v_inst_4881_);
    v___f_4884_ = lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4884_, 0, v_always_4882_);
    v___x_4885_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4885_, 0, v___f_4883_);
    lean_ctor_set(v___x_4885_, 1, v___f_4884_);
    return v___x_4885_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateT(
    mut v_m_4886_: *mut LeanObject,
    mut v_inst_4887_: *mut LeanObject,
    mut v_00_u03b5_4888_: *mut LeanObject,
    mut v_00_u03c3_4889_: *mut LeanObject,
    mut v_always_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_4887_, v_always_4890_);
    return v___x_4891_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(
    mut v_always_4892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_always_4892_);
    v___f_4893_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4893_, 0, v_always_4892_);
    v___f_4894_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4894_, 0, v_always_4892_);
    v___x_4895_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4895_, 0, v___f_4893_);
    lean_ctor_set(v___x_4895_, 1, v___f_4894_);
    return v___x_4895_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateRefT_x27(
    mut v_m_4896_: *mut LeanObject,
    mut v_00_u03b5_4897_: *mut LeanObject,
    mut v_00_u03c9_4898_: *mut LeanObject,
    mut v_00_u03c3_4899_: *mut LeanObject,
    mut v_always_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_4900_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptReaderT___redArg(
    mut v_always_4902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_always_4902_);
    v___f_4903_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4903_, 0, v_always_4902_);
    v___f_4904_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4904_, 0, v_always_4902_);
    v___x_4905_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4905_, 0, v___f_4903_);
    lean_ctor_set(v___x_4905_, 1, v___f_4904_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptReaderT(
    mut v_m_4906_: *mut LeanObject,
    mut v_00_u03b5_4907_: *mut LeanObject,
    mut v_00_u03c1_4908_: *mut LeanObject,
    mut v_always_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    v___x_4910_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_4909_);
    return v___x_4910_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(
    mut v_always_4911_: *mut LeanObject,
    mut v_inst_4912_: *mut LeanObject,
    mut v_inst_4913_: *mut LeanObject,
    mut v_inst_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    v___x_4915_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_4912_,
        v_inst_4913_,
        v_inst_4914_,
        v_always_4911_,
    );
    return v___x_4915_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptMonadCacheT(
    mut v_00_u03b1_4916_: *mut LeanObject,
    mut v_m_4917_: *mut LeanObject,
    mut v_00_u03b5_4918_: *mut LeanObject,
    mut v_00_u03c9_4919_: *mut LeanObject,
    mut v_00_u03b2_4920_: *mut LeanObject,
    mut v_always_4921_: *mut LeanObject,
    mut v_inst_4922_: *mut LeanObject,
    mut v_inst_4923_: *mut LeanObject,
    mut v_inst_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    v___x_4925_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_4922_,
        v_inst_4923_,
        v_inst_4924_,
        v_always_4921_,
    );
    return v___x_4925_;
}
pub unsafe fn l_Lean_TraceResult_toEmoji(mut v_x_4932_: u8) -> *mut LeanObject {
    match v_x_4932_ {
        0 => {
            let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
            v___x_4933_ = l_Lean_checkEmoji___closed__0;
            return v___x_4933_;
        }
        1 => {
            let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
            v___x_4934_ = l_Lean_crossEmoji___closed__0;
            return v___x_4934_;
        }
        _ => {
            let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
            v___x_4935_ = l_Lean_bombEmoji___closed__0;
            return v___x_4935_;
        }
    }
}
pub unsafe fn l_Lean_TraceResult_toEmoji___boxed(
    mut v_x_4936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_31__boxed_4937_: u8 = 0;
    let mut v_res_4938_: *mut LeanObject = core::ptr::null_mut();
    v_x_31__boxed_4937_ = (lean_unbox(v_x_4936_) as u8);
    v_res_4938_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_4937_);
    return v_res_4938_;
}
pub unsafe fn l_Lean_instExceptToTraceResultBool___lam__0(mut v_x_4939_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4939_) == 0 {
        let mut v___x_4940_: u8 = 0;
        v___x_4940_ = 2;
        return v___x_4940_;
    } else {
        let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: u8 = 0;
        v_a_4941_ = lean_ctor_get(v_x_4939_, 0);
        v___x_4942_ = (lean_unbox(v_a_4941_) as u8);
        if v___x_4942_ == 0 {
            let mut v___x_4943_: u8 = 0;
            v___x_4943_ = 1;
            return v___x_4943_;
        } else {
            let mut v___x_4944_: u8 = 0;
            v___x_4944_ = 0;
            return v___x_4944_;
        }
    }
}
pub unsafe fn l_Lean_instExceptToTraceResultBool___lam__0___boxed(
    mut v_x_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4946_: u8 = 0;
    let mut v_r_4947_: *mut LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_4945_);
    lean_dec_ref(v_x_4945_);
    v_r_4947_ = lean_box((v_res_4946_) as usize);
    return v_r_4947_;
}
pub unsafe fn l_Lean_instExceptToTraceResultBool(
    mut v_00_u03b5_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4950_: *mut LeanObject = core::ptr::null_mut();
    v___f_4950_ = l_Lean_instExceptToTraceResultBool___closed__0;
    return v___f_4950_;
}
pub unsafe fn l_Lean_instExceptToTraceResultOption___lam__0(mut v_x_4951_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4951_) == 0 {
        let mut v___x_4952_: u8 = 0;
        v___x_4952_ = 2;
        return v___x_4952_;
    } else {
        let mut v_a_4953_: *mut LeanObject = core::ptr::null_mut();
        v_a_4953_ = lean_ctor_get(v_x_4951_, 0);
        if lean_obj_tag(v_a_4953_) == 0 {
            let mut v___x_4954_: u8 = 0;
            v___x_4954_ = 1;
            return v___x_4954_;
        } else {
            let mut v___x_4955_: u8 = 0;
            v___x_4955_ = 0;
            return v___x_4955_;
        }
    }
}
pub unsafe fn l_Lean_instExceptToTraceResultOption___lam__0___boxed(
    mut v_x_4956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4957_: u8 = 0;
    let mut v_r_4958_: *mut LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_4956_);
    lean_dec_ref(v_x_4956_);
    v_r_4958_ = lean_box((v_res_4957_) as usize);
    return v_r_4958_;
}
pub unsafe fn l_Lean_instExceptToTraceResultOption(
    mut v_00_u03b1_4960_: *mut LeanObject,
    mut v_00_u03b5_4961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4962_: *mut LeanObject = core::ptr::null_mut();
    v___f_4962_ = l_Lean_instExceptToTraceResultOption___closed__0;
    return v___f_4962_;
}
pub unsafe fn l_Lean_instExceptToTraceResultExpr___lam__0(mut v_x_4963_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4963_) == 0 {
        let mut v___x_4964_: u8 = 0;
        v___x_4964_ = 2;
        return v___x_4964_;
    } else {
        let mut v_a_4965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: u8 = 0;
        v_a_4965_ = lean_ctor_get(v_x_4963_, 0);
        v___x_4966_ = l_Lean_Expr_hasSyntheticSorry(v_a_4965_);
        if v___x_4966_ == 0 {
            let mut v___x_4967_: u8 = 0;
            v___x_4967_ = 0;
            return v___x_4967_;
        } else {
            let mut v___x_4968_: u8 = 0;
            v___x_4968_ = 1;
            return v___x_4968_;
        }
    }
}
pub unsafe fn l_Lean_instExceptToTraceResultExpr___lam__0___boxed(
    mut v_x_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4970_: u8 = 0;
    let mut v_r_4971_: *mut LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_4969_);
    lean_dec_ref(v_x_4969_);
    v_r_4971_ = lean_box((v_res_4970_) as usize);
    return v_r_4971_;
}
pub unsafe fn l_Lean_instExceptToTraceResultExpr(
    mut v_00_u03b5_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4974_: *mut LeanObject = core::ptr::null_mut();
    v___f_4974_ = l_Lean_instExceptToTraceResultExpr___closed__0;
    return v___f_4974_;
}
pub unsafe fn l_Lean_instExceptToTraceResult___lam__0(mut v_x_4975_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4975_) == 0 {
        let mut v___x_4976_: u8 = 0;
        v___x_4976_ = 2;
        return v___x_4976_;
    } else {
        let mut v___x_4977_: u8 = 0;
        v___x_4977_ = 0;
        return v___x_4977_;
    }
}
pub unsafe fn l_Lean_instExceptToTraceResult___lam__0___boxed(
    mut v_x_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4979_: u8 = 0;
    let mut v_r_4980_: *mut LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_instExceptToTraceResult___lam__0(v_x_4978_);
    lean_dec_ref(v_x_4978_);
    v_r_4980_ = lean_box((v_res_4979_) as usize);
    return v_r_4980_;
}
pub unsafe fn l_Lean_instExceptToTraceResult(
    mut v_00_u03b1_4982_: *mut LeanObject,
    mut v_00_u03b5_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4984_: *mut LeanObject = core::ptr::null_mut();
    v___f_4984_ = l_Lean_instExceptToTraceResult___closed__0;
    return v___f_4984_;
}
pub unsafe fn l_Except_toTraceResult___redArg(
    mut v_inst_4985_: *mut LeanObject,
    mut v_e_4986_: *mut LeanObject,
) -> u8 {
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    v___x_4987_ = lean_apply_1(v_inst_4985_, v_e_4986_);
    v___x_4988_ = (lean_unbox(v___x_4987_) as u8);
    return v___x_4988_;
}
pub unsafe fn l_Except_toTraceResult___redArg___boxed(
    mut v_inst_4989_: *mut LeanObject,
    mut v_e_4990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4991_: u8 = 0;
    let mut v_r_4992_: *mut LeanObject = core::ptr::null_mut();
    v_res_4991_ = l_Except_toTraceResult___redArg(v_inst_4989_, v_e_4990_);
    v_r_4992_ = lean_box((v_res_4991_) as usize);
    return v_r_4992_;
}
pub unsafe fn l_Except_toTraceResult(
    mut v_00_u03b1_4993_: *mut LeanObject,
    mut v_00_u03b5_4994_: *mut LeanObject,
    mut v_inst_4995_: *mut LeanObject,
    mut v_e_4996_: *mut LeanObject,
) -> u8 {
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    v___x_4997_ = lean_apply_1(v_inst_4995_, v_e_4996_);
    v___x_4998_ = (lean_unbox(v___x_4997_) as u8);
    return v___x_4998_;
}
pub unsafe fn l_Except_toTraceResult___boxed(
    mut v_00_u03b1_4999_: *mut LeanObject,
    mut v_00_u03b5_5000_: *mut LeanObject,
    mut v_inst_5001_: *mut LeanObject,
    mut v_e_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5003_: u8 = 0;
    let mut v_r_5004_: *mut LeanObject = core::ptr::null_mut();
    v_res_5003_ =
        l_Except_toTraceResult(v_00_u03b1_4999_, v_00_u03b5_5000_, v_inst_5001_, v_e_5002_);
    v_r_5004_ = lean_box((v_res_5003_) as usize);
    return v_r_5004_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    v___x_5006_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0;
    v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
    return v___x_5007_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(
    mut v_inst_5008_: *mut LeanObject,
    mut v_x_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5010_ = lean_ctor_get(v_inst_5008_, 0);
    lean_inc_ref(v_toApplicative_5010_);
    lean_dec_ref(v_inst_5008_);
    v_toPure_5011_ = lean_ctor_get(v_toApplicative_5010_, 1);
    lean_inc(v_toPure_5011_);
    lean_dec_ref(v_toApplicative_5010_);
    v___x_5012_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
    v___x_5013_ = lean_apply_2(v_toPure_5011_, lean_box(0), v___x_5012_);
    return v___x_5013_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(
    mut v_inst_5014_: *mut LeanObject,
    mut v_x_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5016_: *mut LeanObject = core::ptr::null_mut();
    v_res_5016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(
        v_inst_5014_,
        v_x_5015_,
    );
    lean_dec(v_x_5015_);
    return v_res_5016_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(
    mut v_oldTraces_5017_: *mut LeanObject,
    mut v_s_5018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tid_5019_: u64 = 0;
    let mut v_traces_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5023_: u8 = 0;
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_5019_ = lean_ctor_get_uint64(
                    v_s_5018_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5020_ = lean_ctor_get(v_s_5018_, 0);
                v_isSharedCheck_5028_ = (!lean_is_exclusive(v_s_5018_)) as u8;
                if v_isSharedCheck_5028_ == 0 {
                    v___x_5022_ = v_s_5018_;
                    v_isShared_5023_ = v_isSharedCheck_5028_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_traces_5020_);
                    lean_dec(v_s_5018_);
                    v___x_5022_ = lean_box(0);
                    v_isShared_5023_ = v_isSharedCheck_5028_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5024_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5017_, v_traces_5020_);
                lean_dec_ref(v_traces_5020_);
                if v_isShared_5023_ == 0 {
                    lean_ctor_set(v___x_5022_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5027_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5019_,
                    );
                    v___x_5026_ = v_reuseFailAlloc_5027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(
    mut v_always_5029_: *mut LeanObject,
    mut v_inst_5030_: *mut LeanObject,
    mut v_fst_5031_: *mut LeanObject,
    mut v_____r_5032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_5029_);
    v___x_5034_ = l_MonadExcept_ofExcept___redArg(v_inst_5030_, v___x_5033_, v_fst_5031_);
    return v___x_5034_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(
    mut v_inst_5035_: *mut LeanObject,
    mut v___x_5036_: *mut LeanObject,
    mut v_fst_5037_: *mut LeanObject,
    mut v_____r_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    v___x_5039_ = l_MonadExcept_ofExcept___redArg(v_inst_5035_, v___x_5036_, v_fst_5037_);
    return v___x_5039_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1()
-> *mut LeanObject {
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    v___x_5041_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0;
    v___x_5042_ = l_Lean_stringToMessageData(v___x_5041_);
    return v___x_5042_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(
    mut v_inst_5043_: *mut LeanObject,
    mut v_fst_5044_: *mut LeanObject,
    mut v_inst_5045_: *mut LeanObject,
    mut v_inst_5046_: *mut LeanObject,
    mut v_inst_5047_: *mut LeanObject,
    mut v_inst_5048_: *mut LeanObject,
    mut v_oldTraces_5049_: *mut LeanObject,
    mut v_ref_5050_: *mut LeanObject,
    mut v_toBind_5051_: *mut LeanObject,
    mut v___f_5052_: *mut LeanObject,
    mut v_cls_5053_: *mut LeanObject,
    mut v_collapsed_5054_: u8,
    mut v_tag_5055_: *mut LeanObject,
    mut v___x_5056_: u8,
    mut v_fst_5057_: f64,
    mut v_snd_5058_: f64,
    mut v_m_5059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: f64 = 0.0;
    let mut v_data_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_5060_ = lean_apply_1(v_inst_5043_, v_fst_5044_);
                v___x_5061_ = (lean_unbox(v_result_5060_) as u8);
                v___x_5062_ = l_Lean_TraceResult_toEmoji(v___x_5061_);
                v___x_5063_ = l_Lean_stringToMessageData(v___x_5062_);
                v___x_5064_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
                v___x_5065_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5065_, 0, v___x_5063_);
                lean_ctor_set(v___x_5065_, 1, v___x_5064_);
                v_m_5066_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_m_5066_, 0, v___x_5065_);
                lean_ctor_set(v_m_5066_, 1, v_m_5059_);
                v___x_5071_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5071_, 0, v_result_5060_);
                v___x_5072_ = lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                lean_inc_ref(v_tag_5055_);
                lean_inc_ref(v___x_5071_);
                lean_inc(v_cls_5053_);
                v_data_5073_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_5073_, 0, v_cls_5053_);
                lean_ctor_set(v_data_5073_, 1, v___x_5071_);
                lean_ctor_set(v_data_5073_, 2, v_tag_5055_);
                lean_ctor_set_float(
                    v_data_5073_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5072_,
                );
                lean_ctor_set_float(
                    v_data_5073_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5072_,
                );
                lean_ctor_set_uint8(
                    v_data_5073_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5054_,
                );
                if v___x_5056_ == 0 {
                    lean_dec_ref_known(v___x_5071_, 1);
                    lean_dec_ref(v_tag_5055_);
                    lean_dec(v_cls_5053_);
                    v_data_5068_ = v_data_5073_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_5073_, 3);
                    v_data_5074_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_5074_, 0, v_cls_5053_);
                    lean_ctor_set(v_data_5074_, 1, v___x_5071_);
                    lean_ctor_set(v_data_5074_, 2, v_tag_5055_);
                    lean_ctor_set_float(
                        v_data_5074_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_fst_5057_,
                    );
                    lean_ctor_set_float(
                        v_data_5074_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v_snd_5058_,
                    );
                    lean_ctor_set_uint8(
                        v_data_5074_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_5054_,
                    );
                    v_data_5068_ = v_data_5074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5069_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(
                    v_inst_5045_,
                    v_inst_5046_,
                    v_inst_5047_,
                    v_inst_5048_,
                    v_oldTraces_5049_,
                    v_data_5068_,
                    v_ref_5050_,
                    v_m_5066_,
                );
                v___x_5070_ = lean_apply_4(
                    v_toBind_5051_,
                    lean_box(0),
                    lean_box(0),
                    v___x_5069_,
                    v___f_5052_,
                );
                return v___x_5070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5075_: *mut LeanObject = *_args.add(0);
    let mut v_fst_5076_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5077_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5078_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5079_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5080_: *mut LeanObject = *_args.add(5);
    let mut v_oldTraces_5081_: *mut LeanObject = *_args.add(6);
    let mut v_ref_5082_: *mut LeanObject = *_args.add(7);
    let mut v_toBind_5083_: *mut LeanObject = *_args.add(8);
    let mut v___f_5084_: *mut LeanObject = *_args.add(9);
    let mut v_cls_5085_: *mut LeanObject = *_args.add(10);
    let mut v_collapsed_5086_: *mut LeanObject = *_args.add(11);
    let mut v_tag_5087_: *mut LeanObject = *_args.add(12);
    let mut v___x_5088_: *mut LeanObject = *_args.add(13);
    let mut v_fst_5089_: *mut LeanObject = *_args.add(14);
    let mut v_snd_5090_: *mut LeanObject = *_args.add(15);
    let mut v_m_5091_: *mut LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5092_: u8 = 0;
    let mut v___x_677__boxed_5093_: u8 = 0;
    let mut v_fst_678__boxed_5094_: f64 = 0.0;
    let mut v_snd_679__boxed_5095_: f64 = 0.0;
    let mut v_res_5096_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5092_ = (lean_unbox(v_collapsed_5086_) as u8);
    v___x_677__boxed_5093_ = (lean_unbox(v___x_5088_) as u8);
    v_fst_678__boxed_5094_ = lean_unbox_float(v_fst_5089_);
    lean_dec_ref(v_fst_5089_);
    v_snd_679__boxed_5095_ = lean_unbox_float(v_snd_5090_);
    lean_dec_ref(v_snd_5090_);
    v_res_5096_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(
        v_inst_5075_,
        v_fst_5076_,
        v_inst_5077_,
        v_inst_5078_,
        v_inst_5079_,
        v_inst_5080_,
        v_oldTraces_5081_,
        v_ref_5082_,
        v_toBind_5083_,
        v___f_5084_,
        v_cls_5085_,
        v_collapsed_boxed_5092_,
        v_tag_5087_,
        v___x_677__boxed_5093_,
        v_fst_678__boxed_5094_,
        v_snd_679__boxed_5095_,
        v_m_5091_,
    );
    return v_res_5096_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(
    mut v_always_5097_: *mut LeanObject,
    mut v_inst_5098_: *mut LeanObject,
    mut v_fst_5099_: *mut LeanObject,
    mut v_inst_5100_: *mut LeanObject,
    mut v_inst_5101_: *mut LeanObject,
    mut v_inst_5102_: *mut LeanObject,
    mut v_inst_5103_: *mut LeanObject,
    mut v_oldTraces_5104_: *mut LeanObject,
    mut v_toBind_5105_: *mut LeanObject,
    mut v_cls_5106_: *mut LeanObject,
    mut v_collapsed_5107_: u8,
    mut v_tag_5108_: *mut LeanObject,
    mut v___x_5109_: u8,
    mut v_fst_5110_: f64,
    mut v_snd_5111_: f64,
    mut v_msg_5112_: *mut LeanObject,
    mut v___f_5113_: *mut LeanObject,
    mut v_ref_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_always_5097_);
    v___x_5115_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_5097_);
    v_tryCatch_5116_ = lean_ctor_get(v_always_5097_, 1);
    lean_inc(v_tryCatch_5116_);
    lean_dec_ref(v_always_5097_);
    lean_inc_ref_n(v_fst_5099_, 2);
    lean_inc_ref(v_inst_5098_);
    v___f_5117_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5117_, 0, v_inst_5098_);
    lean_closure_set(v___f_5117_, 1, v___x_5115_);
    lean_closure_set(v___f_5117_, 2, v_fst_5099_);
    v___x_5118_ = lean_box((v_collapsed_5107_) as usize);
    v___x_5119_ = lean_box((v___x_5109_) as usize);
    v___x_5120_ = lean_box_float(v_fst_5110_);
    v___x_5121_ = lean_box_float(v_snd_5111_);
    lean_inc(v_toBind_5105_);
    v___f_5122_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    lean_closure_set(v___f_5122_, 0, v_inst_5100_);
    lean_closure_set(v___f_5122_, 1, v_fst_5099_);
    lean_closure_set(v___f_5122_, 2, v_inst_5098_);
    lean_closure_set(v___f_5122_, 3, v_inst_5101_);
    lean_closure_set(v___f_5122_, 4, v_inst_5102_);
    lean_closure_set(v___f_5122_, 5, v_inst_5103_);
    lean_closure_set(v___f_5122_, 6, v_oldTraces_5104_);
    lean_closure_set(v___f_5122_, 7, v_ref_5114_);
    lean_closure_set(v___f_5122_, 8, v_toBind_5105_);
    lean_closure_set(v___f_5122_, 9, v___f_5117_);
    lean_closure_set(v___f_5122_, 10, v_cls_5106_);
    lean_closure_set(v___f_5122_, 11, v___x_5118_);
    lean_closure_set(v___f_5122_, 12, v_tag_5108_);
    lean_closure_set(v___f_5122_, 13, v___x_5119_);
    lean_closure_set(v___f_5122_, 14, v___x_5120_);
    lean_closure_set(v___f_5122_, 15, v___x_5121_);
    v___x_5123_ = lean_apply_1(v_msg_5112_, v_fst_5099_);
    v___x_5124_ = lean_apply_3(v_tryCatch_5116_, lean_box(0), v___x_5123_, v___f_5113_);
    v___x_5125_ = lean_apply_4(
        v_toBind_5105_,
        lean_box(0),
        lean_box(0),
        v___x_5124_,
        v___f_5122_,
    );
    return v___x_5125_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_always_5126_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5127_: *mut LeanObject = *_args.add(1);
    let mut v_fst_5128_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5129_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5130_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5131_: *mut LeanObject = *_args.add(5);
    let mut v_inst_5132_: *mut LeanObject = *_args.add(6);
    let mut v_oldTraces_5133_: *mut LeanObject = *_args.add(7);
    let mut v_toBind_5134_: *mut LeanObject = *_args.add(8);
    let mut v_cls_5135_: *mut LeanObject = *_args.add(9);
    let mut v_collapsed_5136_: *mut LeanObject = *_args.add(10);
    let mut v_tag_5137_: *mut LeanObject = *_args.add(11);
    let mut v___x_5138_: *mut LeanObject = *_args.add(12);
    let mut v_fst_5139_: *mut LeanObject = *_args.add(13);
    let mut v_snd_5140_: *mut LeanObject = *_args.add(14);
    let mut v_msg_5141_: *mut LeanObject = *_args.add(15);
    let mut v___f_5142_: *mut LeanObject = *_args.add(16);
    let mut v_ref_5143_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5144_: u8 = 0;
    let mut v___x_729__boxed_5145_: u8 = 0;
    let mut v_fst_730__boxed_5146_: f64 = 0.0;
    let mut v_snd_731__boxed_5147_: f64 = 0.0;
    let mut v_res_5148_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5144_ = (lean_unbox(v_collapsed_5136_) as u8);
    v___x_729__boxed_5145_ = (lean_unbox(v___x_5138_) as u8);
    v_fst_730__boxed_5146_ = lean_unbox_float(v_fst_5139_);
    lean_dec_ref(v_fst_5139_);
    v_snd_731__boxed_5147_ = lean_unbox_float(v_snd_5140_);
    lean_dec_ref(v_snd_5140_);
    v_res_5148_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(
        v_always_5126_,
        v_inst_5127_,
        v_fst_5128_,
        v_inst_5129_,
        v_inst_5130_,
        v_inst_5131_,
        v_inst_5132_,
        v_oldTraces_5133_,
        v_toBind_5134_,
        v_cls_5135_,
        v_collapsed_boxed_5144_,
        v_tag_5137_,
        v___x_729__boxed_5145_,
        v_fst_730__boxed_5146_,
        v_snd_731__boxed_5147_,
        v_msg_5141_,
        v___f_5142_,
        v_ref_5143_,
    );
    return v_res_5148_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(
    mut v_inst_5149_: *mut LeanObject,
    mut v_inst_5150_: *mut LeanObject,
    mut v_inst_5151_: *mut LeanObject,
    mut v_inst_5152_: *mut LeanObject,
    mut v_always_5153_: *mut LeanObject,
    mut v_inst_5154_: *mut LeanObject,
    mut v_cls_5155_: *mut LeanObject,
    mut v_collapsed_5156_: u8,
    mut v_tag_5157_: *mut LeanObject,
    mut v_opts_5158_: *mut LeanObject,
    mut v_clsEnabled_5159_: u8,
    mut v_oldTraces_5160_: *mut LeanObject,
    mut v_msg_5161_: *mut LeanObject,
    mut v_resStartStop_5162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: u8 = 0;
    let mut v_toBind_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: f64 = 0.0;
    let mut v___x_5187_: f64 = 0.0;
    let mut v___x_5188_: f64 = 0.0;
    let mut v___x_5189_: f64 = 0.0;
    let mut v___x_5190_: u8 = 0;
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: u8 = 0;
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: f64 = 0.0;
    let mut v___x_5200_: f64 = 0.0;
    let mut v___x_5201_: f64 = 0.0;
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: f64 = 0.0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5163_ = l_Lean_KVMap_instValueBool;
                v_snd_5164_ = lean_ctor_get(v_resStartStop_5162_, 1);
                lean_inc(v_snd_5164_);
                v_fst_5165_ = lean_ctor_get(v_resStartStop_5162_, 0);
                lean_inc_n(v_fst_5165_, 2);
                lean_dec_ref(v_resStartStop_5162_);
                v_fst_5166_ = lean_ctor_get(v_snd_5164_, 0);
                lean_inc(v_fst_5166_);
                v_snd_5167_ = lean_ctor_get(v_snd_5164_, 1);
                lean_inc(v_snd_5167_);
                lean_dec(v_snd_5164_);
                lean_inc_ref_n(v_inst_5149_, 2);
                v___f_5168_ = lean_alloc_closure(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_5168_, 0, v_inst_5149_);
                lean_inc_ref(v_oldTraces_5160_);
                v___f_5169_ = lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_5169_, 0, v_oldTraces_5160_);
                lean_inc_ref(v_always_5153_);
                v___f_5170_ = lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_5170_, 0, v_always_5153_);
                lean_closure_set(v___f_5170_, 1, v_inst_5149_);
                lean_closure_set(v___f_5170_, 2, v_fst_5165_);
                v___x_5171_ = l_Lean_trace_profiler;
                v___x_5172_ = l_Lean_Option_get___redArg(v___x_5163_, v_opts_5158_, v___x_5171_);
                v___x_5191_ = (lean_unbox(v___x_5172_) as u8);
                if v___x_5191_ == 0 {
                    v___x_5192_ = (lean_unbox(v___x_5172_) as u8);
                    v___y_5180_ = v___x_5192_;
                    state = 2;
                    continue;
                } else {
                    v___x_5193_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5194_ =
                        l_Lean_Option_get___redArg(v___x_5163_, v_opts_5158_, v___x_5193_);
                    v___x_5195_ = (lean_unbox(v___x_5194_) as u8);
                    lean_dec(v___x_5194_);
                    if v___x_5195_ == 0 {
                        v___x_5196_ = l_Lean_KVMap_instValueNat;
                        v___x_5197_ = l_Lean_trace_profiler_threshold;
                        v___x_5198_ =
                            l_Lean_Option_get___redArg(v___x_5196_, v_opts_5158_, v___x_5197_);
                        v___x_5199_ = lean_float_of_nat(v___x_5198_);
                        v___x_5200_ = lean_float_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_trace_profiler_threshold_unitAdjusted___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once
                            ),
                            _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0,
                        );
                        v___x_5201_ = lean_float_div(v___x_5199_, v___x_5200_);
                        v___y_5186_ = v___x_5201_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5202_ = l_Lean_KVMap_instValueNat;
                        v___x_5203_ = l_Lean_trace_profiler_threshold;
                        v___x_5204_ =
                            l_Lean_Option_get___redArg(v___x_5202_, v_opts_5158_, v___x_5203_);
                        v___x_5205_ = lean_float_of_nat(v___x_5204_);
                        v___y_5186_ = v___x_5205_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_toBind_5174_ = lean_ctor_get(v_inst_5149_, 1);
                lean_inc_n(v_toBind_5174_, 2);
                v_getRef_5175_ = lean_ctor_get(v_inst_5151_, 0);
                lean_inc(v_getRef_5175_);
                v___x_5176_ = lean_box((v_collapsed_5156_) as usize);
                v___f_5177_ = lean_alloc_closure(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed as *mut core::ffi::c_void, 18, 17);
                lean_closure_set(v___f_5177_, 0, v_always_5153_);
                lean_closure_set(v___f_5177_, 1, v_inst_5149_);
                lean_closure_set(v___f_5177_, 2, v_fst_5165_);
                lean_closure_set(v___f_5177_, 3, v_inst_5154_);
                lean_closure_set(v___f_5177_, 4, v_inst_5150_);
                lean_closure_set(v___f_5177_, 5, v_inst_5151_);
                lean_closure_set(v___f_5177_, 6, v_inst_5152_);
                lean_closure_set(v___f_5177_, 7, v_oldTraces_5160_);
                lean_closure_set(v___f_5177_, 8, v_toBind_5174_);
                lean_closure_set(v___f_5177_, 9, v_cls_5155_);
                lean_closure_set(v___f_5177_, 10, v___x_5176_);
                lean_closure_set(v___f_5177_, 11, v_tag_5157_);
                lean_closure_set(v___f_5177_, 12, v___x_5172_);
                lean_closure_set(v___f_5177_, 13, v_fst_5166_);
                lean_closure_set(v___f_5177_, 14, v_snd_5167_);
                lean_closure_set(v___f_5177_, 15, v_msg_5161_);
                lean_closure_set(v___f_5177_, 16, v___f_5168_);
                v___x_5178_ = lean_apply_4(
                    v_toBind_5174_,
                    lean_box(0),
                    lean_box(0),
                    v_getRef_5175_,
                    v___f_5177_,
                );
                return v___x_5178_;
            }
            2 => {
                if v_clsEnabled_5159_ == 0 {
                    if v___y_5180_ == 0 {
                        lean_dec(v___x_5172_);
                        lean_dec_ref(v___f_5168_);
                        lean_dec(v_snd_5167_);
                        lean_dec(v_fst_5166_);
                        lean_dec(v_fst_5165_);
                        lean_dec(v_msg_5161_);
                        lean_dec_ref(v_oldTraces_5160_);
                        lean_dec_ref(v_tag_5157_);
                        lean_dec(v_cls_5155_);
                        lean_dec_ref(v_inst_5154_);
                        lean_dec_ref(v_always_5153_);
                        lean_dec(v_inst_5152_);
                        lean_dec_ref(v_inst_5151_);
                        v_toBind_5181_ = lean_ctor_get(v_inst_5149_, 1);
                        lean_inc(v_toBind_5181_);
                        lean_dec_ref(v_inst_5149_);
                        v_modifyTraceState_5182_ = lean_ctor_get(v_inst_5150_, 0);
                        lean_inc(v_modifyTraceState_5182_);
                        lean_dec_ref(v_inst_5150_);
                        v___x_5183_ = lean_apply_1(v_modifyTraceState_5182_, v___f_5169_);
                        v___x_5184_ = lean_apply_4(
                            v_toBind_5181_,
                            lean_box(0),
                            lean_box(0),
                            v___x_5183_,
                            v___f_5170_,
                        );
                        return v___x_5184_;
                    } else {
                        lean_dec_ref(v___f_5170_);
                        lean_dec_ref(v___f_5169_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_5170_);
                    lean_dec_ref(v___f_5169_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5187_ = lean_unbox_float(v_snd_5167_);
                v___x_5188_ = lean_unbox_float(v_fst_5166_);
                v___x_5189_ = lean_float_sub(v___x_5187_, v___x_5188_);
                v___x_5190_ = lean_float_decLt(v___y_5186_, v___x_5189_);
                v___y_5180_ = v___x_5190_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(
    mut v_inst_5206_: *mut LeanObject,
    mut v_inst_5207_: *mut LeanObject,
    mut v_inst_5208_: *mut LeanObject,
    mut v_inst_5209_: *mut LeanObject,
    mut v_always_5210_: *mut LeanObject,
    mut v_inst_5211_: *mut LeanObject,
    mut v_cls_5212_: *mut LeanObject,
    mut v_collapsed_5213_: *mut LeanObject,
    mut v_tag_5214_: *mut LeanObject,
    mut v_opts_5215_: *mut LeanObject,
    mut v_clsEnabled_5216_: *mut LeanObject,
    mut v_oldTraces_5217_: *mut LeanObject,
    mut v_msg_5218_: *mut LeanObject,
    mut v_resStartStop_5219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5220_: u8 = 0;
    let mut v_clsEnabled_boxed_5221_: u8 = 0;
    let mut v_res_5222_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5220_ = (lean_unbox(v_collapsed_5213_) as u8);
    v_clsEnabled_boxed_5221_ = (lean_unbox(v_clsEnabled_5216_) as u8);
    v_res_5222_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(
        v_inst_5206_,
        v_inst_5207_,
        v_inst_5208_,
        v_inst_5209_,
        v_always_5210_,
        v_inst_5211_,
        v_cls_5212_,
        v_collapsed_boxed_5220_,
        v_tag_5214_,
        v_opts_5215_,
        v_clsEnabled_boxed_5221_,
        v_oldTraces_5217_,
        v_msg_5218_,
        v_resStartStop_5219_,
    );
    lean_dec_ref(v_opts_5215_);
    return v_res_5222_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
    mut v_00_u03b1_5223_: *mut LeanObject,
    mut v_m_5224_: *mut LeanObject,
    mut v_inst_5225_: *mut LeanObject,
    mut v_inst_5226_: *mut LeanObject,
    mut v_inst_5227_: *mut LeanObject,
    mut v_inst_5228_: *mut LeanObject,
    mut v_00_u03b5_5229_: *mut LeanObject,
    mut v_always_5230_: *mut LeanObject,
    mut v_inst_5231_: *mut LeanObject,
    mut v_cls_5232_: *mut LeanObject,
    mut v_collapsed_5233_: u8,
    mut v_tag_5234_: *mut LeanObject,
    mut v_opts_5235_: *mut LeanObject,
    mut v_clsEnabled_5236_: u8,
    mut v_oldTraces_5237_: *mut LeanObject,
    mut v_msg_5238_: *mut LeanObject,
    mut v_resStartStop_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    v___x_5240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(
        v_inst_5225_,
        v_inst_5226_,
        v_inst_5227_,
        v_inst_5228_,
        v_always_5230_,
        v_inst_5231_,
        v_cls_5232_,
        v_collapsed_5233_,
        v_tag_5234_,
        v_opts_5235_,
        v_clsEnabled_5236_,
        v_oldTraces_5237_,
        v_msg_5238_,
        v_resStartStop_5239_,
    );
    return v___x_5240_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_5241_: *mut LeanObject = *_args.add(0);
    let mut v_m_5242_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5243_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5244_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5245_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5246_: *mut LeanObject = *_args.add(5);
    let mut v_00_u03b5_5247_: *mut LeanObject = *_args.add(6);
    let mut v_always_5248_: *mut LeanObject = *_args.add(7);
    let mut v_inst_5249_: *mut LeanObject = *_args.add(8);
    let mut v_cls_5250_: *mut LeanObject = *_args.add(9);
    let mut v_collapsed_5251_: *mut LeanObject = *_args.add(10);
    let mut v_tag_5252_: *mut LeanObject = *_args.add(11);
    let mut v_opts_5253_: *mut LeanObject = *_args.add(12);
    let mut v_clsEnabled_5254_: *mut LeanObject = *_args.add(13);
    let mut v_oldTraces_5255_: *mut LeanObject = *_args.add(14);
    let mut v_msg_5256_: *mut LeanObject = *_args.add(15);
    let mut v_resStartStop_5257_: *mut LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5258_: u8 = 0;
    let mut v_clsEnabled_boxed_5259_: u8 = 0;
    let mut v_res_5260_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5258_ = (lean_unbox(v_collapsed_5251_) as u8);
    v_clsEnabled_boxed_5259_ = (lean_unbox(v_clsEnabled_5254_) as u8);
    v_res_5260_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
        v_00_u03b1_5241_,
        v_m_5242_,
        v_inst_5243_,
        v_inst_5244_,
        v_inst_5245_,
        v_inst_5246_,
        v_00_u03b5_5247_,
        v_always_5248_,
        v_inst_5249_,
        v_cls_5250_,
        v_collapsed_boxed_5258_,
        v_tag_5252_,
        v_opts_5253_,
        v_clsEnabled_boxed_5259_,
        v_oldTraces_5255_,
        v_msg_5256_,
        v_resStartStop_5257_,
    );
    lean_dec_ref(v_opts_5253_);
    return v_res_5260_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__0(
    mut v_inst_5261_: *mut LeanObject,
    mut v_inst_5262_: *mut LeanObject,
    mut v_inst_5263_: *mut LeanObject,
    mut v_inst_5264_: *mut LeanObject,
    mut v_always_5265_: *mut LeanObject,
    mut v_inst_5266_: *mut LeanObject,
    mut v_cls_5267_: *mut LeanObject,
    mut v_collapsed_5268_: u8,
    mut v_tag_5269_: *mut LeanObject,
    mut v_opts_5270_: *mut LeanObject,
    mut v_clsEnabled_5271_: u8,
    mut v_oldTraces_5272_: *mut LeanObject,
    mut v_msg_5273_: *mut LeanObject,
    mut v_resStartStop_5274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    v___x_5275_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(
        v_inst_5261_,
        v_inst_5262_,
        v_inst_5263_,
        v_inst_5264_,
        v_always_5265_,
        v_inst_5266_,
        v_cls_5267_,
        v_collapsed_5268_,
        v_tag_5269_,
        v_opts_5270_,
        v_clsEnabled_5271_,
        v_oldTraces_5272_,
        v_msg_5273_,
        v_resStartStop_5274_,
    );
    return v___x_5275_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__0___boxed(
    mut v_inst_5276_: *mut LeanObject,
    mut v_inst_5277_: *mut LeanObject,
    mut v_inst_5278_: *mut LeanObject,
    mut v_inst_5279_: *mut LeanObject,
    mut v_always_5280_: *mut LeanObject,
    mut v_inst_5281_: *mut LeanObject,
    mut v_cls_5282_: *mut LeanObject,
    mut v_collapsed_5283_: *mut LeanObject,
    mut v_tag_5284_: *mut LeanObject,
    mut v_opts_5285_: *mut LeanObject,
    mut v_clsEnabled_5286_: *mut LeanObject,
    mut v_oldTraces_5287_: *mut LeanObject,
    mut v_msg_5288_: *mut LeanObject,
    mut v_resStartStop_5289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5290_: u8 = 0;
    let mut v_clsEnabled_boxed_5291_: u8 = 0;
    let mut v_res_5292_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5290_ = (lean_unbox(v_collapsed_5283_) as u8);
    v_clsEnabled_boxed_5291_ = (lean_unbox(v_clsEnabled_5286_) as u8);
    v_res_5292_ = l_Lean_withTraceNode___redArg___lam__0(
        v_inst_5276_,
        v_inst_5277_,
        v_inst_5278_,
        v_inst_5279_,
        v_always_5280_,
        v_inst_5281_,
        v_cls_5282_,
        v_collapsed_boxed_5290_,
        v_tag_5284_,
        v_opts_5285_,
        v_clsEnabled_boxed_5291_,
        v_oldTraces_5287_,
        v_msg_5288_,
        v_resStartStop_5289_,
    );
    lean_dec_ref(v_opts_5285_);
    return v_res_5292_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__1(
    mut v_toPure_5293_: *mut LeanObject,
    mut v_ex_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    v___x_5295_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5295_, 0, v_ex_5294_);
    v___x_5296_ = lean_apply_2(v_toPure_5293_, lean_box(0), v___x_5295_);
    return v___x_5296_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__2(
    mut v_toPure_5297_: *mut LeanObject,
    mut v_a_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    v___x_5299_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5299_, 0, v_a_5298_);
    v___x_5300_ = lean_apply_2(v_toPure_5297_, lean_box(0), v___x_5299_);
    return v___x_5300_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__3(
    mut v_start_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_toPure_5303_: *mut LeanObject,
    mut v_stop_5304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5305_: f64 = 0.0;
    let mut v___x_5306_: f64 = 0.0;
    let mut v___x_5307_: f64 = 0.0;
    let mut v___x_5308_: f64 = 0.0;
    let mut v___x_5309_: f64 = 0.0;
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    v___x_5305_ = lean_float_of_nat(v_start_5301_);
    v___x_5306_ = lean_float_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once
        ),
        _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0,
    );
    v___x_5307_ = lean_float_div(v___x_5305_, v___x_5306_);
    v___x_5308_ = lean_float_of_nat(v_stop_5304_);
    v___x_5309_ = lean_float_div(v___x_5308_, v___x_5306_);
    v___x_5310_ = lean_box_float(v___x_5307_);
    v___x_5311_ = lean_box_float(v___x_5309_);
    v___x_5312_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5312_, 0, v___x_5310_);
    lean_ctor_set(v___x_5312_, 1, v___x_5311_);
    v___x_5313_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5313_, 0, v_a_5302_);
    lean_ctor_set(v___x_5313_, 1, v___x_5312_);
    v___x_5314_ = lean_apply_2(v_toPure_5303_, lean_box(0), v___x_5313_);
    return v___x_5314_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__4(
    mut v_start_5315_: *mut LeanObject,
    mut v_toPure_5316_: *mut LeanObject,
    mut v_toBind_5317_: *mut LeanObject,
    mut v___x_5318_: *mut LeanObject,
    mut v_a_5319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    v___f_5320_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5320_, 0, v_start_5315_);
    lean_closure_set(v___f_5320_, 1, v_a_5319_);
    lean_closure_set(v___f_5320_, 2, v_toPure_5316_);
    v___x_5321_ = lean_apply_4(
        v_toBind_5317_,
        lean_box(0),
        lean_box(0),
        v___x_5318_,
        v___f_5320_,
    );
    return v___x_5321_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__5(
    mut v_toPure_5322_: *mut LeanObject,
    mut v_toBind_5323_: *mut LeanObject,
    mut v___x_5324_: *mut LeanObject,
    mut v___x_5325_: *mut LeanObject,
    mut v_start_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5323_);
    v___f_5327_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5327_, 0, v_start_5326_);
    lean_closure_set(v___f_5327_, 1, v_toPure_5322_);
    lean_closure_set(v___f_5327_, 2, v_toBind_5323_);
    lean_closure_set(v___f_5327_, 3, v___x_5324_);
    v___x_5328_ = lean_apply_4(
        v_toBind_5323_,
        lean_box(0),
        lean_box(0),
        v___x_5325_,
        v___f_5327_,
    );
    return v___x_5328_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__6(
    mut v_start_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
    mut v_toPure_5331_: *mut LeanObject,
    mut v_stop_5332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5333_: f64 = 0.0;
    let mut v___x_5334_: f64 = 0.0;
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    v___x_5333_ = lean_float_of_nat(v_start_5329_);
    v___x_5334_ = lean_float_of_nat(v_stop_5332_);
    v___x_5335_ = lean_box_float(v___x_5333_);
    v___x_5336_ = lean_box_float(v___x_5334_);
    v___x_5337_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5337_, 0, v___x_5335_);
    lean_ctor_set(v___x_5337_, 1, v___x_5336_);
    v___x_5338_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5338_, 0, v_a_5330_);
    lean_ctor_set(v___x_5338_, 1, v___x_5337_);
    v___x_5339_ = lean_apply_2(v_toPure_5331_, lean_box(0), v___x_5338_);
    return v___x_5339_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__7(
    mut v_start_5340_: *mut LeanObject,
    mut v_toPure_5341_: *mut LeanObject,
    mut v_toBind_5342_: *mut LeanObject,
    mut v___x_5343_: *mut LeanObject,
    mut v_a_5344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    v___f_5345_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5345_, 0, v_start_5340_);
    lean_closure_set(v___f_5345_, 1, v_a_5344_);
    lean_closure_set(v___f_5345_, 2, v_toPure_5341_);
    v___x_5346_ = lean_apply_4(
        v_toBind_5342_,
        lean_box(0),
        lean_box(0),
        v___x_5343_,
        v___f_5345_,
    );
    return v___x_5346_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__8(
    mut v_toPure_5347_: *mut LeanObject,
    mut v_toBind_5348_: *mut LeanObject,
    mut v___x_5349_: *mut LeanObject,
    mut v___x_5350_: *mut LeanObject,
    mut v_start_5351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5348_);
    v___f_5352_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5352_, 0, v_start_5351_);
    lean_closure_set(v___f_5352_, 1, v_toPure_5347_);
    lean_closure_set(v___f_5352_, 2, v_toBind_5348_);
    lean_closure_set(v___f_5352_, 3, v___x_5349_);
    v___x_5353_ = lean_apply_4(
        v_toBind_5348_,
        lean_box(0),
        lean_box(0),
        v___x_5350_,
        v___f_5352_,
    );
    return v___x_5353_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__9(
    mut v_always_5354_: *mut LeanObject,
    mut v_inst_5355_: *mut LeanObject,
    mut v_inst_5356_: *mut LeanObject,
    mut v_inst_5357_: *mut LeanObject,
    mut v_inst_5358_: *mut LeanObject,
    mut v_inst_5359_: *mut LeanObject,
    mut v_cls_5360_: *mut LeanObject,
    mut v_collapsed_5361_: u8,
    mut v_tag_5362_: *mut LeanObject,
    mut v_opts_5363_: *mut LeanObject,
    mut v_clsEnabled_5364_: u8,
    mut v_msg_5365_: *mut LeanObject,
    mut v_toPure_5366_: *mut LeanObject,
    mut v_toBind_5367_: *mut LeanObject,
    mut v_k_5368_: *mut LeanObject,
    mut v_inst_5369_: *mut LeanObject,
    mut v_oldTraces_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    v_tryCatch_5371_ = lean_ctor_get(v_always_5354_, 1);
    lean_inc(v_tryCatch_5371_);
    v___x_5372_ = lean_box((v_collapsed_5361_) as usize);
    v___x_5373_ = lean_box((v_clsEnabled_5364_) as usize);
    lean_inc_ref(v_opts_5363_);
    v___f_5374_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    lean_closure_set(v___f_5374_, 0, v_inst_5355_);
    lean_closure_set(v___f_5374_, 1, v_inst_5356_);
    lean_closure_set(v___f_5374_, 2, v_inst_5357_);
    lean_closure_set(v___f_5374_, 3, v_inst_5358_);
    lean_closure_set(v___f_5374_, 4, v_always_5354_);
    lean_closure_set(v___f_5374_, 5, v_inst_5359_);
    lean_closure_set(v___f_5374_, 6, v_cls_5360_);
    lean_closure_set(v___f_5374_, 7, v___x_5372_);
    lean_closure_set(v___f_5374_, 8, v_tag_5362_);
    lean_closure_set(v___f_5374_, 9, v_opts_5363_);
    lean_closure_set(v___f_5374_, 10, v___x_5373_);
    lean_closure_set(v___f_5374_, 11, v_oldTraces_5370_);
    lean_closure_set(v___f_5374_, 12, v_msg_5365_);
    lean_inc_n(v_toPure_5366_, 2);
    v___f_5375_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5375_, 0, v_toPure_5366_);
    v___f_5376_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5376_, 0, v_toPure_5366_);
    lean_inc(v_toBind_5367_);
    v___x_5377_ = lean_apply_4(
        v_toBind_5367_,
        lean_box(0),
        lean_box(0),
        v_k_5368_,
        v___f_5376_,
    );
    v___x_5378_ = lean_apply_3(v_tryCatch_5371_, lean_box(0), v___x_5377_, v___f_5375_);
    v___x_5379_ = l_Lean_KVMap_instValueBool;
    v___x_5380_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_5381_ = l_Lean_Option_get___redArg(v___x_5379_, v_opts_5363_, v___x_5380_);
    lean_dec_ref(v_opts_5363_);
    v___x_5382_ = (lean_unbox(v___x_5381_) as u8);
    lean_dec(v___x_5381_);
    if v___x_5382_ == 0 {
        let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
        v___x_5383_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_5384_ = lean_apply_2(v_inst_5369_, lean_box(0), v___x_5383_);
        lean_inc(v___x_5384_);
        lean_inc_n(v_toBind_5367_, 2);
        v___f_5385_ = lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__5 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5385_, 0, v_toPure_5366_);
        lean_closure_set(v___f_5385_, 1, v_toBind_5367_);
        lean_closure_set(v___f_5385_, 2, v___x_5384_);
        lean_closure_set(v___f_5385_, 3, v___x_5378_);
        v___x_5386_ = lean_apply_4(
            v_toBind_5367_,
            lean_box(0),
            lean_box(0),
            v___x_5384_,
            v___f_5385_,
        );
        v___x_5387_ = lean_apply_4(
            v_toBind_5367_,
            lean_box(0),
            lean_box(0),
            v___x_5386_,
            v___f_5374_,
        );
        return v___x_5387_;
    } else {
        let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
        v___x_5388_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_5389_ = lean_apply_2(v_inst_5369_, lean_box(0), v___x_5388_);
        lean_inc(v___x_5389_);
        lean_inc_n(v_toBind_5367_, 2);
        v___f_5390_ = lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__8 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5390_, 0, v_toPure_5366_);
        lean_closure_set(v___f_5390_, 1, v_toBind_5367_);
        lean_closure_set(v___f_5390_, 2, v___x_5389_);
        lean_closure_set(v___f_5390_, 3, v___x_5378_);
        v___x_5391_ = lean_apply_4(
            v_toBind_5367_,
            lean_box(0),
            lean_box(0),
            v___x_5389_,
            v___f_5390_,
        );
        v___x_5392_ = lean_apply_4(
            v_toBind_5367_,
            lean_box(0),
            lean_box(0),
            v___x_5391_,
            v___f_5374_,
        );
        return v___x_5392_;
    }
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__9___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_always_5393_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5394_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5395_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5396_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5397_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5398_: *mut LeanObject = *_args.add(5);
    let mut v_cls_5399_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_5400_: *mut LeanObject = *_args.add(7);
    let mut v_tag_5401_: *mut LeanObject = *_args.add(8);
    let mut v_opts_5402_: *mut LeanObject = *_args.add(9);
    let mut v_clsEnabled_5403_: *mut LeanObject = *_args.add(10);
    let mut v_msg_5404_: *mut LeanObject = *_args.add(11);
    let mut v_toPure_5405_: *mut LeanObject = *_args.add(12);
    let mut v_toBind_5406_: *mut LeanObject = *_args.add(13);
    let mut v_k_5407_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5408_: *mut LeanObject = *_args.add(15);
    let mut v_oldTraces_5409_: *mut LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5410_: u8 = 0;
    let mut v_clsEnabled_boxed_5411_: u8 = 0;
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5410_ = (lean_unbox(v_collapsed_5400_) as u8);
    v_clsEnabled_boxed_5411_ = (lean_unbox(v_clsEnabled_5403_) as u8);
    v_res_5412_ = l_Lean_withTraceNode___redArg___lam__9(
        v_always_5393_,
        v_inst_5394_,
        v_inst_5395_,
        v_inst_5396_,
        v_inst_5397_,
        v_inst_5398_,
        v_cls_5399_,
        v_collapsed_boxed_5410_,
        v_tag_5401_,
        v_opts_5402_,
        v_clsEnabled_boxed_5411_,
        v_msg_5404_,
        v_toPure_5405_,
        v_toBind_5406_,
        v_k_5407_,
        v_inst_5408_,
        v_oldTraces_5409_,
    );
    return v_res_5412_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__10(
    mut v_always_5413_: *mut LeanObject,
    mut v_inst_5414_: *mut LeanObject,
    mut v_inst_5415_: *mut LeanObject,
    mut v_inst_5416_: *mut LeanObject,
    mut v_inst_5417_: *mut LeanObject,
    mut v_inst_5418_: *mut LeanObject,
    mut v_cls_5419_: *mut LeanObject,
    mut v_collapsed_5420_: u8,
    mut v_tag_5421_: *mut LeanObject,
    mut v_opts_5422_: *mut LeanObject,
    mut v_msg_5423_: *mut LeanObject,
    mut v_toPure_5424_: *mut LeanObject,
    mut v_toBind_5425_: *mut LeanObject,
    mut v_k_5426_: *mut LeanObject,
    mut v_inst_5427_: *mut LeanObject,
    mut v_clsEnabled_5428_: u8,
) -> *mut LeanObject {
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5429_ = lean_box((v_collapsed_5420_) as usize);
                v___x_5430_ = lean_box((v_clsEnabled_5428_) as usize);
                lean_inc(v_k_5426_);
                lean_inc(v_toBind_5425_);
                lean_inc_ref(v_opts_5422_);
                lean_inc_ref(v_inst_5415_);
                lean_inc_ref(v_inst_5414_);
                v___f_5431_ = lean_alloc_closure(
                    l_Lean_withTraceNode___redArg___lam__9___boxed as *mut core::ffi::c_void,
                    17,
                    16,
                );
                lean_closure_set(v___f_5431_, 0, v_always_5413_);
                lean_closure_set(v___f_5431_, 1, v_inst_5414_);
                lean_closure_set(v___f_5431_, 2, v_inst_5415_);
                lean_closure_set(v___f_5431_, 3, v_inst_5416_);
                lean_closure_set(v___f_5431_, 4, v_inst_5417_);
                lean_closure_set(v___f_5431_, 5, v_inst_5418_);
                lean_closure_set(v___f_5431_, 6, v_cls_5419_);
                lean_closure_set(v___f_5431_, 7, v___x_5429_);
                lean_closure_set(v___f_5431_, 8, v_tag_5421_);
                lean_closure_set(v___f_5431_, 9, v_opts_5422_);
                lean_closure_set(v___f_5431_, 10, v___x_5430_);
                lean_closure_set(v___f_5431_, 11, v_msg_5423_);
                lean_closure_set(v___f_5431_, 12, v_toPure_5424_);
                lean_closure_set(v___f_5431_, 13, v_toBind_5425_);
                lean_closure_set(v___f_5431_, 14, v_k_5426_);
                lean_closure_set(v___f_5431_, 15, v_inst_5427_);
                if v_clsEnabled_5428_ == 0 {
                    v___x_5435_ = l_Lean_KVMap_instValueBool;
                    v___x_5436_ = l_Lean_trace_profiler;
                    v___x_5437_ =
                        l_Lean_Option_get___redArg(v___x_5435_, v_opts_5422_, v___x_5436_);
                    lean_dec_ref(v_opts_5422_);
                    v___x_5438_ = (lean_unbox(v___x_5437_) as u8);
                    lean_dec(v___x_5437_);
                    if v___x_5438_ == 0 {
                        lean_dec_ref(v___f_5431_);
                        lean_dec(v_toBind_5425_);
                        lean_dec_ref(v_inst_5415_);
                        lean_dec_ref(v_inst_5414_);
                        return v_k_5426_;
                    } else {
                        lean_dec(v_k_5426_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_5426_);
                    lean_dec_ref(v_opts_5422_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5433_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_5414_,
                    v_inst_5415_,
                );
                v___x_5434_ = lean_apply_4(
                    v_toBind_5425_,
                    lean_box(0),
                    lean_box(0),
                    v___x_5433_,
                    v___f_5431_,
                );
                return v___x_5434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__10___boxed(
    mut v_always_5439_: *mut LeanObject,
    mut v_inst_5440_: *mut LeanObject,
    mut v_inst_5441_: *mut LeanObject,
    mut v_inst_5442_: *mut LeanObject,
    mut v_inst_5443_: *mut LeanObject,
    mut v_inst_5444_: *mut LeanObject,
    mut v_cls_5445_: *mut LeanObject,
    mut v_collapsed_5446_: *mut LeanObject,
    mut v_tag_5447_: *mut LeanObject,
    mut v_opts_5448_: *mut LeanObject,
    mut v_msg_5449_: *mut LeanObject,
    mut v_toPure_5450_: *mut LeanObject,
    mut v_toBind_5451_: *mut LeanObject,
    mut v_k_5452_: *mut LeanObject,
    mut v_inst_5453_: *mut LeanObject,
    mut v_clsEnabled_5454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5455_: u8 = 0;
    let mut v_clsEnabled_boxed_5456_: u8 = 0;
    let mut v_res_5457_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5455_ = (lean_unbox(v_collapsed_5446_) as u8);
    v_clsEnabled_boxed_5456_ = (lean_unbox(v_clsEnabled_5454_) as u8);
    v_res_5457_ = l_Lean_withTraceNode___redArg___lam__10(
        v_always_5439_,
        v_inst_5440_,
        v_inst_5441_,
        v_inst_5442_,
        v_inst_5443_,
        v_inst_5444_,
        v_cls_5445_,
        v_collapsed_boxed_5455_,
        v_tag_5447_,
        v_opts_5448_,
        v_msg_5449_,
        v_toPure_5450_,
        v_toBind_5451_,
        v_k_5452_,
        v_inst_5453_,
        v_clsEnabled_boxed_5456_,
    );
    return v_res_5457_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__13(
    mut v_k_5458_: *mut LeanObject,
    mut v_inst_5459_: *mut LeanObject,
    mut v_toApplicative_5460_: *mut LeanObject,
    mut v_always_5461_: *mut LeanObject,
    mut v_inst_5462_: *mut LeanObject,
    mut v_inst_5463_: *mut LeanObject,
    mut v_inst_5464_: *mut LeanObject,
    mut v_inst_5465_: *mut LeanObject,
    mut v_cls_5466_: *mut LeanObject,
    mut v_collapsed_5467_: u8,
    mut v_tag_5468_: *mut LeanObject,
    mut v_msg_5469_: *mut LeanObject,
    mut v_toBind_5470_: *mut LeanObject,
    mut v_inst_5471_: *mut LeanObject,
    mut v_inst_5472_: *mut LeanObject,
    mut v_opts_5473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_5474_: u8 = 0;
    v_hasTrace_5474_ = lean_ctor_get_uint8(
        v_opts_5473_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5474_ == 0 {
        lean_dec_ref(v_opts_5473_);
        lean_dec(v_inst_5472_);
        lean_dec(v_inst_5471_);
        lean_dec(v_toBind_5470_);
        lean_dec(v_msg_5469_);
        lean_dec_ref(v_tag_5468_);
        lean_dec(v_cls_5466_);
        lean_dec_ref(v_inst_5465_);
        lean_dec(v_inst_5464_);
        lean_dec_ref(v_inst_5463_);
        lean_dec_ref(v_inst_5462_);
        lean_dec_ref(v_always_5461_);
        lean_dec_ref(v_toApplicative_5460_);
        lean_dec_ref(v_inst_5459_);
        return v_k_5458_;
    } else {
        let mut v_getInheritedTraceOptions_5475_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_5475_ = lean_ctor_get(v_inst_5459_, 2);
        lean_inc(v_getInheritedTraceOptions_5475_);
        v_toPure_5476_ = lean_ctor_get(v_toApplicative_5460_, 1);
        lean_inc_n(v_toPure_5476_, 2);
        lean_dec_ref(v_toApplicative_5460_);
        v___x_5477_ = lean_box((v_collapsed_5467_) as usize);
        lean_inc_n(v_toBind_5470_, 3);
        lean_inc(v_cls_5466_);
        v___f_5478_ = lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__10___boxed as *mut core::ffi::c_void,
            16,
            15,
        );
        lean_closure_set(v___f_5478_, 0, v_always_5461_);
        lean_closure_set(v___f_5478_, 1, v_inst_5462_);
        lean_closure_set(v___f_5478_, 2, v_inst_5459_);
        lean_closure_set(v___f_5478_, 3, v_inst_5463_);
        lean_closure_set(v___f_5478_, 4, v_inst_5464_);
        lean_closure_set(v___f_5478_, 5, v_inst_5465_);
        lean_closure_set(v___f_5478_, 6, v_cls_5466_);
        lean_closure_set(v___f_5478_, 7, v___x_5477_);
        lean_closure_set(v___f_5478_, 8, v_tag_5468_);
        lean_closure_set(v___f_5478_, 9, v_opts_5473_);
        lean_closure_set(v___f_5478_, 10, v_msg_5469_);
        lean_closure_set(v___f_5478_, 11, v_toPure_5476_);
        lean_closure_set(v___f_5478_, 12, v_toBind_5470_);
        lean_closure_set(v___f_5478_, 13, v_k_5458_);
        lean_closure_set(v___f_5478_, 14, v_inst_5471_);
        v___f_5479_ = lean_alloc_closure(
            l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5479_, 0, v_toPure_5476_);
        lean_closure_set(v___f_5479_, 1, v_cls_5466_);
        lean_closure_set(v___f_5479_, 2, v_toBind_5470_);
        lean_closure_set(v___f_5479_, 3, v_inst_5472_);
        v___x_5480_ = lean_apply_4(
            v_toBind_5470_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_5475_,
            v___f_5479_,
        );
        v___x_5481_ = lean_apply_4(
            v_toBind_5470_,
            lean_box(0),
            lean_box(0),
            v___x_5480_,
            v___f_5478_,
        );
        return v___x_5481_;
    }
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__13___boxed(
    mut v_k_5482_: *mut LeanObject,
    mut v_inst_5483_: *mut LeanObject,
    mut v_toApplicative_5484_: *mut LeanObject,
    mut v_always_5485_: *mut LeanObject,
    mut v_inst_5486_: *mut LeanObject,
    mut v_inst_5487_: *mut LeanObject,
    mut v_inst_5488_: *mut LeanObject,
    mut v_inst_5489_: *mut LeanObject,
    mut v_cls_5490_: *mut LeanObject,
    mut v_collapsed_5491_: *mut LeanObject,
    mut v_tag_5492_: *mut LeanObject,
    mut v_msg_5493_: *mut LeanObject,
    mut v_toBind_5494_: *mut LeanObject,
    mut v_inst_5495_: *mut LeanObject,
    mut v_inst_5496_: *mut LeanObject,
    mut v_opts_5497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5498_: u8 = 0;
    let mut v_res_5499_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5498_ = (lean_unbox(v_collapsed_5491_) as u8);
    v_res_5499_ = l_Lean_withTraceNode___redArg___lam__13(
        v_k_5482_,
        v_inst_5483_,
        v_toApplicative_5484_,
        v_always_5485_,
        v_inst_5486_,
        v_inst_5487_,
        v_inst_5488_,
        v_inst_5489_,
        v_cls_5490_,
        v_collapsed_boxed_5498_,
        v_tag_5492_,
        v_msg_5493_,
        v_toBind_5494_,
        v_inst_5495_,
        v_inst_5496_,
        v_opts_5497_,
    );
    return v_res_5499_;
}
pub unsafe fn l_Lean_withTraceNode___redArg(
    mut v_inst_5500_: *mut LeanObject,
    mut v_inst_5501_: *mut LeanObject,
    mut v_inst_5502_: *mut LeanObject,
    mut v_inst_5503_: *mut LeanObject,
    mut v_inst_5504_: *mut LeanObject,
    mut v_always_5505_: *mut LeanObject,
    mut v_inst_5506_: *mut LeanObject,
    mut v_inst_5507_: *mut LeanObject,
    mut v_cls_5508_: *mut LeanObject,
    mut v_msg_5509_: *mut LeanObject,
    mut v_k_5510_: *mut LeanObject,
    mut v_collapsed_5511_: u8,
    mut v_tag_5512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5513_ = lean_ctor_get(v_inst_5500_, 0);
    lean_inc_ref(v_toApplicative_5513_);
    v_toBind_5514_ = lean_ctor_get(v_inst_5500_, 1);
    lean_inc_n(v_toBind_5514_, 2);
    v___x_5515_ = lean_box((v_collapsed_5511_) as usize);
    lean_inc(v_inst_5504_);
    v___f_5516_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__13___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_5516_, 0, v_k_5510_);
    lean_closure_set(v___f_5516_, 1, v_inst_5501_);
    lean_closure_set(v___f_5516_, 2, v_toApplicative_5513_);
    lean_closure_set(v___f_5516_, 3, v_always_5505_);
    lean_closure_set(v___f_5516_, 4, v_inst_5500_);
    lean_closure_set(v___f_5516_, 5, v_inst_5502_);
    lean_closure_set(v___f_5516_, 6, v_inst_5503_);
    lean_closure_set(v___f_5516_, 7, v_inst_5507_);
    lean_closure_set(v___f_5516_, 8, v_cls_5508_);
    lean_closure_set(v___f_5516_, 9, v___x_5515_);
    lean_closure_set(v___f_5516_, 10, v_tag_5512_);
    lean_closure_set(v___f_5516_, 11, v_msg_5509_);
    lean_closure_set(v___f_5516_, 12, v_toBind_5514_);
    lean_closure_set(v___f_5516_, 13, v_inst_5506_);
    lean_closure_set(v___f_5516_, 14, v_inst_5504_);
    v___x_5517_ = lean_apply_4(
        v_toBind_5514_,
        lean_box(0),
        lean_box(0),
        v_inst_5504_,
        v___f_5516_,
    );
    return v___x_5517_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___boxed(
    mut v_inst_5518_: *mut LeanObject,
    mut v_inst_5519_: *mut LeanObject,
    mut v_inst_5520_: *mut LeanObject,
    mut v_inst_5521_: *mut LeanObject,
    mut v_inst_5522_: *mut LeanObject,
    mut v_always_5523_: *mut LeanObject,
    mut v_inst_5524_: *mut LeanObject,
    mut v_inst_5525_: *mut LeanObject,
    mut v_cls_5526_: *mut LeanObject,
    mut v_msg_5527_: *mut LeanObject,
    mut v_k_5528_: *mut LeanObject,
    mut v_collapsed_5529_: *mut LeanObject,
    mut v_tag_5530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5531_: u8 = 0;
    let mut v_res_5532_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5531_ = (lean_unbox(v_collapsed_5529_) as u8);
    v_res_5532_ = l_Lean_withTraceNode___redArg(
        v_inst_5518_,
        v_inst_5519_,
        v_inst_5520_,
        v_inst_5521_,
        v_inst_5522_,
        v_always_5523_,
        v_inst_5524_,
        v_inst_5525_,
        v_cls_5526_,
        v_msg_5527_,
        v_k_5528_,
        v_collapsed_boxed_5531_,
        v_tag_5530_,
    );
    return v_res_5532_;
}
pub unsafe fn l_Lean_withTraceNode(
    mut v_00_u03b1_5533_: *mut LeanObject,
    mut v_m_5534_: *mut LeanObject,
    mut v_inst_5535_: *mut LeanObject,
    mut v_inst_5536_: *mut LeanObject,
    mut v_inst_5537_: *mut LeanObject,
    mut v_inst_5538_: *mut LeanObject,
    mut v_inst_5539_: *mut LeanObject,
    mut v_00_u03b5_5540_: *mut LeanObject,
    mut v_always_5541_: *mut LeanObject,
    mut v_inst_5542_: *mut LeanObject,
    mut v_inst_5543_: *mut LeanObject,
    mut v_cls_5544_: *mut LeanObject,
    mut v_msg_5545_: *mut LeanObject,
    mut v_k_5546_: *mut LeanObject,
    mut v_collapsed_5547_: u8,
    mut v_tag_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5549_ = lean_ctor_get(v_inst_5535_, 0);
    lean_inc_ref(v_toApplicative_5549_);
    v_toBind_5550_ = lean_ctor_get(v_inst_5535_, 1);
    lean_inc_n(v_toBind_5550_, 2);
    v___x_5551_ = lean_box((v_collapsed_5547_) as usize);
    lean_inc(v_inst_5539_);
    v___f_5552_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__13___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_5552_, 0, v_k_5546_);
    lean_closure_set(v___f_5552_, 1, v_inst_5536_);
    lean_closure_set(v___f_5552_, 2, v_toApplicative_5549_);
    lean_closure_set(v___f_5552_, 3, v_always_5541_);
    lean_closure_set(v___f_5552_, 4, v_inst_5535_);
    lean_closure_set(v___f_5552_, 5, v_inst_5537_);
    lean_closure_set(v___f_5552_, 6, v_inst_5538_);
    lean_closure_set(v___f_5552_, 7, v_inst_5543_);
    lean_closure_set(v___f_5552_, 8, v_cls_5544_);
    lean_closure_set(v___f_5552_, 9, v___x_5551_);
    lean_closure_set(v___f_5552_, 10, v_tag_5548_);
    lean_closure_set(v___f_5552_, 11, v_msg_5545_);
    lean_closure_set(v___f_5552_, 12, v_toBind_5550_);
    lean_closure_set(v___f_5552_, 13, v_inst_5542_);
    lean_closure_set(v___f_5552_, 14, v_inst_5539_);
    v___x_5553_ = lean_apply_4(
        v_toBind_5550_,
        lean_box(0),
        lean_box(0),
        v_inst_5539_,
        v___f_5552_,
    );
    return v___x_5553_;
}
pub unsafe fn l_Lean_withTraceNode___boxed(
    mut v_00_u03b1_5554_: *mut LeanObject,
    mut v_m_5555_: *mut LeanObject,
    mut v_inst_5556_: *mut LeanObject,
    mut v_inst_5557_: *mut LeanObject,
    mut v_inst_5558_: *mut LeanObject,
    mut v_inst_5559_: *mut LeanObject,
    mut v_inst_5560_: *mut LeanObject,
    mut v_00_u03b5_5561_: *mut LeanObject,
    mut v_always_5562_: *mut LeanObject,
    mut v_inst_5563_: *mut LeanObject,
    mut v_inst_5564_: *mut LeanObject,
    mut v_cls_5565_: *mut LeanObject,
    mut v_msg_5566_: *mut LeanObject,
    mut v_k_5567_: *mut LeanObject,
    mut v_collapsed_5568_: *mut LeanObject,
    mut v_tag_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5570_: u8 = 0;
    let mut v_res_5571_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5570_ = (lean_unbox(v_collapsed_5568_) as u8);
    v_res_5571_ = l_Lean_withTraceNode(
        v_00_u03b1_5554_,
        v_m_5555_,
        v_inst_5556_,
        v_inst_5557_,
        v_inst_5558_,
        v_inst_5559_,
        v_inst_5560_,
        v_00_u03b5_5561_,
        v_always_5562_,
        v_inst_5563_,
        v_inst_5564_,
        v_cls_5565_,
        v_msg_5566_,
        v_k_5567_,
        v_collapsed_boxed_5570_,
        v_tag_5569_,
    );
    return v_res_5571_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__0(
    mut v_self_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5573_: *mut LeanObject = core::ptr::null_mut();
    v_fst_5573_ = lean_ctor_get(v_self_5572_, 0);
    lean_inc(v_fst_5573_);
    return v_fst_5573_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__0___boxed(
    mut v_self_5574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5575_: *mut LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_5574_);
    lean_dec_ref(v_self_5574_);
    return v_res_5575_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__1(
    mut v_toPure_5576_: *mut LeanObject,
    mut v_x_5577_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5577_) == 0 {
        let mut v_a_5578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
        v_a_5578_ = lean_ctor_get(v_x_5577_, 0);
        lean_inc(v_a_5578_);
        lean_dec_ref_known(v_x_5577_, 1);
        v___x_5579_ = l_Lean_Exception_toMessageData(v_a_5578_);
        v___x_5580_ = lean_apply_2(v_toPure_5576_, lean_box(0), v___x_5579_);
        return v___x_5580_;
    } else {
        let mut v_a_5581_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_5582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
        v_a_5581_ = lean_ctor_get(v_x_5577_, 0);
        lean_inc(v_a_5581_);
        lean_dec_ref_known(v_x_5577_, 1);
        v_snd_5582_ = lean_ctor_get(v_a_5581_, 1);
        lean_inc(v_snd_5582_);
        lean_dec(v_a_5581_);
        v___x_5583_ = lean_apply_2(v_toPure_5576_, lean_box(0), v_snd_5582_);
        return v___x_5583_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__4(
    mut v_toPure_5584_: *mut LeanObject,
    mut v_ex_5585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    v___x_5586_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5586_, 0, v_ex_5585_);
    v___x_5587_ = lean_apply_2(v_toPure_5584_, lean_box(0), v___x_5586_);
    return v___x_5587_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__2(
    mut v_toPure_5588_: *mut LeanObject,
    mut v_a_5589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    v___x_5590_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5590_, 0, v_a_5589_);
    v___x_5591_ = lean_apply_2(v_toPure_5588_, lean_box(0), v___x_5590_);
    return v___x_5591_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__3(
    mut v_inst_5592_: *mut LeanObject,
    mut v_inst_5593_: *mut LeanObject,
    mut v_inst_5594_: *mut LeanObject,
    mut v_inst_5595_: *mut LeanObject,
    mut v_inst_5596_: *mut LeanObject,
    mut v___f_5597_: *mut LeanObject,
    mut v_cls_5598_: *mut LeanObject,
    mut v_collapsed_5599_: u8,
    mut v_tag_5600_: *mut LeanObject,
    mut v_opts_5601_: *mut LeanObject,
    mut v_clsEnabled_5602_: u8,
    mut v_oldTraces_5603_: *mut LeanObject,
    mut v_msg_5604_: *mut LeanObject,
    mut v_resStartStop_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    v___x_5606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(
        v_inst_5592_,
        v_inst_5593_,
        v_inst_5594_,
        v_inst_5595_,
        v_inst_5596_,
        v___f_5597_,
        v_cls_5598_,
        v_collapsed_5599_,
        v_tag_5600_,
        v_opts_5601_,
        v_clsEnabled_5602_,
        v_oldTraces_5603_,
        v_msg_5604_,
        v_resStartStop_5605_,
    );
    return v___x_5606_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__3___boxed(
    mut v_inst_5607_: *mut LeanObject,
    mut v_inst_5608_: *mut LeanObject,
    mut v_inst_5609_: *mut LeanObject,
    mut v_inst_5610_: *mut LeanObject,
    mut v_inst_5611_: *mut LeanObject,
    mut v___f_5612_: *mut LeanObject,
    mut v_cls_5613_: *mut LeanObject,
    mut v_collapsed_5614_: *mut LeanObject,
    mut v_tag_5615_: *mut LeanObject,
    mut v_opts_5616_: *mut LeanObject,
    mut v_clsEnabled_5617_: *mut LeanObject,
    mut v_oldTraces_5618_: *mut LeanObject,
    mut v_msg_5619_: *mut LeanObject,
    mut v_resStartStop_5620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5621_: u8 = 0;
    let mut v_clsEnabled_boxed_5622_: u8 = 0;
    let mut v_res_5623_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5621_ = (lean_unbox(v_collapsed_5614_) as u8);
    v_clsEnabled_boxed_5622_ = (lean_unbox(v_clsEnabled_5617_) as u8);
    v_res_5623_ = l_Lean_withTraceNode_x27___redArg___lam__3(
        v_inst_5607_,
        v_inst_5608_,
        v_inst_5609_,
        v_inst_5610_,
        v_inst_5611_,
        v___f_5612_,
        v_cls_5613_,
        v_collapsed_boxed_5621_,
        v_tag_5615_,
        v_opts_5616_,
        v_clsEnabled_boxed_5622_,
        v_oldTraces_5618_,
        v_msg_5619_,
        v_resStartStop_5620_,
    );
    lean_dec_ref(v_opts_5616_);
    return v_res_5623_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__5(
    mut v_start_5624_: *mut LeanObject,
    mut v_a_5625_: *mut LeanObject,
    mut v_toPure_5626_: *mut LeanObject,
    mut v_stop_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5628_: f64 = 0.0;
    let mut v___x_5629_: f64 = 0.0;
    let mut v___x_5630_: f64 = 0.0;
    let mut v___x_5631_: f64 = 0.0;
    let mut v___x_5632_: f64 = 0.0;
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    v___x_5628_ = lean_float_of_nat(v_start_5624_);
    v___x_5629_ = lean_float_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once
        ),
        _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0,
    );
    v___x_5630_ = lean_float_div(v___x_5628_, v___x_5629_);
    v___x_5631_ = lean_float_of_nat(v_stop_5627_);
    v___x_5632_ = lean_float_div(v___x_5631_, v___x_5629_);
    v___x_5633_ = lean_box_float(v___x_5630_);
    v___x_5634_ = lean_box_float(v___x_5632_);
    v___x_5635_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5635_, 0, v___x_5633_);
    lean_ctor_set(v___x_5635_, 1, v___x_5634_);
    v___x_5636_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5636_, 0, v_a_5625_);
    lean_ctor_set(v___x_5636_, 1, v___x_5635_);
    v___x_5637_ = lean_apply_2(v_toPure_5626_, lean_box(0), v___x_5636_);
    return v___x_5637_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__6(
    mut v_start_5638_: *mut LeanObject,
    mut v_toPure_5639_: *mut LeanObject,
    mut v_toBind_5640_: *mut LeanObject,
    mut v___x_5641_: *mut LeanObject,
    mut v_a_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    v___f_5643_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5643_, 0, v_start_5638_);
    lean_closure_set(v___f_5643_, 1, v_a_5642_);
    lean_closure_set(v___f_5643_, 2, v_toPure_5639_);
    v___x_5644_ = lean_apply_4(
        v_toBind_5640_,
        lean_box(0),
        lean_box(0),
        v___x_5641_,
        v___f_5643_,
    );
    return v___x_5644_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__7(
    mut v_toPure_5645_: *mut LeanObject,
    mut v_toBind_5646_: *mut LeanObject,
    mut v___x_5647_: *mut LeanObject,
    mut v___x_5648_: *mut LeanObject,
    mut v_start_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5646_);
    v___f_5650_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5650_, 0, v_start_5649_);
    lean_closure_set(v___f_5650_, 1, v_toPure_5645_);
    lean_closure_set(v___f_5650_, 2, v_toBind_5646_);
    lean_closure_set(v___f_5650_, 3, v___x_5647_);
    v___x_5651_ = lean_apply_4(
        v_toBind_5646_,
        lean_box(0),
        lean_box(0),
        v___x_5648_,
        v___f_5650_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__8(
    mut v_start_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_toPure_5654_: *mut LeanObject,
    mut v_stop_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5656_: f64 = 0.0;
    let mut v___x_5657_: f64 = 0.0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    v___x_5656_ = lean_float_of_nat(v_start_5652_);
    v___x_5657_ = lean_float_of_nat(v_stop_5655_);
    v___x_5658_ = lean_box_float(v___x_5656_);
    v___x_5659_ = lean_box_float(v___x_5657_);
    v___x_5660_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5660_, 0, v___x_5658_);
    lean_ctor_set(v___x_5660_, 1, v___x_5659_);
    v___x_5661_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5661_, 0, v_a_5653_);
    lean_ctor_set(v___x_5661_, 1, v___x_5660_);
    v___x_5662_ = lean_apply_2(v_toPure_5654_, lean_box(0), v___x_5661_);
    return v___x_5662_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__9(
    mut v_start_5663_: *mut LeanObject,
    mut v_toPure_5664_: *mut LeanObject,
    mut v_toBind_5665_: *mut LeanObject,
    mut v___x_5666_: *mut LeanObject,
    mut v_a_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    v___f_5668_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5668_, 0, v_start_5663_);
    lean_closure_set(v___f_5668_, 1, v_a_5667_);
    lean_closure_set(v___f_5668_, 2, v_toPure_5664_);
    v___x_5669_ = lean_apply_4(
        v_toBind_5665_,
        lean_box(0),
        lean_box(0),
        v___x_5666_,
        v___f_5668_,
    );
    return v___x_5669_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__10(
    mut v_toPure_5670_: *mut LeanObject,
    mut v_toBind_5671_: *mut LeanObject,
    mut v___x_5672_: *mut LeanObject,
    mut v___x_5673_: *mut LeanObject,
    mut v_start_5674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5671_);
    v___f_5675_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5675_, 0, v_start_5674_);
    lean_closure_set(v___f_5675_, 1, v_toPure_5670_);
    lean_closure_set(v___f_5675_, 2, v_toBind_5671_);
    lean_closure_set(v___f_5675_, 3, v___x_5672_);
    v___x_5676_ = lean_apply_4(
        v_toBind_5671_,
        lean_box(0),
        lean_box(0),
        v___x_5673_,
        v___f_5675_,
    );
    return v___x_5676_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__11(
    mut v_inst_5677_: *mut LeanObject,
    mut v_inst_5678_: *mut LeanObject,
    mut v_inst_5679_: *mut LeanObject,
    mut v_inst_5680_: *mut LeanObject,
    mut v_inst_5681_: *mut LeanObject,
    mut v___f_5682_: *mut LeanObject,
    mut v_cls_5683_: *mut LeanObject,
    mut v_collapsed_5684_: u8,
    mut v_tag_5685_: *mut LeanObject,
    mut v_opts_5686_: *mut LeanObject,
    mut v_clsEnabled_5687_: u8,
    mut v_msg_5688_: *mut LeanObject,
    mut v_toBind_5689_: *mut LeanObject,
    mut v_k_5690_: *mut LeanObject,
    mut v___f_5691_: *mut LeanObject,
    mut v___f_5692_: *mut LeanObject,
    mut v_inst_5693_: *mut LeanObject,
    mut v_toPure_5694_: *mut LeanObject,
    mut v_oldTraces_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u8 = 0;
    v_tryCatch_5696_ = lean_ctor_get(v_inst_5677_, 1);
    lean_inc(v_tryCatch_5696_);
    v___x_5697_ = lean_box((v_collapsed_5684_) as usize);
    v___x_5698_ = lean_box((v_clsEnabled_5687_) as usize);
    lean_inc_ref(v_opts_5686_);
    v___f_5699_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    lean_closure_set(v___f_5699_, 0, v_inst_5678_);
    lean_closure_set(v___f_5699_, 1, v_inst_5679_);
    lean_closure_set(v___f_5699_, 2, v_inst_5680_);
    lean_closure_set(v___f_5699_, 3, v_inst_5681_);
    lean_closure_set(v___f_5699_, 4, v_inst_5677_);
    lean_closure_set(v___f_5699_, 5, v___f_5682_);
    lean_closure_set(v___f_5699_, 6, v_cls_5683_);
    lean_closure_set(v___f_5699_, 7, v___x_5697_);
    lean_closure_set(v___f_5699_, 8, v_tag_5685_);
    lean_closure_set(v___f_5699_, 9, v_opts_5686_);
    lean_closure_set(v___f_5699_, 10, v___x_5698_);
    lean_closure_set(v___f_5699_, 11, v_oldTraces_5695_);
    lean_closure_set(v___f_5699_, 12, v_msg_5688_);
    lean_inc(v_toBind_5689_);
    v___x_5700_ = lean_apply_4(
        v_toBind_5689_,
        lean_box(0),
        lean_box(0),
        v_k_5690_,
        v___f_5691_,
    );
    v___x_5701_ = lean_apply_3(v_tryCatch_5696_, lean_box(0), v___x_5700_, v___f_5692_);
    v___x_5702_ = l_Lean_KVMap_instValueBool;
    v___x_5703_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_5704_ = l_Lean_Option_get___redArg(v___x_5702_, v_opts_5686_, v___x_5703_);
    lean_dec_ref(v_opts_5686_);
    v___x_5705_ = (lean_unbox(v___x_5704_) as u8);
    lean_dec(v___x_5704_);
    if v___x_5705_ == 0 {
        let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
        v___x_5706_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_5707_ = lean_apply_2(v_inst_5693_, lean_box(0), v___x_5706_);
        lean_inc(v___x_5707_);
        lean_inc_n(v_toBind_5689_, 2);
        v___f_5708_ = lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__7 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5708_, 0, v_toPure_5694_);
        lean_closure_set(v___f_5708_, 1, v_toBind_5689_);
        lean_closure_set(v___f_5708_, 2, v___x_5707_);
        lean_closure_set(v___f_5708_, 3, v___x_5701_);
        v___x_5709_ = lean_apply_4(
            v_toBind_5689_,
            lean_box(0),
            lean_box(0),
            v___x_5707_,
            v___f_5708_,
        );
        v___x_5710_ = lean_apply_4(
            v_toBind_5689_,
            lean_box(0),
            lean_box(0),
            v___x_5709_,
            v___f_5699_,
        );
        return v___x_5710_;
    } else {
        let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
        v___x_5711_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_5712_ = lean_apply_2(v_inst_5693_, lean_box(0), v___x_5711_);
        lean_inc(v___x_5712_);
        lean_inc_n(v_toBind_5689_, 2);
        v___f_5713_ = lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__10 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5713_, 0, v_toPure_5694_);
        lean_closure_set(v___f_5713_, 1, v_toBind_5689_);
        lean_closure_set(v___f_5713_, 2, v___x_5712_);
        lean_closure_set(v___f_5713_, 3, v___x_5701_);
        v___x_5714_ = lean_apply_4(
            v_toBind_5689_,
            lean_box(0),
            lean_box(0),
            v___x_5712_,
            v___f_5713_,
        );
        v___x_5715_ = lean_apply_4(
            v_toBind_5689_,
            lean_box(0),
            lean_box(0),
            v___x_5714_,
            v___f_5699_,
        );
        return v___x_5715_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__11___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5716_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5717_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5718_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5719_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5720_: *mut LeanObject = *_args.add(4);
    let mut v___f_5721_: *mut LeanObject = *_args.add(5);
    let mut v_cls_5722_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_5723_: *mut LeanObject = *_args.add(7);
    let mut v_tag_5724_: *mut LeanObject = *_args.add(8);
    let mut v_opts_5725_: *mut LeanObject = *_args.add(9);
    let mut v_clsEnabled_5726_: *mut LeanObject = *_args.add(10);
    let mut v_msg_5727_: *mut LeanObject = *_args.add(11);
    let mut v_toBind_5728_: *mut LeanObject = *_args.add(12);
    let mut v_k_5729_: *mut LeanObject = *_args.add(13);
    let mut v___f_5730_: *mut LeanObject = *_args.add(14);
    let mut v___f_5731_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5732_: *mut LeanObject = *_args.add(16);
    let mut v_toPure_5733_: *mut LeanObject = *_args.add(17);
    let mut v_oldTraces_5734_: *mut LeanObject = *_args.add(18);
    let mut v_collapsed_boxed_5735_: u8 = 0;
    let mut v_clsEnabled_boxed_5736_: u8 = 0;
    let mut v_res_5737_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5735_ = (lean_unbox(v_collapsed_5723_) as u8);
    v_clsEnabled_boxed_5736_ = (lean_unbox(v_clsEnabled_5726_) as u8);
    v_res_5737_ = l_Lean_withTraceNode_x27___redArg___lam__11(
        v_inst_5716_,
        v_inst_5717_,
        v_inst_5718_,
        v_inst_5719_,
        v_inst_5720_,
        v___f_5721_,
        v_cls_5722_,
        v_collapsed_boxed_5735_,
        v_tag_5724_,
        v_opts_5725_,
        v_clsEnabled_boxed_5736_,
        v_msg_5727_,
        v_toBind_5728_,
        v_k_5729_,
        v___f_5730_,
        v___f_5731_,
        v_inst_5732_,
        v_toPure_5733_,
        v_oldTraces_5734_,
    );
    return v_res_5737_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__12(
    mut v_inst_5738_: *mut LeanObject,
    mut v_inst_5739_: *mut LeanObject,
    mut v_inst_5740_: *mut LeanObject,
    mut v_inst_5741_: *mut LeanObject,
    mut v_inst_5742_: *mut LeanObject,
    mut v___f_5743_: *mut LeanObject,
    mut v_cls_5744_: *mut LeanObject,
    mut v_collapsed_5745_: u8,
    mut v_tag_5746_: *mut LeanObject,
    mut v_opts_5747_: *mut LeanObject,
    mut v_msg_5748_: *mut LeanObject,
    mut v_toBind_5749_: *mut LeanObject,
    mut v_k_5750_: *mut LeanObject,
    mut v___f_5751_: *mut LeanObject,
    mut v___f_5752_: *mut LeanObject,
    mut v_inst_5753_: *mut LeanObject,
    mut v_toPure_5754_: *mut LeanObject,
    mut v_clsEnabled_5755_: u8,
) -> *mut LeanObject {
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5756_ = lean_box((v_collapsed_5745_) as usize);
                v___x_5757_ = lean_box((v_clsEnabled_5755_) as usize);
                lean_inc(v_k_5750_);
                lean_inc(v_toBind_5749_);
                lean_inc_ref(v_opts_5747_);
                lean_inc_ref(v_inst_5740_);
                lean_inc_ref(v_inst_5739_);
                v___f_5758_ = lean_alloc_closure(
                    l_Lean_withTraceNode_x27___redArg___lam__11___boxed as *mut core::ffi::c_void,
                    19,
                    18,
                );
                lean_closure_set(v___f_5758_, 0, v_inst_5738_);
                lean_closure_set(v___f_5758_, 1, v_inst_5739_);
                lean_closure_set(v___f_5758_, 2, v_inst_5740_);
                lean_closure_set(v___f_5758_, 3, v_inst_5741_);
                lean_closure_set(v___f_5758_, 4, v_inst_5742_);
                lean_closure_set(v___f_5758_, 5, v___f_5743_);
                lean_closure_set(v___f_5758_, 6, v_cls_5744_);
                lean_closure_set(v___f_5758_, 7, v___x_5756_);
                lean_closure_set(v___f_5758_, 8, v_tag_5746_);
                lean_closure_set(v___f_5758_, 9, v_opts_5747_);
                lean_closure_set(v___f_5758_, 10, v___x_5757_);
                lean_closure_set(v___f_5758_, 11, v_msg_5748_);
                lean_closure_set(v___f_5758_, 12, v_toBind_5749_);
                lean_closure_set(v___f_5758_, 13, v_k_5750_);
                lean_closure_set(v___f_5758_, 14, v___f_5751_);
                lean_closure_set(v___f_5758_, 15, v___f_5752_);
                lean_closure_set(v___f_5758_, 16, v_inst_5753_);
                lean_closure_set(v___f_5758_, 17, v_toPure_5754_);
                if v_clsEnabled_5755_ == 0 {
                    v___x_5762_ = l_Lean_KVMap_instValueBool;
                    v___x_5763_ = l_Lean_trace_profiler;
                    v___x_5764_ =
                        l_Lean_Option_get___redArg(v___x_5762_, v_opts_5747_, v___x_5763_);
                    lean_dec_ref(v_opts_5747_);
                    v___x_5765_ = (lean_unbox(v___x_5764_) as u8);
                    lean_dec(v___x_5764_);
                    if v___x_5765_ == 0 {
                        lean_dec_ref(v___f_5758_);
                        lean_dec(v_toBind_5749_);
                        lean_dec_ref(v_inst_5740_);
                        lean_dec_ref(v_inst_5739_);
                        return v_k_5750_;
                    } else {
                        lean_dec(v_k_5750_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_5750_);
                    lean_dec_ref(v_opts_5747_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5760_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_5739_,
                    v_inst_5740_,
                );
                v___x_5761_ = lean_apply_4(
                    v_toBind_5749_,
                    lean_box(0),
                    lean_box(0),
                    v___x_5760_,
                    v___f_5758_,
                );
                return v___x_5761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__12___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5766_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5767_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5768_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5769_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5770_: *mut LeanObject = *_args.add(4);
    let mut v___f_5771_: *mut LeanObject = *_args.add(5);
    let mut v_cls_5772_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_5773_: *mut LeanObject = *_args.add(7);
    let mut v_tag_5774_: *mut LeanObject = *_args.add(8);
    let mut v_opts_5775_: *mut LeanObject = *_args.add(9);
    let mut v_msg_5776_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_5777_: *mut LeanObject = *_args.add(11);
    let mut v_k_5778_: *mut LeanObject = *_args.add(12);
    let mut v___f_5779_: *mut LeanObject = *_args.add(13);
    let mut v___f_5780_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5781_: *mut LeanObject = *_args.add(15);
    let mut v_toPure_5782_: *mut LeanObject = *_args.add(16);
    let mut v_clsEnabled_5783_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5784_: u8 = 0;
    let mut v_clsEnabled_boxed_5785_: u8 = 0;
    let mut v_res_5786_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5784_ = (lean_unbox(v_collapsed_5773_) as u8);
    v_clsEnabled_boxed_5785_ = (lean_unbox(v_clsEnabled_5783_) as u8);
    v_res_5786_ = l_Lean_withTraceNode_x27___redArg___lam__12(
        v_inst_5766_,
        v_inst_5767_,
        v_inst_5768_,
        v_inst_5769_,
        v_inst_5770_,
        v___f_5771_,
        v_cls_5772_,
        v_collapsed_boxed_5784_,
        v_tag_5774_,
        v_opts_5775_,
        v_msg_5776_,
        v_toBind_5777_,
        v_k_5778_,
        v___f_5779_,
        v___f_5780_,
        v_inst_5781_,
        v_toPure_5782_,
        v_clsEnabled_boxed_5785_,
    );
    return v_res_5786_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__13(
    mut v_k_5787_: *mut LeanObject,
    mut v_inst_5788_: *mut LeanObject,
    mut v_inst_5789_: *mut LeanObject,
    mut v_inst_5790_: *mut LeanObject,
    mut v_inst_5791_: *mut LeanObject,
    mut v_inst_5792_: *mut LeanObject,
    mut v___f_5793_: *mut LeanObject,
    mut v_cls_5794_: *mut LeanObject,
    mut v_collapsed_5795_: u8,
    mut v_tag_5796_: *mut LeanObject,
    mut v_msg_5797_: *mut LeanObject,
    mut v_toBind_5798_: *mut LeanObject,
    mut v___f_5799_: *mut LeanObject,
    mut v___f_5800_: *mut LeanObject,
    mut v_inst_5801_: *mut LeanObject,
    mut v_toPure_5802_: *mut LeanObject,
    mut v___f_5803_: *mut LeanObject,
    mut v_opts_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_5805_: u8 = 0;
    v_hasTrace_5805_ = lean_ctor_get_uint8(
        v_opts_5804_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5805_ == 0 {
        lean_dec_ref(v_opts_5804_);
        lean_dec(v___f_5803_);
        lean_dec(v_toPure_5802_);
        lean_dec(v_inst_5801_);
        lean_dec(v___f_5800_);
        lean_dec(v___f_5799_);
        lean_dec(v_toBind_5798_);
        lean_dec(v_msg_5797_);
        lean_dec_ref(v_tag_5796_);
        lean_dec(v_cls_5794_);
        lean_dec_ref(v___f_5793_);
        lean_dec(v_inst_5792_);
        lean_dec_ref(v_inst_5791_);
        lean_dec_ref(v_inst_5790_);
        lean_dec_ref(v_inst_5789_);
        lean_dec_ref(v_inst_5788_);
        return v_k_5787_;
    } else {
        let mut v_getInheritedTraceOptions_5806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_5806_ = lean_ctor_get(v_inst_5788_, 2);
        lean_inc(v_getInheritedTraceOptions_5806_);
        v___x_5807_ = lean_box((v_collapsed_5795_) as usize);
        lean_inc_n(v_toBind_5798_, 2);
        v___f_5808_ = lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__12___boxed as *mut core::ffi::c_void,
            18,
            17,
        );
        lean_closure_set(v___f_5808_, 0, v_inst_5789_);
        lean_closure_set(v___f_5808_, 1, v_inst_5790_);
        lean_closure_set(v___f_5808_, 2, v_inst_5788_);
        lean_closure_set(v___f_5808_, 3, v_inst_5791_);
        lean_closure_set(v___f_5808_, 4, v_inst_5792_);
        lean_closure_set(v___f_5808_, 5, v___f_5793_);
        lean_closure_set(v___f_5808_, 6, v_cls_5794_);
        lean_closure_set(v___f_5808_, 7, v___x_5807_);
        lean_closure_set(v___f_5808_, 8, v_tag_5796_);
        lean_closure_set(v___f_5808_, 9, v_opts_5804_);
        lean_closure_set(v___f_5808_, 10, v_msg_5797_);
        lean_closure_set(v___f_5808_, 11, v_toBind_5798_);
        lean_closure_set(v___f_5808_, 12, v_k_5787_);
        lean_closure_set(v___f_5808_, 13, v___f_5799_);
        lean_closure_set(v___f_5808_, 14, v___f_5800_);
        lean_closure_set(v___f_5808_, 15, v_inst_5801_);
        lean_closure_set(v___f_5808_, 16, v_toPure_5802_);
        v___x_5809_ = lean_apply_4(
            v_toBind_5798_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_5806_,
            v___f_5803_,
        );
        v___x_5810_ = lean_apply_4(
            v_toBind_5798_,
            lean_box(0),
            lean_box(0),
            v___x_5809_,
            v___f_5808_,
        );
        return v___x_5810_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__13___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5811_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5812_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5813_: *mut LeanObject = *_args.add(2);
    let mut v_inst_5814_: *mut LeanObject = *_args.add(3);
    let mut v_inst_5815_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5816_: *mut LeanObject = *_args.add(5);
    let mut v___f_5817_: *mut LeanObject = *_args.add(6);
    let mut v_cls_5818_: *mut LeanObject = *_args.add(7);
    let mut v_collapsed_5819_: *mut LeanObject = *_args.add(8);
    let mut v_tag_5820_: *mut LeanObject = *_args.add(9);
    let mut v_msg_5821_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_5822_: *mut LeanObject = *_args.add(11);
    let mut v___f_5823_: *mut LeanObject = *_args.add(12);
    let mut v___f_5824_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5825_: *mut LeanObject = *_args.add(14);
    let mut v_toPure_5826_: *mut LeanObject = *_args.add(15);
    let mut v___f_5827_: *mut LeanObject = *_args.add(16);
    let mut v_opts_5828_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5829_: u8 = 0;
    let mut v_res_5830_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5829_ = (lean_unbox(v_collapsed_5819_) as u8);
    v_res_5830_ = l_Lean_withTraceNode_x27___redArg___lam__13(
        v_k_5811_,
        v_inst_5812_,
        v_inst_5813_,
        v_inst_5814_,
        v_inst_5815_,
        v_inst_5816_,
        v___f_5817_,
        v_cls_5818_,
        v_collapsed_boxed_5829_,
        v_tag_5820_,
        v_msg_5821_,
        v_toBind_5822_,
        v___f_5823_,
        v___f_5824_,
        v_inst_5825_,
        v_toPure_5826_,
        v___f_5827_,
        v_opts_5828_,
    );
    return v_res_5830_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg(
    mut v_inst_5832_: *mut LeanObject,
    mut v_inst_5833_: *mut LeanObject,
    mut v_inst_5834_: *mut LeanObject,
    mut v_inst_5835_: *mut LeanObject,
    mut v_inst_5836_: *mut LeanObject,
    mut v_inst_5837_: *mut LeanObject,
    mut v_inst_5838_: *mut LeanObject,
    mut v_cls_5839_: *mut LeanObject,
    mut v_k_5840_: *mut LeanObject,
    mut v_collapsed_5841_: u8,
    mut v_tag_5842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5843_ = lean_ctor_get(v_inst_5832_, 0);
    v_toFunctor_5844_ = lean_ctor_get(v_toApplicative_5843_, 0);
    v_toBind_5845_ = lean_ctor_get(v_inst_5832_, 1);
    lean_inc_n(v_toBind_5845_, 3);
    v_toPure_5846_ = lean_ctor_get(v_toApplicative_5843_, 1);
    lean_inc_n(v_toPure_5846_, 5);
    v_map_5847_ = lean_ctor_get(v_toFunctor_5844_, 0);
    lean_inc(v_map_5847_);
    v___f_5848_ = l_Lean_withTraceNode_x27___redArg___closed__0;
    v_msg_5849_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v_msg_5849_, 0, v_toPure_5846_);
    lean_inc(v_inst_5836_);
    lean_inc(v_cls_5839_);
    v___f_5850_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5850_, 0, v_toPure_5846_);
    lean_closure_set(v___f_5850_, 1, v_cls_5839_);
    lean_closure_set(v___f_5850_, 2, v_toBind_5845_);
    lean_closure_set(v___f_5850_, 3, v_inst_5836_);
    v___f_5851_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5851_, 0, v_toPure_5846_);
    v___f_5852_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5852_, 0, v_toPure_5846_);
    v___f_5853_ = l_Lean_instExceptToTraceResult___closed__0;
    v___x_5854_ = lean_box((v_collapsed_5841_) as usize);
    v___f_5855_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__13___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    lean_closure_set(v___f_5855_, 0, v_k_5840_);
    lean_closure_set(v___f_5855_, 1, v_inst_5833_);
    lean_closure_set(v___f_5855_, 2, v_inst_5837_);
    lean_closure_set(v___f_5855_, 3, v_inst_5832_);
    lean_closure_set(v___f_5855_, 4, v_inst_5834_);
    lean_closure_set(v___f_5855_, 5, v_inst_5835_);
    lean_closure_set(v___f_5855_, 6, v___f_5853_);
    lean_closure_set(v___f_5855_, 7, v_cls_5839_);
    lean_closure_set(v___f_5855_, 8, v___x_5854_);
    lean_closure_set(v___f_5855_, 9, v_tag_5842_);
    lean_closure_set(v___f_5855_, 10, v_msg_5849_);
    lean_closure_set(v___f_5855_, 11, v_toBind_5845_);
    lean_closure_set(v___f_5855_, 12, v___f_5852_);
    lean_closure_set(v___f_5855_, 13, v___f_5851_);
    lean_closure_set(v___f_5855_, 14, v_inst_5838_);
    lean_closure_set(v___f_5855_, 15, v_toPure_5846_);
    lean_closure_set(v___f_5855_, 16, v___f_5850_);
    v___x_5856_ = lean_apply_4(
        v_toBind_5845_,
        lean_box(0),
        lean_box(0),
        v_inst_5836_,
        v___f_5855_,
    );
    v___x_5857_ = lean_apply_4(
        v_map_5847_,
        lean_box(0),
        lean_box(0),
        v___f_5848_,
        v___x_5856_,
    );
    return v___x_5857_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___boxed(
    mut v_inst_5858_: *mut LeanObject,
    mut v_inst_5859_: *mut LeanObject,
    mut v_inst_5860_: *mut LeanObject,
    mut v_inst_5861_: *mut LeanObject,
    mut v_inst_5862_: *mut LeanObject,
    mut v_inst_5863_: *mut LeanObject,
    mut v_inst_5864_: *mut LeanObject,
    mut v_cls_5865_: *mut LeanObject,
    mut v_k_5866_: *mut LeanObject,
    mut v_collapsed_5867_: *mut LeanObject,
    mut v_tag_5868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5869_: u8 = 0;
    let mut v_res_5870_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5869_ = (lean_unbox(v_collapsed_5867_) as u8);
    v_res_5870_ = l_Lean_withTraceNode_x27___redArg(
        v_inst_5858_,
        v_inst_5859_,
        v_inst_5860_,
        v_inst_5861_,
        v_inst_5862_,
        v_inst_5863_,
        v_inst_5864_,
        v_cls_5865_,
        v_k_5866_,
        v_collapsed_boxed_5869_,
        v_tag_5868_,
    );
    return v_res_5870_;
}
pub unsafe fn l_Lean_withTraceNode_x27(
    mut v_00_u03b1_5871_: *mut LeanObject,
    mut v_m_5872_: *mut LeanObject,
    mut v_inst_5873_: *mut LeanObject,
    mut v_inst_5874_: *mut LeanObject,
    mut v_inst_5875_: *mut LeanObject,
    mut v_inst_5876_: *mut LeanObject,
    mut v_inst_5877_: *mut LeanObject,
    mut v_inst_5878_: *mut LeanObject,
    mut v_inst_5879_: *mut LeanObject,
    mut v_cls_5880_: *mut LeanObject,
    mut v_k_5881_: *mut LeanObject,
    mut v_collapsed_5882_: u8,
    mut v_tag_5883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5884_ = lean_ctor_get(v_inst_5873_, 0);
    v_toFunctor_5885_ = lean_ctor_get(v_toApplicative_5884_, 0);
    v_toBind_5886_ = lean_ctor_get(v_inst_5873_, 1);
    lean_inc_n(v_toBind_5886_, 3);
    v_toPure_5887_ = lean_ctor_get(v_toApplicative_5884_, 1);
    lean_inc_n(v_toPure_5887_, 5);
    v_map_5888_ = lean_ctor_get(v_toFunctor_5885_, 0);
    lean_inc(v_map_5888_);
    v___f_5889_ = l_Lean_withTraceNode_x27___redArg___closed__0;
    v_msg_5890_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v_msg_5890_, 0, v_toPure_5887_);
    lean_inc(v_inst_5877_);
    lean_inc(v_cls_5880_);
    v___f_5891_ = lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5891_, 0, v_toPure_5887_);
    lean_closure_set(v___f_5891_, 1, v_cls_5880_);
    lean_closure_set(v___f_5891_, 2, v_toBind_5886_);
    lean_closure_set(v___f_5891_, 3, v_inst_5877_);
    v___f_5892_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5892_, 0, v_toPure_5887_);
    v___f_5893_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5893_, 0, v_toPure_5887_);
    v___f_5894_ = l_Lean_instExceptToTraceResult___closed__0;
    v___x_5895_ = lean_box((v_collapsed_5882_) as usize);
    v___f_5896_ = lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__13___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    lean_closure_set(v___f_5896_, 0, v_k_5881_);
    lean_closure_set(v___f_5896_, 1, v_inst_5874_);
    lean_closure_set(v___f_5896_, 2, v_inst_5878_);
    lean_closure_set(v___f_5896_, 3, v_inst_5873_);
    lean_closure_set(v___f_5896_, 4, v_inst_5875_);
    lean_closure_set(v___f_5896_, 5, v_inst_5876_);
    lean_closure_set(v___f_5896_, 6, v___f_5894_);
    lean_closure_set(v___f_5896_, 7, v_cls_5880_);
    lean_closure_set(v___f_5896_, 8, v___x_5895_);
    lean_closure_set(v___f_5896_, 9, v_tag_5883_);
    lean_closure_set(v___f_5896_, 10, v_msg_5890_);
    lean_closure_set(v___f_5896_, 11, v_toBind_5886_);
    lean_closure_set(v___f_5896_, 12, v___f_5893_);
    lean_closure_set(v___f_5896_, 13, v___f_5892_);
    lean_closure_set(v___f_5896_, 14, v_inst_5879_);
    lean_closure_set(v___f_5896_, 15, v_toPure_5887_);
    lean_closure_set(v___f_5896_, 16, v___f_5891_);
    v___x_5897_ = lean_apply_4(
        v_toBind_5886_,
        lean_box(0),
        lean_box(0),
        v_inst_5877_,
        v___f_5896_,
    );
    v___x_5898_ = lean_apply_4(
        v_map_5888_,
        lean_box(0),
        lean_box(0),
        v___f_5889_,
        v___x_5897_,
    );
    return v___x_5898_;
}
pub unsafe fn l_Lean_withTraceNode_x27___boxed(
    mut v_00_u03b1_5899_: *mut LeanObject,
    mut v_m_5900_: *mut LeanObject,
    mut v_inst_5901_: *mut LeanObject,
    mut v_inst_5902_: *mut LeanObject,
    mut v_inst_5903_: *mut LeanObject,
    mut v_inst_5904_: *mut LeanObject,
    mut v_inst_5905_: *mut LeanObject,
    mut v_inst_5906_: *mut LeanObject,
    mut v_inst_5907_: *mut LeanObject,
    mut v_cls_5908_: *mut LeanObject,
    mut v_k_5909_: *mut LeanObject,
    mut v_collapsed_5910_: *mut LeanObject,
    mut v_tag_5911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5912_: u8 = 0;
    let mut v_res_5913_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5912_ = (lean_unbox(v_collapsed_5910_) as u8);
    v_res_5913_ = l_Lean_withTraceNode_x27(
        v_00_u03b1_5899_,
        v_m_5900_,
        v_inst_5901_,
        v_inst_5902_,
        v_inst_5903_,
        v_inst_5904_,
        v_inst_5905_,
        v_inst_5906_,
        v_inst_5907_,
        v_cls_5908_,
        v_k_5909_,
        v_collapsed_boxed_5912_,
        v_tag_5911_,
    );
    return v_res_5913_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__4() -> *mut LeanObject {
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    v___x_5922_ = l_Lean_registerTraceClass___auto__1___closed__3;
    v___x_5923_ = l_Lean_mkAtom(v___x_5922_);
    return v___x_5923_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__5() -> *mut LeanObject {
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    v___x_5924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__4_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__4,
    );
    v___x_5925_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5926_ = lean_array_push(v___x_5925_, v___x_5924_);
    return v___x_5926_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__6() -> *mut LeanObject {
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    v___x_5927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__5_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__5,
    );
    v___x_5928_ = l_Lean_registerTraceClass___auto__1___closed__2;
    v___x_5929_ = lean_box(2);
    v___x_5930_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5930_, 0, v___x_5929_);
    lean_ctor_set(v___x_5930_, 1, v___x_5928_);
    lean_ctor_set(v___x_5930_, 2, v___x_5927_);
    return v___x_5930_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__7() -> *mut LeanObject {
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    v___x_5931_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__6_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__6,
    );
    v___x_5932_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13,
    );
    v___x_5933_ = lean_array_push(v___x_5932_, v___x_5931_);
    return v___x_5933_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__8() -> *mut LeanObject {
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    v___x_5934_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__7),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__7_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__7,
    );
    v___x_5935_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11;
    v___x_5936_ = lean_box(2);
    v___x_5937_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5937_, 0, v___x_5936_);
    lean_ctor_set(v___x_5937_, 1, v___x_5935_);
    lean_ctor_set(v___x_5937_, 2, v___x_5934_);
    return v___x_5937_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__9() -> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    v___x_5938_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__8),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__8_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__8,
    );
    v___x_5939_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5940_ = lean_array_push(v___x_5939_, v___x_5938_);
    return v___x_5940_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__10() -> *mut LeanObject {
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    v___x_5941_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__9_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__9,
    );
    v___x_5942_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
    v___x_5943_ = lean_box(2);
    v___x_5944_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5944_, 0, v___x_5943_);
    lean_ctor_set(v___x_5944_, 1, v___x_5942_);
    lean_ctor_set(v___x_5944_, 2, v___x_5941_);
    return v___x_5944_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__11() -> *mut LeanObject {
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    v___x_5945_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__10_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__10,
    );
    v___x_5946_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5947_ = lean_array_push(v___x_5946_, v___x_5945_);
    return v___x_5947_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    v___x_5948_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__11_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__11,
    );
    v___x_5949_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7;
    v___x_5950_ = lean_box(2);
    v___x_5951_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5951_, 0, v___x_5950_);
    lean_ctor_set(v___x_5951_, 1, v___x_5949_);
    lean_ctor_set(v___x_5951_, 2, v___x_5948_);
    return v___x_5951_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    v___x_5952_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__12_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__12,
    );
    v___x_5953_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5954_ = lean_array_push(v___x_5953_, v___x_5952_);
    return v___x_5954_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__14() -> *mut LeanObject {
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    v___x_5955_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__13_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__13,
    );
    v___x_5956_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4;
    v___x_5957_ = lean_box(2);
    v___x_5958_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5958_, 0, v___x_5957_);
    lean_ctor_set(v___x_5958_, 1, v___x_5956_);
    lean_ctor_set(v___x_5958_, 2, v___x_5955_);
    return v___x_5958_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1() -> *mut LeanObject {
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    v___x_5959_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__14_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__14,
    );
    return v___x_5959_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_5960_: *mut LeanObject,
    mut v_x_5961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: u64 = 0;
    let mut v___x_5971_: u64 = 0;
    let mut v___x_5972_: u64 = 0;
    let mut v_fold_5973_: u64 = 0;
    let mut v___x_5974_: u64 = 0;
    let mut v___x_5975_: u64 = 0;
    let mut v___x_5976_: u64 = 0;
    let mut v___x_5977_: usize = 0;
    let mut v___x_5978_: usize = 0;
    let mut v___x_5979_: usize = 0;
    let mut v___x_5980_: usize = 0;
    let mut v___x_5981_: usize = 0;
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u64 = 0;
    let mut v_hash_5989_: u64 = 0;
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5961_) == 0 {
                    return v_x_5960_;
                } else {
                    v_key_5962_ = lean_ctor_get(v_x_5961_, 0);
                    v_value_5963_ = lean_ctor_get(v_x_5961_, 1);
                    v_tail_5964_ = lean_ctor_get(v_x_5961_, 2);
                    v_isSharedCheck_5990_ = (!lean_is_exclusive(v_x_5961_)) as u8;
                    if v_isSharedCheck_5990_ == 0 {
                        v___x_5966_ = v_x_5961_;
                        v_isShared_5967_ = v_isSharedCheck_5990_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5964_);
                        lean_inc(v_value_5963_);
                        lean_inc(v_key_5962_);
                        lean_dec(v_x_5961_);
                        v___x_5966_ = lean_box(0);
                        v_isShared_5967_ = v_isSharedCheck_5990_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5968_ = lean_array_get_size(v_x_5960_);
                if lean_obj_tag(v_key_5962_) == 0 {
                    v___x_5988_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_5970_ = v___x_5988_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5989_ = lean_ctor_get_uint64(
                        v_key_5962_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_5970_ = v_hash_5989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5971_ = 32u64;
                v___x_5972_ = lean_uint64_shift_right(v___y_5970_, v___x_5971_);
                v_fold_5973_ = lean_uint64_xor(v___y_5970_, v___x_5972_);
                v___x_5974_ = 16u64;
                v___x_5975_ = lean_uint64_shift_right(v_fold_5973_, v___x_5974_);
                v___x_5976_ = lean_uint64_xor(v_fold_5973_, v___x_5975_);
                v___x_5977_ = lean_uint64_to_usize(v___x_5976_);
                v___x_5978_ = lean_usize_of_nat(v___x_5968_);
                v___x_5979_ = 1usize;
                v___x_5980_ = lean_usize_sub(v___x_5978_, v___x_5979_);
                v___x_5981_ = lean_usize_land(v___x_5977_, v___x_5980_);
                v___x_5982_ = lean_array_uget_borrowed(v_x_5960_, v___x_5981_);
                lean_inc(v___x_5982_);
                if v_isShared_5967_ == 0 {
                    lean_ctor_set(v___x_5966_, 2, v___x_5982_);
                    v___x_5984_ = v___x_5966_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_key_5962_);
                    lean_ctor_set(v_reuseFailAlloc_5987_, 1, v_value_5963_);
                    lean_ctor_set(v_reuseFailAlloc_5987_, 2, v___x_5982_);
                    v___x_5984_ = v_reuseFailAlloc_5987_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5985_ = lean_array_uset(v_x_5960_, v___x_5981_, v___x_5984_);
                v_x_5960_ = v___x_5985_;
                v_x_5961_ = v_tail_5964_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(
    mut v_i_5991_: *mut LeanObject,
    mut v_source_5992_: *mut LeanObject,
    mut v_target_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: u8 = 0;
    let mut v_es_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5994_ = lean_array_get_size(v_source_5992_);
                v___x_5995_ = lean_nat_dec_lt(v_i_5991_, v___x_5994_);
                if v___x_5995_ == 0 {
                    lean_dec_ref(v_source_5992_);
                    lean_dec(v_i_5991_);
                    return v_target_5993_;
                } else {
                    v_es_5996_ = lean_array_fget(v_source_5992_, v_i_5991_);
                    v___x_5997_ = lean_box(0);
                    v_source_5998_ = lean_array_fset(v_source_5992_, v_i_5991_, v___x_5997_);
                    v_target_5999_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_5993_, v_es_5996_);
                    v___x_6000_ = lean_unsigned_to_nat(1);
                    v___x_6001_ = lean_nat_add(v_i_5991_, v___x_6000_);
                    lean_dec(v_i_5991_);
                    v_i_5991_ = v___x_6001_;
                    v_source_5992_ = v_source_5998_;
                    v_target_5993_ = v_target_5999_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(
    mut v_data_6003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    v___x_6004_ = lean_array_get_size(v_data_6003_);
    v___x_6005_ = lean_unsigned_to_nat(2);
    v_nbuckets_6006_ = lean_nat_mul(v___x_6004_, v___x_6005_);
    v___x_6007_ = lean_unsigned_to_nat(0);
    v___x_6008_ = lean_box(0);
    v___x_6009_ = lean_mk_array(v_nbuckets_6006_, v___x_6008_);
    v___x_6010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_6007_, v_data_6003_, v___x_6009_);
    return v___x_6010_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(
    mut v_m_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
    mut v_b_6013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6018_: u64 = 0;
    let mut v___x_6019_: u64 = 0;
    let mut v___x_6020_: u64 = 0;
    let mut v_fold_6021_: u64 = 0;
    let mut v___x_6022_: u64 = 0;
    let mut v___x_6023_: u64 = 0;
    let mut v___x_6024_: u64 = 0;
    let mut v___x_6025_: usize = 0;
    let mut v___x_6026_: usize = 0;
    let mut v___x_6027_: usize = 0;
    let mut v___x_6028_: usize = 0;
    let mut v___x_6029_: usize = 0;
    let mut v_bkt_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: u8 = 0;
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: u8 = 0;
    let mut v_val_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_unused_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u64 = 0;
    let mut v_hash_6056_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6014_ = lean_ctor_get(v_m_6011_, 0);
                v_buckets_6015_ = lean_ctor_get(v_m_6011_, 1);
                v___x_6016_ = lean_array_get_size(v_buckets_6015_);
                if lean_obj_tag(v_a_6012_) == 0 {
                    v___x_6055_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_6018_ = v___x_6055_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6056_ = lean_ctor_get_uint64(
                        v_a_6012_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_6018_ = v_hash_6056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6019_ = 32u64;
                v___x_6020_ = lean_uint64_shift_right(v___y_6018_, v___x_6019_);
                v_fold_6021_ = lean_uint64_xor(v___y_6018_, v___x_6020_);
                v___x_6022_ = 16u64;
                v___x_6023_ = lean_uint64_shift_right(v_fold_6021_, v___x_6022_);
                v___x_6024_ = lean_uint64_xor(v_fold_6021_, v___x_6023_);
                v___x_6025_ = lean_uint64_to_usize(v___x_6024_);
                v___x_6026_ = lean_usize_of_nat(v___x_6016_);
                v___x_6027_ = 1usize;
                v___x_6028_ = lean_usize_sub(v___x_6026_, v___x_6027_);
                v___x_6029_ = lean_usize_land(v___x_6025_, v___x_6028_);
                v_bkt_6030_ = lean_array_uget_borrowed(v_buckets_6015_, v___x_6029_);
                v___x_6031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_6012_, v_bkt_6030_);
                if v___x_6031_ == 0 {
                    lean_inc_ref(v_buckets_6015_);
                    lean_inc(v_size_6014_);
                    v_isSharedCheck_6052_ = (!lean_is_exclusive(v_m_6011_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v_unused_6053_ = lean_ctor_get(v_m_6011_, 1);
                        lean_dec(v_unused_6053_);
                        v_unused_6054_ = lean_ctor_get(v_m_6011_, 0);
                        lean_dec(v_unused_6054_);
                        v___x_6033_ = v_m_6011_;
                        v_isShared_6034_ = v_isSharedCheck_6052_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_6011_);
                        v___x_6033_ = lean_box(0);
                        v_isShared_6034_ = v_isSharedCheck_6052_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_6013_);
                    lean_dec(v_a_6012_);
                    return v_m_6011_;
                }
            }
            2 => {
                v___x_6035_ = lean_unsigned_to_nat(1);
                v_size_x27_6036_ = lean_nat_add(v_size_6014_, v___x_6035_);
                lean_dec(v_size_6014_);
                lean_inc(v_bkt_6030_);
                v___x_6037_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6037_, 0, v_a_6012_);
                lean_ctor_set(v___x_6037_, 1, v_b_6013_);
                lean_ctor_set(v___x_6037_, 2, v_bkt_6030_);
                v_buckets_x27_6038_ = lean_array_uset(v_buckets_6015_, v___x_6029_, v___x_6037_);
                v___x_6039_ = lean_unsigned_to_nat(4);
                v___x_6040_ = lean_nat_mul(v_size_x27_6036_, v___x_6039_);
                v___x_6041_ = lean_unsigned_to_nat(3);
                v___x_6042_ = lean_nat_div(v___x_6040_, v___x_6041_);
                lean_dec(v___x_6040_);
                v___x_6043_ = lean_array_get_size(v_buckets_x27_6038_);
                v___x_6044_ = lean_nat_dec_le(v___x_6042_, v___x_6043_);
                lean_dec(v___x_6042_);
                if v___x_6044_ == 0 {
                    v_val_6045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_6038_);
                    if v_isShared_6034_ == 0 {
                        lean_ctor_set(v___x_6033_, 1, v_val_6045_);
                        lean_ctor_set(v___x_6033_, 0, v_size_x27_6036_);
                        v___x_6047_ = v___x_6033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_size_x27_6036_);
                        lean_ctor_set(v_reuseFailAlloc_6048_, 1, v_val_6045_);
                        v___x_6047_ = v_reuseFailAlloc_6048_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_6034_ == 0 {
                        lean_ctor_set(v___x_6033_, 1, v_buckets_x27_6038_);
                        lean_ctor_set(v___x_6033_, 0, v_size_x27_6036_);
                        v___x_6050_ = v___x_6033_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_size_x27_6036_);
                        lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_buckets_x27_6038_);
                        v___x_6050_ = v_reuseFailAlloc_6051_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6047_;
            }
            4 => {
                return v___x_6050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerTraceClass(
    mut v_traceClassName_6060_: *mut LeanObject,
    mut v_inherited_6061_: u8,
    mut v_ref_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionName_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut v_unused_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6064_ = l_Lean_checkTraceOption___closed__1;
                v_optionName_6065_ = l_Lean_Name_append(v___x_6064_, v_traceClassName_6060_);
                v___x_6066_ = l_Lean_registerTraceClass___closed__0;
                v___x_6067_ = l_Lean_registerTraceClass___closed__1;
                v___x_6068_ = lean_box(0);
                lean_inc_n(v_optionName_6065_, 2);
                v___x_6069_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_6069_, 0, v_optionName_6065_);
                lean_ctor_set(v___x_6069_, 1, v_ref_6062_);
                lean_ctor_set(v___x_6069_, 2, v___x_6066_);
                lean_ctor_set(v___x_6069_, 3, v___x_6067_);
                lean_ctor_set(v___x_6069_, 4, v___x_6068_);
                v___x_6070_ = lean_register_option(v_optionName_6065_, v___x_6069_);
                if lean_obj_tag(v___x_6070_) == 0 {
                    v_isSharedCheck_6086_ = (!lean_is_exclusive(v___x_6070_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v_unused_6087_ = lean_ctor_get(v___x_6070_, 0);
                        lean_dec(v_unused_6087_);
                        v___x_6072_ = v___x_6070_;
                        v_isShared_6073_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6070_);
                        v___x_6072_ = lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_optionName_6065_);
                    return v___x_6070_;
                }
            }
            1 => {
                if v_inherited_6061_ == 0 {
                    lean_dec(v_optionName_6065_);
                    v___x_6074_ = lean_box(0);
                    if v_isShared_6073_ == 0 {
                        lean_ctor_set(v___x_6072_, 0, v___x_6074_);
                        v___x_6076_ = v___x_6072_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6074_);
                        v___x_6076_ = v_reuseFailAlloc_6077_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6078_ = l_Lean_inheritedTraceOptions;
                    v___x_6079_ = lean_st_ref_take(v___x_6078_);
                    v___x_6080_ = lean_box(0);
                    v___x_6081_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_6079_, v_optionName_6065_, v___x_6080_);
                    v___x_6082_ = lean_st_ref_set(v___x_6078_, v___x_6081_);
                    if v_isShared_6073_ == 0 {
                        lean_ctor_set(v___x_6072_, 0, v___x_6082_);
                        v___x_6084_ = v___x_6072_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6085_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6085_, 0, v___x_6082_);
                        v___x_6084_ = v_reuseFailAlloc_6085_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6076_;
            }
            3 => {
                return v___x_6084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerTraceClass___boxed(
    mut v_traceClassName_6088_: *mut LeanObject,
    mut v_inherited_6089_: *mut LeanObject,
    mut v_ref_6090_: *mut LeanObject,
    mut v_a_6091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inherited_boxed_6092_: u8 = 0;
    let mut v_res_6093_: *mut LeanObject = core::ptr::null_mut();
    v_inherited_boxed_6092_ = (lean_unbox(v_inherited_6089_) as u8);
    v_res_6093_ =
        l_Lean_registerTraceClass(v_traceClassName_6088_, v_inherited_boxed_6092_, v_ref_6090_);
    return v_res_6093_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(
    mut v_00_u03b2_6094_: *mut LeanObject,
    mut v_m_6095_: *mut LeanObject,
    mut v_a_6096_: *mut LeanObject,
    mut v_b_6097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    v___x_6098_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_6095_, v_a_6096_, v_b_6097_);
    return v___x_6098_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(
    mut v_00_u03b2_6099_: *mut LeanObject,
    mut v_data_6100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    v___x_6101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_6100_);
    return v___x_6101_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6102_: *mut LeanObject,
    mut v_i_6103_: *mut LeanObject,
    mut v_source_6104_: *mut LeanObject,
    mut v_target_6105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    v___x_6106_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_6103_, v_source_6104_, v_target_6105_);
    return v___x_6106_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_6107_: *mut LeanObject,
    mut v_x_6108_: *mut LeanObject,
    mut v_x_6109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    v___x_6110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_6108_, v_x_6109_);
    return v___x_6110_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8()
-> *mut LeanObject {
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    v___x_6120_ = l_Lean_addTrace___redArg___lam__0___closed__1;
    v___x_6121_ = l_String_toRawSubstring_x27(v___x_6120_);
    return v___x_6121_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13()
-> *mut LeanObject {
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    v___x_6126_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12;
    v___x_6127_ = l_String_toRawSubstring_x27(v___x_6126_);
    return v___x_6127_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19()
-> *mut LeanObject {
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    v___x_6133_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18;
    v___x_6134_ = l_String_toRawSubstring_x27(v___x_6133_);
    return v___x_6134_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31()
-> *mut LeanObject {
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    v___x_6162_ = l_Array_mkArray0(lean_box(0));
    return v___x_6162_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41()
-> *mut LeanObject {
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    v___x_6188_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40;
    v___x_6189_ = l_String_toRawSubstring_x27(v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58()
-> *mut LeanObject {
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    v___x_6224_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57;
    v___x_6225_ = l_String_toRawSubstring_x27(v___x_6224_);
    return v___x_6225_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
    mut v_id_6247_: *mut LeanObject,
    mut v_s_6248_: *mut LeanObject,
    mut v_a_6249_: *mut LeanObject,
    mut v_a_6250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: u8 = 0;
    let mut v_quotContext_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: u8 = 0;
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_s_6248_);
                v___x_6397_ = l_Lean_Syntax_getKind(v_s_6248_);
                v___x_6398_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49;
                v___x_6399_ = lean_name_eq(v___x_6397_, v___x_6398_);
                lean_dec(v___x_6397_);
                if v___x_6399_ == 0 {
                    v_quotContext_6400_ = lean_ctor_get(v_a_6249_, 1);
                    v_currMacroScope_6401_ = lean_ctor_get(v_a_6249_, 2);
                    v_ref_6402_ = lean_ctor_get(v_a_6249_, 5);
                    v___x_6403_ = l_Lean_SourceInfo_fromRef(v_ref_6402_, v___x_6399_);
                    v___x_6404_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51;
                    v___x_6405_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52;
                    v___x_6406_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5;
                    lean_inc_n(v___x_6403_, 8);
                    v___x_6407_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6407_, 0, v___x_6403_);
                    lean_ctor_set(v___x_6407_, 1, v___x_6406_);
                    v___x_6408_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7;
                    v___x_6409_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once
                        ),
                        _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8,
                    );
                    v___x_6410_ = lean_box(0);
                    lean_inc_n(v_currMacroScope_6401_, 3);
                    lean_inc_n(v_quotContext_6400_, 3);
                    v___x_6411_ = l_Lean_addMacroScope(
                        v_quotContext_6400_,
                        v___x_6410_,
                        v_currMacroScope_6401_,
                    );
                    v___x_6412_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55;
                    v___x_6413_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_6413_, 0, v___x_6403_);
                    lean_ctor_set(v___x_6413_, 1, v___x_6409_);
                    lean_ctor_set(v___x_6413_, 2, v___x_6411_);
                    lean_ctor_set(v___x_6413_, 3, v___x_6412_);
                    v___x_6414_ = l_Lean_Syntax_node1(v___x_6403_, v___x_6408_, v___x_6413_);
                    v___x_6415_ =
                        l_Lean_Syntax_node2(v___x_6403_, v___x_6405_, v___x_6407_, v___x_6414_);
                    v___x_6416_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56;
                    v___x_6417_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6417_, 0, v___x_6403_);
                    lean_ctor_set(v___x_6417_, 1, v___x_6416_);
                    v___x_6418_ =
                        l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
                    v___x_6419_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once
                        ),
                        _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58,
                    );
                    v___x_6420_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59;
                    v___x_6421_ = l_Lean_addMacroScope(
                        v_quotContext_6400_,
                        v___x_6420_,
                        v_currMacroScope_6401_,
                    );
                    v___x_6422_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64;
                    v___x_6423_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_6423_, 0, v___x_6403_);
                    lean_ctor_set(v___x_6423_, 1, v___x_6419_);
                    lean_ctor_set(v___x_6423_, 2, v___x_6421_);
                    lean_ctor_set(v___x_6423_, 3, v___x_6422_);
                    v___x_6424_ = l_Lean_Syntax_node1(v___x_6403_, v___x_6418_, v___x_6423_);
                    v___x_6425_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15;
                    v___x_6426_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6426_, 0, v___x_6403_);
                    lean_ctor_set(v___x_6426_, 1, v___x_6425_);
                    v___x_6427_ = l_Lean_Syntax_node5(
                        v___x_6403_,
                        v___x_6404_,
                        v___x_6415_,
                        v_s_6248_,
                        v___x_6417_,
                        v___x_6424_,
                        v___x_6426_,
                    );
                    v_msg_6347_ = v___x_6427_;
                    v_quotContext_6348_ = v_quotContext_6400_;
                    v_currMacroScope_6349_ = v_currMacroScope_6401_;
                    v_ref_6350_ = v_ref_6402_;
                    v___y_6351_ = v_a_6250_;
                    state = 2;
                    continue;
                } else {
                    v_quotContext_6428_ = lean_ctor_get(v_a_6249_, 1);
                    v_currMacroScope_6429_ = lean_ctor_get(v_a_6249_, 2);
                    v_ref_6430_ = lean_ctor_get(v_a_6249_, 5);
                    v___x_6431_ = 0;
                    v___x_6432_ = l_Lean_SourceInfo_fromRef(v_ref_6430_, v___x_6431_);
                    v___x_6433_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66;
                    v___x_6434_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67;
                    lean_inc(v___x_6432_);
                    v___x_6435_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6435_, 0, v___x_6432_);
                    lean_ctor_set(v___x_6435_, 1, v___x_6434_);
                    v___x_6436_ =
                        l_Lean_Syntax_node2(v___x_6432_, v___x_6433_, v___x_6435_, v_s_6248_);
                    lean_inc(v_currMacroScope_6429_);
                    lean_inc(v_quotContext_6428_);
                    v_msg_6347_ = v___x_6436_;
                    v_quotContext_6348_ = v_quotContext_6428_;
                    v_currMacroScope_6349_ = v_currMacroScope_6429_;
                    v_ref_6350_ = v_ref_6430_;
                    v___y_6351_ = v_a_6250_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v___y_6262_, 8);
                lean_inc(v___y_6264_);
                lean_inc_n(v___y_6261_, 29);
                v___x_6276_ = l_Lean_Syntax_node5(
                    v___y_6261_,
                    v___y_6264_,
                    v___y_6270_,
                    v___y_6262_,
                    v___y_6262_,
                    v___y_6259_,
                    v___y_6275_,
                );
                lean_inc(v___y_6265_);
                v___x_6277_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6265_, v___x_6276_);
                lean_inc(v___y_6255_);
                v___x_6278_ = l_Lean_Syntax_node4(
                    v___y_6261_,
                    v___y_6255_,
                    v___y_6272_,
                    v___y_6262_,
                    v___y_6263_,
                    v___x_6277_,
                );
                lean_inc_n(v___y_6258_, 3);
                v___x_6279_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6258_, v___x_6278_, v___y_6262_);
                v___x_6280_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0;
                lean_inc_ref_n(v___y_6268_, 7);
                lean_inc_ref_n(v___y_6273_, 7);
                lean_inc_ref_n(v___y_6269_, 10);
                v___x_6281_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6280_);
                v___x_6282_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1;
                v___x_6283_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6283_, 0, v___y_6261_);
                lean_ctor_set(v___x_6283_, 1, v___x_6282_);
                v___x_6284_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2;
                v___x_6285_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6284_);
                v___x_6286_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3;
                v___x_6287_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6286_);
                v___x_6288_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4;
                v___x_6289_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6288_);
                v___x_6290_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5;
                v___x_6291_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6291_, 0, v___y_6261_);
                lean_ctor_set(v___x_6291_, 1, v___x_6290_);
                v___x_6292_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7;
                v___x_6293_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8,
                );
                v___x_6294_ = lean_box(0);
                lean_inc_n(v___y_6254_, 2);
                lean_inc_n(v___y_6271_, 2);
                v___x_6295_ = l_Lean_addMacroScope(v___y_6271_, v___x_6294_, v___y_6254_);
                v___x_6296_ = l_Lean_Name_mkStr1(v___y_6269_);
                v___x_6297_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6297_, 0, v___x_6296_);
                lean_inc_n(v___y_6253_, 2);
                v___x_6298_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6298_, 0, v___x_6297_);
                lean_ctor_set(v___x_6298_, 1, v___y_6253_);
                v___x_6299_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6299_, 0, v___y_6261_);
                lean_ctor_set(v___x_6299_, 1, v___x_6293_);
                lean_ctor_set(v___x_6299_, 2, v___x_6295_);
                lean_ctor_set(v___x_6299_, 3, v___x_6298_);
                v___x_6300_ = l_Lean_Syntax_node1(v___y_6261_, v___x_6292_, v___x_6299_);
                v___x_6301_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6289_, v___x_6291_, v___x_6300_);
                v___x_6302_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9;
                v___x_6303_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6302_);
                v___x_6304_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10;
                v___x_6305_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6305_, 0, v___y_6261_);
                lean_ctor_set(v___x_6305_, 1, v___x_6304_);
                v___x_6306_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11;
                v___x_6307_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6306_);
                v___x_6308_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13,
                );
                v___x_6309_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14;
                v___x_6310_ = l_Lean_Name_mkStr2(v___y_6269_, v___x_6309_);
                lean_inc(v___x_6310_);
                v___x_6311_ = l_Lean_addMacroScope(v___y_6271_, v___x_6310_, v___y_6254_);
                v___x_6312_ = lean_box(0);
                v___x_6313_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6313_, 0, v___x_6310_);
                lean_ctor_set(v___x_6313_, 1, v___x_6312_);
                v___x_6314_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6314_, 0, v___x_6313_);
                lean_ctor_set(v___x_6314_, 1, v___y_6253_);
                v___x_6315_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6315_, 0, v___y_6261_);
                lean_ctor_set(v___x_6315_, 1, v___x_6308_);
                lean_ctor_set(v___x_6315_, 2, v___x_6311_);
                lean_ctor_set(v___x_6315_, 3, v___x_6314_);
                lean_inc(v___y_6257_);
                lean_inc_n(v___y_6260_, 4);
                v___x_6316_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6260_, v___y_6257_);
                lean_inc(v___x_6307_);
                v___x_6317_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6307_, v___x_6315_, v___x_6316_);
                v___x_6318_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6303_, v___x_6305_, v___x_6317_);
                v___x_6319_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15;
                v___x_6320_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6320_, 0, v___y_6261_);
                lean_ctor_set(v___x_6320_, 1, v___x_6319_);
                v___x_6321_ = l_Lean_Syntax_node3(
                    v___y_6261_,
                    v___x_6287_,
                    v___x_6301_,
                    v___x_6318_,
                    v___x_6320_,
                );
                v___x_6322_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6285_, v___y_6262_, v___x_6321_);
                v___x_6323_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16;
                v___x_6324_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6324_, 0, v___y_6261_);
                lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                v___x_6325_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17;
                v___x_6326_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6325_);
                v___x_6327_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19,
                );
                v___x_6328_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20;
                v___x_6329_ = l_Lean_Name_mkStr2(v___y_6269_, v___x_6328_);
                lean_inc(v___x_6329_);
                v___x_6330_ = l_Lean_addMacroScope(v___y_6271_, v___x_6329_, v___y_6254_);
                v___x_6331_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6331_, 0, v___x_6329_);
                lean_ctor_set(v___x_6331_, 1, v___x_6312_);
                v___x_6332_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6332_, 0, v___x_6331_);
                lean_ctor_set(v___x_6332_, 1, v___y_6253_);
                v___x_6333_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6333_, 0, v___y_6261_);
                lean_ctor_set(v___x_6333_, 1, v___x_6327_);
                lean_ctor_set(v___x_6333_, 2, v___x_6330_);
                lean_ctor_set(v___x_6333_, 3, v___x_6332_);
                v___x_6334_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6260_, v___y_6257_, v___y_6252_);
                v___x_6335_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6307_, v___x_6333_, v___x_6334_);
                v___x_6336_ = l_Lean_Syntax_node1(v___y_6261_, v___x_6326_, v___x_6335_);
                v___x_6337_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6258_, v___x_6336_, v___y_6262_);
                v___x_6338_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6260_, v___x_6337_);
                lean_inc_n(v___y_6266_, 2);
                v___x_6339_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6266_, v___x_6338_);
                v___x_6340_ = l_Lean_Syntax_node6(
                    v___y_6261_,
                    v___x_6281_,
                    v___x_6283_,
                    v___x_6322_,
                    v___x_6324_,
                    v___x_6339_,
                    v___y_6262_,
                    v___y_6262_,
                );
                v___x_6341_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6258_, v___x_6340_, v___y_6262_);
                v___x_6342_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6260_, v___x_6279_, v___x_6341_);
                v___x_6343_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6266_, v___x_6342_);
                lean_inc(v___y_6274_);
                v___x_6344_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6274_, v___y_6256_, v___x_6343_);
                v___x_6345_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6345_, 0, v___x_6344_);
                lean_ctor_set(v___x_6345_, 1, v___y_6267_);
                return v___x_6345_;
            }
            2 => {
                v___x_6352_ = 0;
                v___x_6353_ = l_Lean_SourceInfo_fromRef(v_ref_6350_, v___x_6352_);
                v___x_6354_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0;
                v___x_6355_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1;
                v___x_6356_ = l_Lean_registerTraceClass___auto__1___closed__0;
                v___x_6357_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22;
                v___x_6358_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23;
                lean_inc_n(v___x_6353_, 7);
                v___x_6359_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6359_, 0, v___x_6353_);
                lean_ctor_set(v___x_6359_, 1, v___x_6358_);
                v___x_6360_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25;
                v___x_6361_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
                v___x_6362_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27;
                v___x_6363_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29;
                v___x_6364_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30;
                v___x_6365_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6365_, 0, v___x_6353_);
                lean_ctor_set(v___x_6365_, 1, v___x_6364_);
                v___x_6366_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31,
                );
                v___x_6367_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6367_, 0, v___x_6353_);
                lean_ctor_set(v___x_6367_, 1, v___x_6361_);
                lean_ctor_set(v___x_6367_, 2, v___x_6366_);
                v___x_6368_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33;
                lean_inc_ref(v___x_6367_);
                v___x_6369_ = l_Lean_Syntax_node1(v___x_6353_, v___x_6368_, v___x_6367_);
                v___x_6370_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35;
                v___x_6371_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37;
                v___x_6372_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39;
                v___x_6373_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41,
                );
                v___x_6374_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42;
                lean_inc(v_currMacroScope_6349_);
                lean_inc(v_quotContext_6348_);
                v___x_6375_ =
                    l_Lean_addMacroScope(v_quotContext_6348_, v___x_6374_, v_currMacroScope_6349_);
                v___x_6376_ = lean_box(0);
                v___x_6377_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6377_, 0, v___x_6353_);
                lean_ctor_set(v___x_6377_, 1, v___x_6373_);
                lean_ctor_set(v___x_6377_, 2, v___x_6375_);
                lean_ctor_set(v___x_6377_, 3, v___x_6376_);
                lean_inc_ref(v___x_6377_);
                v___x_6378_ = l_Lean_Syntax_node1(v___x_6353_, v___x_6372_, v___x_6377_);
                v___x_6379_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43;
                v___x_6380_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6380_, 0, v___x_6353_);
                lean_ctor_set(v___x_6380_, 1, v___x_6379_);
                v___x_6381_ = l_Lean_Syntax_getId(v_id_6247_);
                v___x_6382_ = lean_erase_macro_scopes(v___x_6381_);
                lean_inc(v___x_6382_);
                v___x_6383_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_6376_,
                    v___x_6382_,
                );
                if lean_obj_tag(v___x_6383_) == 0 {
                    v___x_6384_ = l_Lean_quoteNameMk(v___x_6382_);
                    v___y_6252_ = v_msg_6347_;
                    v___y_6253_ = v___x_6376_;
                    v___y_6254_ = v_currMacroScope_6349_;
                    v___y_6255_ = v___x_6363_;
                    v___y_6256_ = v___x_6359_;
                    v___y_6257_ = v___x_6377_;
                    v___y_6258_ = v___x_6362_;
                    v___y_6259_ = v___x_6380_;
                    v___y_6260_ = v___x_6361_;
                    v___y_6261_ = v___x_6353_;
                    v___y_6262_ = v___x_6367_;
                    v___y_6263_ = v___x_6369_;
                    v___y_6264_ = v___x_6371_;
                    v___y_6265_ = v___x_6370_;
                    v___y_6266_ = v___x_6360_;
                    v___y_6267_ = v___y_6351_;
                    v___y_6268_ = v___x_6356_;
                    v___y_6269_ = v___x_6354_;
                    v___y_6270_ = v___x_6378_;
                    v___y_6271_ = v_quotContext_6348_;
                    v___y_6272_ = v___x_6365_;
                    v___y_6273_ = v___x_6355_;
                    v___y_6274_ = v___x_6357_;
                    v___y_6275_ = v___x_6384_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_6382_);
                    v_val_6385_ = lean_ctor_get(v___x_6383_, 0);
                    lean_inc(v_val_6385_);
                    lean_dec_ref_known(v___x_6383_, 1);
                    v___x_6386_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45;
                    v___x_6387_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46;
                    v___x_6388_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47;
                    v___x_6389_ = lean_string_intercalate(v___x_6388_, v_val_6385_);
                    v___x_6390_ = lean_string_append(v___x_6387_, v___x_6389_);
                    lean_dec_ref(v___x_6389_);
                    v___x_6391_ = lean_box(2);
                    v___x_6392_ = l_Lean_Syntax_mkNameLit(v___x_6390_, v___x_6391_);
                    v___x_6393_ = lean_unsigned_to_nat(1);
                    v___x_6394_ = lean_mk_empty_array_with_capacity(v___x_6393_);
                    v___x_6395_ = lean_array_push(v___x_6394_, v___x_6392_);
                    v___x_6396_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6396_, 0, v___x_6391_);
                    lean_ctor_set(v___x_6396_, 1, v___x_6386_);
                    lean_ctor_set(v___x_6396_, 2, v___x_6395_);
                    v___y_6252_ = v_msg_6347_;
                    v___y_6253_ = v___x_6376_;
                    v___y_6254_ = v_currMacroScope_6349_;
                    v___y_6255_ = v___x_6363_;
                    v___y_6256_ = v___x_6359_;
                    v___y_6257_ = v___x_6377_;
                    v___y_6258_ = v___x_6362_;
                    v___y_6259_ = v___x_6380_;
                    v___y_6260_ = v___x_6361_;
                    v___y_6261_ = v___x_6353_;
                    v___y_6262_ = v___x_6367_;
                    v___y_6263_ = v___x_6369_;
                    v___y_6264_ = v___x_6371_;
                    v___y_6265_ = v___x_6370_;
                    v___y_6266_ = v___x_6360_;
                    v___y_6267_ = v___y_6351_;
                    v___y_6268_ = v___x_6356_;
                    v___y_6269_ = v___x_6354_;
                    v___y_6270_ = v___x_6378_;
                    v___y_6271_ = v_quotContext_6348_;
                    v___y_6272_ = v___x_6365_;
                    v___y_6273_ = v___x_6355_;
                    v___y_6274_ = v___x_6357_;
                    v___y_6275_ = v___x_6396_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(
    mut v_id_6437_: *mut LeanObject,
    mut v_s_6438_: *mut LeanObject,
    mut v_a_6439_: *mut LeanObject,
    mut v_a_6440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6441_: *mut LeanObject = core::ptr::null_mut();
    v_res_6441_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
        v_id_6437_, v_s_6438_, v_a_6439_, v_a_6440_,
    );
    lean_dec_ref(v_a_6439_);
    lean_dec(v_id_6437_);
    return v_res_6441_;
}
pub unsafe fn l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(
    mut v_x_6496_: *mut LeanObject,
    mut v_a_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: u8 = 0;
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6512_: u8 = 0;
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6499_ = l_Lean_doElemTrace_x5b___x5d_____00__closed__1;
                lean_inc(v_x_6496_);
                v___x_6500_ = l_Lean_Syntax_isOfKind(v_x_6496_, v___x_6499_);
                if v___x_6500_ == 0 {
                    lean_dec(v_x_6496_);
                    v___x_6501_ = lean_box(1);
                    v___x_6502_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6502_, 0, v___x_6501_);
                    lean_ctor_set(v___x_6502_, 1, v_a_6498_);
                    return v___x_6502_;
                } else {
                    v___x_6503_ = lean_unsigned_to_nat(1);
                    v___x_6504_ = l_Lean_Syntax_getArg(v_x_6496_, v___x_6503_);
                    v___x_6505_ = lean_unsigned_to_nat(3);
                    v___x_6506_ = l_Lean_Syntax_getArg(v_x_6496_, v___x_6505_);
                    lean_dec(v_x_6496_);
                    v___x_6507_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
                        v___x_6504_,
                        v___x_6506_,
                        v_a_6497_,
                        v_a_6498_,
                    );
                    lean_dec(v___x_6504_);
                    v_a_6508_ = lean_ctor_get(v___x_6507_, 0);
                    v_a_6509_ = lean_ctor_get(v___x_6507_, 1);
                    v_isSharedCheck_6516_ = (!lean_is_exclusive(v___x_6507_)) as u8;
                    if v_isSharedCheck_6516_ == 0 {
                        v___x_6511_ = v___x_6507_;
                        v_isShared_6512_ = v_isSharedCheck_6516_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6509_);
                        lean_inc(v_a_6508_);
                        lean_dec(v___x_6507_);
                        v___x_6511_ = lean_box(0);
                        v_isShared_6512_ = v_isSharedCheck_6516_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6512_ == 0 {
                    v___x_6514_ = v___x_6511_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6515_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6515_, 0, v_a_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6515_, 1, v_a_6509_);
                    v___x_6514_ = v_reuseFailAlloc_6515_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(
    mut v_x_6517_: *mut LeanObject,
    mut v_a_6518_: *mut LeanObject,
    mut v_a_6519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6520_: *mut LeanObject = core::ptr::null_mut();
    v_res_6520_ =
        l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(
            v_x_6517_, v_a_6518_, v_a_6519_,
        );
    lean_dec_ref(v_a_6518_);
    return v_res_6520_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(
    mut v_inst_6521_: *mut LeanObject,
    mut v_inst_6522_: *mut LeanObject,
    mut v_inst_6523_: *mut LeanObject,
    mut v_inst_6524_: *mut LeanObject,
    mut v_always_6525_: *mut LeanObject,
    mut v_inst_6526_: *mut LeanObject,
    mut v_cls_6527_: *mut LeanObject,
    mut v_collapsed_6528_: u8,
    mut v_tag_6529_: *mut LeanObject,
    mut v_opts_6530_: *mut LeanObject,
    mut v_clsEnabled_6531_: u8,
    mut v_oldTraces_6532_: *mut LeanObject,
    mut v_ref_6533_: *mut LeanObject,
    mut v_msg_6534_: *mut LeanObject,
    mut v_resStartStop_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6541_: u8 = 0;
    let mut v_fst_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v___f_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: u8 = 0;
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: f64 = 0.0;
    let mut v_data_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v_data_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: f64 = 0.0;
    let mut v___x_6573_: f64 = 0.0;
    let mut v_reuseFailAlloc_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: u8 = 0;
    let mut v_toBind_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6583_: f64 = 0.0;
    let mut v___x_6584_: f64 = 0.0;
    let mut v___x_6585_: f64 = 0.0;
    let mut v___x_6586_: f64 = 0.0;
    let mut v___x_6587_: u8 = 0;
    let mut v___x_6588_: u8 = 0;
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: u8 = 0;
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: f64 = 0.0;
    let mut v___x_6597_: f64 = 0.0;
    let mut v___x_6598_: f64 = 0.0;
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: f64 = 0.0;
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6536_ = l_Lean_KVMap_instValueBool;
                v_snd_6537_ = lean_ctor_get(v_resStartStop_6535_, 1);
                v_fst_6538_ = lean_ctor_get(v_resStartStop_6535_, 0);
                v_isSharedCheck_6604_ = (!lean_is_exclusive(v_resStartStop_6535_)) as u8;
                if v_isSharedCheck_6604_ == 0 {
                    v___x_6540_ = v_resStartStop_6535_;
                    v_isShared_6541_ = v_isSharedCheck_6604_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_6537_);
                    lean_inc(v_fst_6538_);
                    lean_dec(v_resStartStop_6535_);
                    v___x_6540_ = lean_box(0);
                    v_isShared_6541_ = v_isSharedCheck_6604_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_6542_ = lean_ctor_get(v_snd_6537_, 0);
                v_snd_6543_ = lean_ctor_get(v_snd_6537_, 1);
                v_isSharedCheck_6603_ = (!lean_is_exclusive(v_snd_6537_)) as u8;
                if v_isSharedCheck_6603_ == 0 {
                    v___x_6545_ = v_snd_6537_;
                    v_isShared_6546_ = v_isSharedCheck_6603_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_6543_);
                    lean_inc(v_fst_6542_);
                    lean_dec(v_snd_6537_);
                    v___x_6545_ = lean_box(0);
                    v_isShared_6546_ = v_isSharedCheck_6603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_oldTraces_6532_);
                v___f_6547_ = lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6547_, 0, v_oldTraces_6532_);
                lean_inc(v_fst_6538_);
                lean_inc_ref(v_inst_6521_);
                v___f_6548_ = lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_6548_, 0, v_always_6525_);
                lean_closure_set(v___f_6548_, 1, v_inst_6521_);
                lean_closure_set(v___f_6548_, 2, v_fst_6538_);
                v___x_6555_ = l_Lean_trace_profiler;
                v___x_6556_ = l_Lean_Option_get___redArg(v___x_6536_, v_opts_6530_, v___x_6555_);
                v___x_6588_ = (lean_unbox(v___x_6556_) as u8);
                if v___x_6588_ == 0 {
                    v___x_6589_ = (lean_unbox(v___x_6556_) as u8);
                    v___y_6577_ = v___x_6589_;
                    state = 7;
                    continue;
                } else {
                    v___x_6590_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_6591_ =
                        l_Lean_Option_get___redArg(v___x_6536_, v_opts_6530_, v___x_6590_);
                    v___x_6592_ = (lean_unbox(v___x_6591_) as u8);
                    lean_dec(v___x_6591_);
                    if v___x_6592_ == 0 {
                        v___x_6593_ = l_Lean_KVMap_instValueNat;
                        v___x_6594_ = l_Lean_trace_profiler_threshold;
                        v___x_6595_ =
                            l_Lean_Option_get___redArg(v___x_6593_, v_opts_6530_, v___x_6594_);
                        v___x_6596_ = lean_float_of_nat(v___x_6595_);
                        v___x_6597_ = lean_float_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_trace_profiler_threshold_unitAdjusted___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once
                            ),
                            _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0,
                        );
                        v___x_6598_ = lean_float_div(v___x_6596_, v___x_6597_);
                        v___y_6583_ = v___x_6598_;
                        state = 8;
                        continue;
                    } else {
                        v___x_6599_ = l_Lean_KVMap_instValueNat;
                        v___x_6600_ = l_Lean_trace_profiler_threshold;
                        v___x_6601_ =
                            l_Lean_Option_get___redArg(v___x_6599_, v_opts_6530_, v___x_6600_);
                        v___x_6602_ = lean_float_of_nat(v___x_6601_);
                        v___y_6583_ = v___x_6602_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_toBind_6552_ = lean_ctor_get(v_inst_6521_, 1);
                lean_inc(v_toBind_6552_);
                v___x_6553_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(
                    v_inst_6521_,
                    v_inst_6522_,
                    v_inst_6523_,
                    v_inst_6524_,
                    v_oldTraces_6532_,
                    v_data_6551_,
                    v_ref_6533_,
                    v___y_6550_,
                );
                v___x_6554_ = lean_apply_4(
                    v_toBind_6552_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6553_,
                    v___f_6548_,
                );
                return v___x_6554_;
            }
            4 => {
                v_result_6558_ = lean_apply_1(v_inst_6526_, v_fst_6538_);
                v___x_6559_ = (lean_unbox(v_result_6558_) as u8);
                v___x_6560_ = l_Lean_TraceResult_toEmoji(v___x_6559_);
                v___x_6561_ = l_Lean_stringToMessageData(v___x_6560_);
                v___x_6562_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
                if v_isShared_6546_ == 0 {
                    lean_ctor_set_tag(v___x_6545_, 7);
                    lean_ctor_set(v___x_6545_, 1, v___x_6562_);
                    lean_ctor_set(v___x_6545_, 0, v___x_6561_);
                    v___x_6564_ = v___x_6545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6561_);
                    lean_ctor_set(v_reuseFailAlloc_6575_, 1, v___x_6562_);
                    v___x_6564_ = v_reuseFailAlloc_6575_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6541_ == 0 {
                    lean_ctor_set_tag(v___x_6540_, 7);
                    lean_ctor_set(v___x_6540_, 1, v_msg_6534_);
                    lean_ctor_set(v___x_6540_, 0, v___x_6564_);
                    v_msg_6566_ = v___x_6540_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6574_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6564_);
                    lean_ctor_set(v_reuseFailAlloc_6574_, 1, v_msg_6534_);
                    v_msg_6566_ = v_reuseFailAlloc_6574_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6567_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6567_, 0, v_result_6558_);
                v___x_6568_ = lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                lean_inc_ref(v_tag_6529_);
                lean_inc_ref(v___x_6567_);
                lean_inc(v_cls_6527_);
                v_data_6569_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_6569_, 0, v_cls_6527_);
                lean_ctor_set(v_data_6569_, 1, v___x_6567_);
                lean_ctor_set(v_data_6569_, 2, v_tag_6529_);
                lean_ctor_set_float(
                    v_data_6569_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6568_,
                );
                lean_ctor_set_float(
                    v_data_6569_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_6568_,
                );
                lean_ctor_set_uint8(
                    v_data_6569_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_6528_,
                );
                v___x_6570_ = (lean_unbox(v___x_6556_) as u8);
                lean_dec(v___x_6556_);
                if v___x_6570_ == 0 {
                    lean_dec_ref_known(v___x_6567_, 1);
                    lean_dec(v_snd_6543_);
                    lean_dec(v_fst_6542_);
                    lean_dec_ref(v_tag_6529_);
                    lean_dec(v_cls_6527_);
                    v___y_6550_ = v_msg_6566_;
                    v_data_6551_ = v_data_6569_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_6569_, 3);
                    v_data_6571_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_6571_, 0, v_cls_6527_);
                    lean_ctor_set(v_data_6571_, 1, v___x_6567_);
                    lean_ctor_set(v_data_6571_, 2, v_tag_6529_);
                    v___x_6572_ = lean_unbox_float(v_fst_6542_);
                    lean_dec(v_fst_6542_);
                    lean_ctor_set_float(
                        v_data_6571_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_6572_,
                    );
                    v___x_6573_ = lean_unbox_float(v_snd_6543_);
                    lean_dec(v_snd_6543_);
                    lean_ctor_set_float(
                        v_data_6571_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_6573_,
                    );
                    lean_ctor_set_uint8(
                        v_data_6571_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_6528_,
                    );
                    v___y_6550_ = v_msg_6566_;
                    v_data_6551_ = v_data_6571_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_clsEnabled_6531_ == 0 {
                    if v___y_6577_ == 0 {
                        lean_dec(v___x_6556_);
                        lean_del_object(v___x_6545_);
                        lean_dec(v_snd_6543_);
                        lean_dec(v_fst_6542_);
                        lean_del_object(v___x_6540_);
                        lean_dec(v_fst_6538_);
                        lean_dec_ref(v_msg_6534_);
                        lean_dec(v_ref_6533_);
                        lean_dec_ref(v_oldTraces_6532_);
                        lean_dec_ref(v_tag_6529_);
                        lean_dec(v_cls_6527_);
                        lean_dec_ref(v_inst_6526_);
                        lean_dec(v_inst_6524_);
                        lean_dec_ref(v_inst_6523_);
                        v_toBind_6578_ = lean_ctor_get(v_inst_6521_, 1);
                        lean_inc(v_toBind_6578_);
                        lean_dec_ref(v_inst_6521_);
                        v_modifyTraceState_6579_ = lean_ctor_get(v_inst_6522_, 0);
                        lean_inc(v_modifyTraceState_6579_);
                        lean_dec_ref(v_inst_6522_);
                        v___x_6580_ = lean_apply_1(v_modifyTraceState_6579_, v___f_6547_);
                        v___x_6581_ = lean_apply_4(
                            v_toBind_6578_,
                            lean_box(0),
                            lean_box(0),
                            v___x_6580_,
                            v___f_6548_,
                        );
                        return v___x_6581_;
                    } else {
                        lean_dec_ref(v___f_6547_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_6547_);
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_6584_ = lean_unbox_float(v_snd_6543_);
                v___x_6585_ = lean_unbox_float(v_fst_6542_);
                v___x_6586_ = lean_float_sub(v___x_6584_, v___x_6585_);
                v___x_6587_ = lean_float_decLt(v___y_6583_, v___x_6586_);
                v___y_6577_ = v___x_6587_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(
    mut v_inst_6605_: *mut LeanObject,
    mut v_inst_6606_: *mut LeanObject,
    mut v_inst_6607_: *mut LeanObject,
    mut v_inst_6608_: *mut LeanObject,
    mut v_always_6609_: *mut LeanObject,
    mut v_inst_6610_: *mut LeanObject,
    mut v_cls_6611_: *mut LeanObject,
    mut v_collapsed_6612_: *mut LeanObject,
    mut v_tag_6613_: *mut LeanObject,
    mut v_opts_6614_: *mut LeanObject,
    mut v_clsEnabled_6615_: *mut LeanObject,
    mut v_oldTraces_6616_: *mut LeanObject,
    mut v_ref_6617_: *mut LeanObject,
    mut v_msg_6618_: *mut LeanObject,
    mut v_resStartStop_6619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_6620_: u8 = 0;
    let mut v_clsEnabled_boxed_6621_: u8 = 0;
    let mut v_res_6622_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6620_ = (lean_unbox(v_collapsed_6612_) as u8);
    v_clsEnabled_boxed_6621_ = (lean_unbox(v_clsEnabled_6615_) as u8);
    v_res_6622_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(
        v_inst_6605_,
        v_inst_6606_,
        v_inst_6607_,
        v_inst_6608_,
        v_always_6609_,
        v_inst_6610_,
        v_cls_6611_,
        v_collapsed_boxed_6620_,
        v_tag_6613_,
        v_opts_6614_,
        v_clsEnabled_boxed_6621_,
        v_oldTraces_6616_,
        v_ref_6617_,
        v_msg_6618_,
        v_resStartStop_6619_,
    );
    lean_dec_ref(v_opts_6614_);
    return v_res_6622_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(
    mut v_00_u03b1_6623_: *mut LeanObject,
    mut v_m_6624_: *mut LeanObject,
    mut v_inst_6625_: *mut LeanObject,
    mut v_inst_6626_: *mut LeanObject,
    mut v_00_u03b5_6627_: *mut LeanObject,
    mut v_inst_6628_: *mut LeanObject,
    mut v_inst_6629_: *mut LeanObject,
    mut v_always_6630_: *mut LeanObject,
    mut v_inst_6631_: *mut LeanObject,
    mut v_cls_6632_: *mut LeanObject,
    mut v_collapsed_6633_: u8,
    mut v_tag_6634_: *mut LeanObject,
    mut v_opts_6635_: *mut LeanObject,
    mut v_clsEnabled_6636_: u8,
    mut v_oldTraces_6637_: *mut LeanObject,
    mut v_ref_6638_: *mut LeanObject,
    mut v_msg_6639_: *mut LeanObject,
    mut v_resStartStop_6640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    v___x_6641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(
        v_inst_6625_,
        v_inst_6626_,
        v_inst_6628_,
        v_inst_6629_,
        v_always_6630_,
        v_inst_6631_,
        v_cls_6632_,
        v_collapsed_6633_,
        v_tag_6634_,
        v_opts_6635_,
        v_clsEnabled_6636_,
        v_oldTraces_6637_,
        v_ref_6638_,
        v_msg_6639_,
        v_resStartStop_6640_,
    );
    return v___x_6641_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_6642_: *mut LeanObject = *_args.add(0);
    let mut v_m_6643_: *mut LeanObject = *_args.add(1);
    let mut v_inst_6644_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6645_: *mut LeanObject = *_args.add(3);
    let mut v_00_u03b5_6646_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6647_: *mut LeanObject = *_args.add(5);
    let mut v_inst_6648_: *mut LeanObject = *_args.add(6);
    let mut v_always_6649_: *mut LeanObject = *_args.add(7);
    let mut v_inst_6650_: *mut LeanObject = *_args.add(8);
    let mut v_cls_6651_: *mut LeanObject = *_args.add(9);
    let mut v_collapsed_6652_: *mut LeanObject = *_args.add(10);
    let mut v_tag_6653_: *mut LeanObject = *_args.add(11);
    let mut v_opts_6654_: *mut LeanObject = *_args.add(12);
    let mut v_clsEnabled_6655_: *mut LeanObject = *_args.add(13);
    let mut v_oldTraces_6656_: *mut LeanObject = *_args.add(14);
    let mut v_ref_6657_: *mut LeanObject = *_args.add(15);
    let mut v_msg_6658_: *mut LeanObject = *_args.add(16);
    let mut v_resStartStop_6659_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6660_: u8 = 0;
    let mut v_clsEnabled_boxed_6661_: u8 = 0;
    let mut v_res_6662_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6660_ = (lean_unbox(v_collapsed_6652_) as u8);
    v_clsEnabled_boxed_6661_ = (lean_unbox(v_clsEnabled_6655_) as u8);
    v_res_6662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(
        v_00_u03b1_6642_,
        v_m_6643_,
        v_inst_6644_,
        v_inst_6645_,
        v_00_u03b5_6646_,
        v_inst_6647_,
        v_inst_6648_,
        v_always_6649_,
        v_inst_6650_,
        v_cls_6651_,
        v_collapsed_boxed_6660_,
        v_tag_6653_,
        v_opts_6654_,
        v_clsEnabled_boxed_6661_,
        v_oldTraces_6656_,
        v_ref_6657_,
        v_msg_6658_,
        v_resStartStop_6659_,
    );
    lean_dec_ref(v_opts_6654_);
    return v_res_6662_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__0(
    mut v_inst_6663_: *mut LeanObject,
    mut v_____do__lift_6664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    v___x_6665_ = lean_apply_1(v_inst_6663_, v_____do__lift_6664_);
    return v___x_6665_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__1(
    mut v_inst_6666_: *mut LeanObject,
    mut v_inst_6667_: *mut LeanObject,
    mut v_inst_6668_: *mut LeanObject,
    mut v_inst_6669_: *mut LeanObject,
    mut v_always_6670_: *mut LeanObject,
    mut v_inst_6671_: *mut LeanObject,
    mut v_cls_6672_: *mut LeanObject,
    mut v_collapsed_6673_: u8,
    mut v_tag_6674_: *mut LeanObject,
    mut v_opts_6675_: *mut LeanObject,
    mut v_clsEnabled_6676_: u8,
    mut v_oldTraces_6677_: *mut LeanObject,
    mut v_ref_6678_: *mut LeanObject,
    mut v_msg_6679_: *mut LeanObject,
    mut v_resStartStop_6680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    v___x_6681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(
        v_inst_6666_,
        v_inst_6667_,
        v_inst_6668_,
        v_inst_6669_,
        v_always_6670_,
        v_inst_6671_,
        v_cls_6672_,
        v_collapsed_6673_,
        v_tag_6674_,
        v_opts_6675_,
        v_clsEnabled_6676_,
        v_oldTraces_6677_,
        v_ref_6678_,
        v_msg_6679_,
        v_resStartStop_6680_,
    );
    return v___x_6681_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(
    mut v_inst_6682_: *mut LeanObject,
    mut v_inst_6683_: *mut LeanObject,
    mut v_inst_6684_: *mut LeanObject,
    mut v_inst_6685_: *mut LeanObject,
    mut v_always_6686_: *mut LeanObject,
    mut v_inst_6687_: *mut LeanObject,
    mut v_cls_6688_: *mut LeanObject,
    mut v_collapsed_6689_: *mut LeanObject,
    mut v_tag_6690_: *mut LeanObject,
    mut v_opts_6691_: *mut LeanObject,
    mut v_clsEnabled_6692_: *mut LeanObject,
    mut v_oldTraces_6693_: *mut LeanObject,
    mut v_ref_6694_: *mut LeanObject,
    mut v_msg_6695_: *mut LeanObject,
    mut v_resStartStop_6696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_6697_: u8 = 0;
    let mut v_clsEnabled_boxed_6698_: u8 = 0;
    let mut v_res_6699_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6697_ = (lean_unbox(v_collapsed_6689_) as u8);
    v_clsEnabled_boxed_6698_ = (lean_unbox(v_clsEnabled_6692_) as u8);
    v_res_6699_ = l_Lean_withTraceNodeBefore___redArg___lam__1(
        v_inst_6682_,
        v_inst_6683_,
        v_inst_6684_,
        v_inst_6685_,
        v_always_6686_,
        v_inst_6687_,
        v_cls_6688_,
        v_collapsed_boxed_6697_,
        v_tag_6690_,
        v_opts_6691_,
        v_clsEnabled_boxed_6698_,
        v_oldTraces_6693_,
        v_ref_6694_,
        v_msg_6695_,
        v_resStartStop_6696_,
    );
    lean_dec_ref(v_opts_6691_);
    return v_res_6699_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__10(
    mut v_always_6700_: *mut LeanObject,
    mut v_inst_6701_: *mut LeanObject,
    mut v_inst_6702_: *mut LeanObject,
    mut v_inst_6703_: *mut LeanObject,
    mut v_inst_6704_: *mut LeanObject,
    mut v_inst_6705_: *mut LeanObject,
    mut v_cls_6706_: *mut LeanObject,
    mut v_collapsed_6707_: u8,
    mut v_tag_6708_: *mut LeanObject,
    mut v_opts_6709_: *mut LeanObject,
    mut v_clsEnabled_6710_: u8,
    mut v_oldTraces_6711_: *mut LeanObject,
    mut v_ref_6712_: *mut LeanObject,
    mut v_toPure_6713_: *mut LeanObject,
    mut v_toBind_6714_: *mut LeanObject,
    mut v_k_6715_: *mut LeanObject,
    mut v_inst_6716_: *mut LeanObject,
    mut v_msg_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: u8 = 0;
    v_tryCatch_6718_ = lean_ctor_get(v_always_6700_, 1);
    lean_inc(v_tryCatch_6718_);
    v___x_6719_ = lean_box((v_collapsed_6707_) as usize);
    v___x_6720_ = lean_box((v_clsEnabled_6710_) as usize);
    lean_inc_ref(v_opts_6709_);
    v___f_6721_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__1___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    lean_closure_set(v___f_6721_, 0, v_inst_6701_);
    lean_closure_set(v___f_6721_, 1, v_inst_6702_);
    lean_closure_set(v___f_6721_, 2, v_inst_6703_);
    lean_closure_set(v___f_6721_, 3, v_inst_6704_);
    lean_closure_set(v___f_6721_, 4, v_always_6700_);
    lean_closure_set(v___f_6721_, 5, v_inst_6705_);
    lean_closure_set(v___f_6721_, 6, v_cls_6706_);
    lean_closure_set(v___f_6721_, 7, v___x_6719_);
    lean_closure_set(v___f_6721_, 8, v_tag_6708_);
    lean_closure_set(v___f_6721_, 9, v_opts_6709_);
    lean_closure_set(v___f_6721_, 10, v___x_6720_);
    lean_closure_set(v___f_6721_, 11, v_oldTraces_6711_);
    lean_closure_set(v___f_6721_, 12, v_ref_6712_);
    lean_closure_set(v___f_6721_, 13, v_msg_6717_);
    lean_inc_n(v_toPure_6713_, 2);
    v___f_6722_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6722_, 0, v_toPure_6713_);
    v___f_6723_ = lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6723_, 0, v_toPure_6713_);
    lean_inc(v_toBind_6714_);
    v___x_6724_ = lean_apply_4(
        v_toBind_6714_,
        lean_box(0),
        lean_box(0),
        v_k_6715_,
        v___f_6723_,
    );
    v___x_6725_ = lean_apply_3(v_tryCatch_6718_, lean_box(0), v___x_6724_, v___f_6722_);
    v___x_6726_ = l_Lean_KVMap_instValueBool;
    v___x_6727_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_6728_ = l_Lean_Option_get___redArg(v___x_6726_, v_opts_6709_, v___x_6727_);
    lean_dec_ref(v_opts_6709_);
    v___x_6729_ = (lean_unbox(v___x_6728_) as u8);
    lean_dec(v___x_6728_);
    if v___x_6729_ == 0 {
        let mut v___x_6730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
        v___x_6730_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_6731_ = lean_apply_2(v_inst_6716_, lean_box(0), v___x_6730_);
        lean_inc(v___x_6731_);
        lean_inc_n(v_toBind_6714_, 2);
        v___f_6732_ = lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__5 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_6732_, 0, v_toPure_6713_);
        lean_closure_set(v___f_6732_, 1, v_toBind_6714_);
        lean_closure_set(v___f_6732_, 2, v___x_6731_);
        lean_closure_set(v___f_6732_, 3, v___x_6725_);
        v___x_6733_ = lean_apply_4(
            v_toBind_6714_,
            lean_box(0),
            lean_box(0),
            v___x_6731_,
            v___f_6732_,
        );
        v___x_6734_ = lean_apply_4(
            v_toBind_6714_,
            lean_box(0),
            lean_box(0),
            v___x_6733_,
            v___f_6721_,
        );
        return v___x_6734_;
    } else {
        let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
        v___x_6735_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_6736_ = lean_apply_2(v_inst_6716_, lean_box(0), v___x_6735_);
        lean_inc(v___x_6736_);
        lean_inc_n(v_toBind_6714_, 2);
        v___f_6737_ = lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__8 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_6737_, 0, v_toPure_6713_);
        lean_closure_set(v___f_6737_, 1, v_toBind_6714_);
        lean_closure_set(v___f_6737_, 2, v___x_6736_);
        lean_closure_set(v___f_6737_, 3, v___x_6725_);
        v___x_6738_ = lean_apply_4(
            v_toBind_6714_,
            lean_box(0),
            lean_box(0),
            v___x_6736_,
            v___f_6737_,
        );
        v___x_6739_ = lean_apply_4(
            v_toBind_6714_,
            lean_box(0),
            lean_box(0),
            v___x_6738_,
            v___f_6721_,
        );
        return v___x_6739_;
    }
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_always_6740_: *mut LeanObject = *_args.add(0);
    let mut v_inst_6741_: *mut LeanObject = *_args.add(1);
    let mut v_inst_6742_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6743_: *mut LeanObject = *_args.add(3);
    let mut v_inst_6744_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6745_: *mut LeanObject = *_args.add(5);
    let mut v_cls_6746_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_6747_: *mut LeanObject = *_args.add(7);
    let mut v_tag_6748_: *mut LeanObject = *_args.add(8);
    let mut v_opts_6749_: *mut LeanObject = *_args.add(9);
    let mut v_clsEnabled_6750_: *mut LeanObject = *_args.add(10);
    let mut v_oldTraces_6751_: *mut LeanObject = *_args.add(11);
    let mut v_ref_6752_: *mut LeanObject = *_args.add(12);
    let mut v_toPure_6753_: *mut LeanObject = *_args.add(13);
    let mut v_toBind_6754_: *mut LeanObject = *_args.add(14);
    let mut v_k_6755_: *mut LeanObject = *_args.add(15);
    let mut v_inst_6756_: *mut LeanObject = *_args.add(16);
    let mut v_msg_6757_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6758_: u8 = 0;
    let mut v_clsEnabled_boxed_6759_: u8 = 0;
    let mut v_res_6760_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6758_ = (lean_unbox(v_collapsed_6747_) as u8);
    v_clsEnabled_boxed_6759_ = (lean_unbox(v_clsEnabled_6750_) as u8);
    v_res_6760_ = l_Lean_withTraceNodeBefore___redArg___lam__10(
        v_always_6740_,
        v_inst_6741_,
        v_inst_6742_,
        v_inst_6743_,
        v_inst_6744_,
        v_inst_6745_,
        v_cls_6746_,
        v_collapsed_boxed_6758_,
        v_tag_6748_,
        v_opts_6749_,
        v_clsEnabled_boxed_6759_,
        v_oldTraces_6751_,
        v_ref_6752_,
        v_toPure_6753_,
        v_toBind_6754_,
        v_k_6755_,
        v_inst_6756_,
        v_msg_6757_,
    );
    return v_res_6760_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__3(
    mut v_always_6761_: *mut LeanObject,
    mut v_inst_6762_: *mut LeanObject,
    mut v_inst_6763_: *mut LeanObject,
    mut v_inst_6764_: *mut LeanObject,
    mut v_inst_6765_: *mut LeanObject,
    mut v_inst_6766_: *mut LeanObject,
    mut v_cls_6767_: *mut LeanObject,
    mut v_collapsed_6768_: u8,
    mut v_tag_6769_: *mut LeanObject,
    mut v_opts_6770_: *mut LeanObject,
    mut v_clsEnabled_6771_: u8,
    mut v_oldTraces_6772_: *mut LeanObject,
    mut v_toPure_6773_: *mut LeanObject,
    mut v_toBind_6774_: *mut LeanObject,
    mut v_k_6775_: *mut LeanObject,
    mut v_inst_6776_: *mut LeanObject,
    mut v_msg_6777_: *mut LeanObject,
    mut v___f_6778_: *mut LeanObject,
    mut v_withRef_6779_: *mut LeanObject,
    mut v_getRef_6780_: *mut LeanObject,
    mut v_ref_6781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    v___x_6782_ = lean_box((v_collapsed_6768_) as usize);
    v___x_6783_ = lean_box((v_clsEnabled_6771_) as usize);
    lean_inc_n(v_toBind_6774_, 3);
    lean_inc(v_ref_6781_);
    v___f_6784_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__10___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    lean_closure_set(v___f_6784_, 0, v_always_6761_);
    lean_closure_set(v___f_6784_, 1, v_inst_6762_);
    lean_closure_set(v___f_6784_, 2, v_inst_6763_);
    lean_closure_set(v___f_6784_, 3, v_inst_6764_);
    lean_closure_set(v___f_6784_, 4, v_inst_6765_);
    lean_closure_set(v___f_6784_, 5, v_inst_6766_);
    lean_closure_set(v___f_6784_, 6, v_cls_6767_);
    lean_closure_set(v___f_6784_, 7, v___x_6782_);
    lean_closure_set(v___f_6784_, 8, v_tag_6769_);
    lean_closure_set(v___f_6784_, 9, v_opts_6770_);
    lean_closure_set(v___f_6784_, 10, v___x_6783_);
    lean_closure_set(v___f_6784_, 11, v_oldTraces_6772_);
    lean_closure_set(v___f_6784_, 12, v_ref_6781_);
    lean_closure_set(v___f_6784_, 13, v_toPure_6773_);
    lean_closure_set(v___f_6784_, 14, v_toBind_6774_);
    lean_closure_set(v___f_6784_, 15, v_k_6775_);
    lean_closure_set(v___f_6784_, 16, v_inst_6776_);
    v___x_6785_ = lean_box(0);
    v___x_6786_ = lean_apply_1(v_msg_6777_, v___x_6785_);
    v___x_6787_ = lean_apply_4(
        v_toBind_6774_,
        lean_box(0),
        lean_box(0),
        v___x_6786_,
        v___f_6778_,
    );
    v___f_6788_ = lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6788_, 0, v_ref_6781_);
    lean_closure_set(v___f_6788_, 1, v_withRef_6779_);
    lean_closure_set(v___f_6788_, 2, v___x_6787_);
    v___x_6789_ = lean_apply_4(
        v_toBind_6774_,
        lean_box(0),
        lean_box(0),
        v_getRef_6780_,
        v___f_6788_,
    );
    v___x_6790_ = lean_apply_4(
        v_toBind_6774_,
        lean_box(0),
        lean_box(0),
        v___x_6789_,
        v___f_6784_,
    );
    return v___x_6790_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_always_6791_: *mut LeanObject = *_args.add(0);
    let mut v_inst_6792_: *mut LeanObject = *_args.add(1);
    let mut v_inst_6793_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6794_: *mut LeanObject = *_args.add(3);
    let mut v_inst_6795_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6796_: *mut LeanObject = *_args.add(5);
    let mut v_cls_6797_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_6798_: *mut LeanObject = *_args.add(7);
    let mut v_tag_6799_: *mut LeanObject = *_args.add(8);
    let mut v_opts_6800_: *mut LeanObject = *_args.add(9);
    let mut v_clsEnabled_6801_: *mut LeanObject = *_args.add(10);
    let mut v_oldTraces_6802_: *mut LeanObject = *_args.add(11);
    let mut v_toPure_6803_: *mut LeanObject = *_args.add(12);
    let mut v_toBind_6804_: *mut LeanObject = *_args.add(13);
    let mut v_k_6805_: *mut LeanObject = *_args.add(14);
    let mut v_inst_6806_: *mut LeanObject = *_args.add(15);
    let mut v_msg_6807_: *mut LeanObject = *_args.add(16);
    let mut v___f_6808_: *mut LeanObject = *_args.add(17);
    let mut v_withRef_6809_: *mut LeanObject = *_args.add(18);
    let mut v_getRef_6810_: *mut LeanObject = *_args.add(19);
    let mut v_ref_6811_: *mut LeanObject = *_args.add(20);
    let mut v_collapsed_boxed_6812_: u8 = 0;
    let mut v_clsEnabled_boxed_6813_: u8 = 0;
    let mut v_res_6814_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6812_ = (lean_unbox(v_collapsed_6798_) as u8);
    v_clsEnabled_boxed_6813_ = (lean_unbox(v_clsEnabled_6801_) as u8);
    v_res_6814_ = l_Lean_withTraceNodeBefore___redArg___lam__3(
        v_always_6791_,
        v_inst_6792_,
        v_inst_6793_,
        v_inst_6794_,
        v_inst_6795_,
        v_inst_6796_,
        v_cls_6797_,
        v_collapsed_boxed_6812_,
        v_tag_6799_,
        v_opts_6800_,
        v_clsEnabled_boxed_6813_,
        v_oldTraces_6802_,
        v_toPure_6803_,
        v_toBind_6804_,
        v_k_6805_,
        v_inst_6806_,
        v_msg_6807_,
        v___f_6808_,
        v_withRef_6809_,
        v_getRef_6810_,
        v_ref_6811_,
    );
    return v_res_6814_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__2(
    mut v_inst_6815_: *mut LeanObject,
    mut v_always_6816_: *mut LeanObject,
    mut v_inst_6817_: *mut LeanObject,
    mut v_inst_6818_: *mut LeanObject,
    mut v_inst_6819_: *mut LeanObject,
    mut v_inst_6820_: *mut LeanObject,
    mut v_cls_6821_: *mut LeanObject,
    mut v_collapsed_6822_: u8,
    mut v_tag_6823_: *mut LeanObject,
    mut v_opts_6824_: *mut LeanObject,
    mut v_clsEnabled_6825_: u8,
    mut v_toPure_6826_: *mut LeanObject,
    mut v_toBind_6827_: *mut LeanObject,
    mut v_k_6828_: *mut LeanObject,
    mut v_inst_6829_: *mut LeanObject,
    mut v_msg_6830_: *mut LeanObject,
    mut v___f_6831_: *mut LeanObject,
    mut v_oldTraces_6832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    v_getRef_6833_ = lean_ctor_get(v_inst_6815_, 0);
    lean_inc_n(v_getRef_6833_, 2);
    v_withRef_6834_ = lean_ctor_get(v_inst_6815_, 1);
    lean_inc(v_withRef_6834_);
    v___x_6835_ = lean_box((v_collapsed_6822_) as usize);
    v___x_6836_ = lean_box((v_clsEnabled_6825_) as usize);
    lean_inc(v_toBind_6827_);
    v___f_6837_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__3___boxed as *mut core::ffi::c_void,
        21,
        20,
    );
    lean_closure_set(v___f_6837_, 0, v_always_6816_);
    lean_closure_set(v___f_6837_, 1, v_inst_6817_);
    lean_closure_set(v___f_6837_, 2, v_inst_6818_);
    lean_closure_set(v___f_6837_, 3, v_inst_6815_);
    lean_closure_set(v___f_6837_, 4, v_inst_6819_);
    lean_closure_set(v___f_6837_, 5, v_inst_6820_);
    lean_closure_set(v___f_6837_, 6, v_cls_6821_);
    lean_closure_set(v___f_6837_, 7, v___x_6835_);
    lean_closure_set(v___f_6837_, 8, v_tag_6823_);
    lean_closure_set(v___f_6837_, 9, v_opts_6824_);
    lean_closure_set(v___f_6837_, 10, v___x_6836_);
    lean_closure_set(v___f_6837_, 11, v_oldTraces_6832_);
    lean_closure_set(v___f_6837_, 12, v_toPure_6826_);
    lean_closure_set(v___f_6837_, 13, v_toBind_6827_);
    lean_closure_set(v___f_6837_, 14, v_k_6828_);
    lean_closure_set(v___f_6837_, 15, v_inst_6829_);
    lean_closure_set(v___f_6837_, 16, v_msg_6830_);
    lean_closure_set(v___f_6837_, 17, v___f_6831_);
    lean_closure_set(v___f_6837_, 18, v_withRef_6834_);
    lean_closure_set(v___f_6837_, 19, v_getRef_6833_);
    v___x_6838_ = lean_apply_4(
        v_toBind_6827_,
        lean_box(0),
        lean_box(0),
        v_getRef_6833_,
        v___f_6837_,
    );
    return v___x_6838_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_6839_: *mut LeanObject = *_args.add(0);
    let mut v_always_6840_: *mut LeanObject = *_args.add(1);
    let mut v_inst_6841_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6842_: *mut LeanObject = *_args.add(3);
    let mut v_inst_6843_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6844_: *mut LeanObject = *_args.add(5);
    let mut v_cls_6845_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_6846_: *mut LeanObject = *_args.add(7);
    let mut v_tag_6847_: *mut LeanObject = *_args.add(8);
    let mut v_opts_6848_: *mut LeanObject = *_args.add(9);
    let mut v_clsEnabled_6849_: *mut LeanObject = *_args.add(10);
    let mut v_toPure_6850_: *mut LeanObject = *_args.add(11);
    let mut v_toBind_6851_: *mut LeanObject = *_args.add(12);
    let mut v_k_6852_: *mut LeanObject = *_args.add(13);
    let mut v_inst_6853_: *mut LeanObject = *_args.add(14);
    let mut v_msg_6854_: *mut LeanObject = *_args.add(15);
    let mut v___f_6855_: *mut LeanObject = *_args.add(16);
    let mut v_oldTraces_6856_: *mut LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6857_: u8 = 0;
    let mut v_clsEnabled_boxed_6858_: u8 = 0;
    let mut v_res_6859_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6857_ = (lean_unbox(v_collapsed_6846_) as u8);
    v_clsEnabled_boxed_6858_ = (lean_unbox(v_clsEnabled_6849_) as u8);
    v_res_6859_ = l_Lean_withTraceNodeBefore___redArg___lam__2(
        v_inst_6839_,
        v_always_6840_,
        v_inst_6841_,
        v_inst_6842_,
        v_inst_6843_,
        v_inst_6844_,
        v_cls_6845_,
        v_collapsed_boxed_6857_,
        v_tag_6847_,
        v_opts_6848_,
        v_clsEnabled_boxed_6858_,
        v_toPure_6850_,
        v_toBind_6851_,
        v_k_6852_,
        v_inst_6853_,
        v_msg_6854_,
        v___f_6855_,
        v_oldTraces_6856_,
    );
    return v_res_6859_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__4(
    mut v_inst_6860_: *mut LeanObject,
    mut v_always_6861_: *mut LeanObject,
    mut v_inst_6862_: *mut LeanObject,
    mut v_inst_6863_: *mut LeanObject,
    mut v_inst_6864_: *mut LeanObject,
    mut v_inst_6865_: *mut LeanObject,
    mut v_cls_6866_: *mut LeanObject,
    mut v_collapsed_6867_: u8,
    mut v_tag_6868_: *mut LeanObject,
    mut v_opts_6869_: *mut LeanObject,
    mut v_toPure_6870_: *mut LeanObject,
    mut v_toBind_6871_: *mut LeanObject,
    mut v_k_6872_: *mut LeanObject,
    mut v_inst_6873_: *mut LeanObject,
    mut v_msg_6874_: *mut LeanObject,
    mut v___f_6875_: *mut LeanObject,
    mut v_clsEnabled_6876_: u8,
) -> *mut LeanObject {
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6877_ = lean_box((v_collapsed_6867_) as usize);
                v___x_6878_ = lean_box((v_clsEnabled_6876_) as usize);
                lean_inc(v_k_6872_);
                lean_inc(v_toBind_6871_);
                lean_inc_ref(v_opts_6869_);
                lean_inc_ref(v_inst_6863_);
                lean_inc_ref(v_inst_6862_);
                v___f_6879_ = lean_alloc_closure(
                    l_Lean_withTraceNodeBefore___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    18,
                    17,
                );
                lean_closure_set(v___f_6879_, 0, v_inst_6860_);
                lean_closure_set(v___f_6879_, 1, v_always_6861_);
                lean_closure_set(v___f_6879_, 2, v_inst_6862_);
                lean_closure_set(v___f_6879_, 3, v_inst_6863_);
                lean_closure_set(v___f_6879_, 4, v_inst_6864_);
                lean_closure_set(v___f_6879_, 5, v_inst_6865_);
                lean_closure_set(v___f_6879_, 6, v_cls_6866_);
                lean_closure_set(v___f_6879_, 7, v___x_6877_);
                lean_closure_set(v___f_6879_, 8, v_tag_6868_);
                lean_closure_set(v___f_6879_, 9, v_opts_6869_);
                lean_closure_set(v___f_6879_, 10, v___x_6878_);
                lean_closure_set(v___f_6879_, 11, v_toPure_6870_);
                lean_closure_set(v___f_6879_, 12, v_toBind_6871_);
                lean_closure_set(v___f_6879_, 13, v_k_6872_);
                lean_closure_set(v___f_6879_, 14, v_inst_6873_);
                lean_closure_set(v___f_6879_, 15, v_msg_6874_);
                lean_closure_set(v___f_6879_, 16, v___f_6875_);
                if v_clsEnabled_6876_ == 0 {
                    v___x_6883_ = l_Lean_KVMap_instValueBool;
                    v___x_6884_ = l_Lean_trace_profiler;
                    v___x_6885_ =
                        l_Lean_Option_get___redArg(v___x_6883_, v_opts_6869_, v___x_6884_);
                    lean_dec_ref(v_opts_6869_);
                    v___x_6886_ = (lean_unbox(v___x_6885_) as u8);
                    lean_dec(v___x_6885_);
                    if v___x_6886_ == 0 {
                        lean_dec_ref(v___f_6879_);
                        lean_dec(v_toBind_6871_);
                        lean_dec_ref(v_inst_6863_);
                        lean_dec_ref(v_inst_6862_);
                        return v_k_6872_;
                    } else {
                        lean_dec(v_k_6872_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_6872_);
                    lean_dec_ref(v_opts_6869_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6881_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_6862_,
                    v_inst_6863_,
                );
                v___x_6882_ = lean_apply_4(
                    v_toBind_6871_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6881_,
                    v___f_6879_,
                );
                return v___x_6882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_6887_: *mut LeanObject = *_args.add(0);
    let mut v_always_6888_: *mut LeanObject = *_args.add(1);
    let mut v_inst_6889_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6890_: *mut LeanObject = *_args.add(3);
    let mut v_inst_6891_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6892_: *mut LeanObject = *_args.add(5);
    let mut v_cls_6893_: *mut LeanObject = *_args.add(6);
    let mut v_collapsed_6894_: *mut LeanObject = *_args.add(7);
    let mut v_tag_6895_: *mut LeanObject = *_args.add(8);
    let mut v_opts_6896_: *mut LeanObject = *_args.add(9);
    let mut v_toPure_6897_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_6898_: *mut LeanObject = *_args.add(11);
    let mut v_k_6899_: *mut LeanObject = *_args.add(12);
    let mut v_inst_6900_: *mut LeanObject = *_args.add(13);
    let mut v_msg_6901_: *mut LeanObject = *_args.add(14);
    let mut v___f_6902_: *mut LeanObject = *_args.add(15);
    let mut v_clsEnabled_6903_: *mut LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_6904_: u8 = 0;
    let mut v_clsEnabled_boxed_6905_: u8 = 0;
    let mut v_res_6906_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6904_ = (lean_unbox(v_collapsed_6894_) as u8);
    v_clsEnabled_boxed_6905_ = (lean_unbox(v_clsEnabled_6903_) as u8);
    v_res_6906_ = l_Lean_withTraceNodeBefore___redArg___lam__4(
        v_inst_6887_,
        v_always_6888_,
        v_inst_6889_,
        v_inst_6890_,
        v_inst_6891_,
        v_inst_6892_,
        v_cls_6893_,
        v_collapsed_boxed_6904_,
        v_tag_6895_,
        v_opts_6896_,
        v_toPure_6897_,
        v_toBind_6898_,
        v_k_6899_,
        v_inst_6900_,
        v_msg_6901_,
        v___f_6902_,
        v_clsEnabled_boxed_6905_,
    );
    return v_res_6906_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__7(
    mut v_k_6907_: *mut LeanObject,
    mut v_inst_6908_: *mut LeanObject,
    mut v_toApplicative_6909_: *mut LeanObject,
    mut v_inst_6910_: *mut LeanObject,
    mut v_always_6911_: *mut LeanObject,
    mut v_inst_6912_: *mut LeanObject,
    mut v_inst_6913_: *mut LeanObject,
    mut v_inst_6914_: *mut LeanObject,
    mut v_cls_6915_: *mut LeanObject,
    mut v_collapsed_6916_: u8,
    mut v_tag_6917_: *mut LeanObject,
    mut v_toBind_6918_: *mut LeanObject,
    mut v_inst_6919_: *mut LeanObject,
    mut v_msg_6920_: *mut LeanObject,
    mut v___f_6921_: *mut LeanObject,
    mut v_inst_6922_: *mut LeanObject,
    mut v_opts_6923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_6924_: u8 = 0;
    v_hasTrace_6924_ = lean_ctor_get_uint8(
        v_opts_6923_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_6924_ == 0 {
        lean_dec_ref(v_opts_6923_);
        lean_dec(v_inst_6922_);
        lean_dec(v___f_6921_);
        lean_dec(v_msg_6920_);
        lean_dec(v_inst_6919_);
        lean_dec(v_toBind_6918_);
        lean_dec_ref(v_tag_6917_);
        lean_dec(v_cls_6915_);
        lean_dec_ref(v_inst_6914_);
        lean_dec(v_inst_6913_);
        lean_dec_ref(v_inst_6912_);
        lean_dec_ref(v_always_6911_);
        lean_dec_ref(v_inst_6910_);
        lean_dec_ref(v_toApplicative_6909_);
        lean_dec_ref(v_inst_6908_);
        return v_k_6907_;
    } else {
        let mut v_getInheritedTraceOptions_6925_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_6925_ = lean_ctor_get(v_inst_6908_, 2);
        lean_inc(v_getInheritedTraceOptions_6925_);
        v_toPure_6926_ = lean_ctor_get(v_toApplicative_6909_, 1);
        lean_inc_n(v_toPure_6926_, 2);
        lean_dec_ref(v_toApplicative_6909_);
        v___x_6927_ = lean_box((v_collapsed_6916_) as usize);
        lean_inc_n(v_toBind_6918_, 3);
        lean_inc(v_cls_6915_);
        v___f_6928_ = lean_alloc_closure(
            l_Lean_withTraceNodeBefore___redArg___lam__4___boxed as *mut core::ffi::c_void,
            17,
            16,
        );
        lean_closure_set(v___f_6928_, 0, v_inst_6910_);
        lean_closure_set(v___f_6928_, 1, v_always_6911_);
        lean_closure_set(v___f_6928_, 2, v_inst_6912_);
        lean_closure_set(v___f_6928_, 3, v_inst_6908_);
        lean_closure_set(v___f_6928_, 4, v_inst_6913_);
        lean_closure_set(v___f_6928_, 5, v_inst_6914_);
        lean_closure_set(v___f_6928_, 6, v_cls_6915_);
        lean_closure_set(v___f_6928_, 7, v___x_6927_);
        lean_closure_set(v___f_6928_, 8, v_tag_6917_);
        lean_closure_set(v___f_6928_, 9, v_opts_6923_);
        lean_closure_set(v___f_6928_, 10, v_toPure_6926_);
        lean_closure_set(v___f_6928_, 11, v_toBind_6918_);
        lean_closure_set(v___f_6928_, 12, v_k_6907_);
        lean_closure_set(v___f_6928_, 13, v_inst_6919_);
        lean_closure_set(v___f_6928_, 14, v_msg_6920_);
        lean_closure_set(v___f_6928_, 15, v___f_6921_);
        v___f_6929_ = lean_alloc_closure(
            l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_6929_, 0, v_toPure_6926_);
        lean_closure_set(v___f_6929_, 1, v_cls_6915_);
        lean_closure_set(v___f_6929_, 2, v_toBind_6918_);
        lean_closure_set(v___f_6929_, 3, v_inst_6922_);
        v___x_6930_ = lean_apply_4(
            v_toBind_6918_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_6925_,
            v___f_6929_,
        );
        v___x_6931_ = lean_apply_4(
            v_toBind_6918_,
            lean_box(0),
            lean_box(0),
            v___x_6930_,
            v___f_6928_,
        );
        return v___x_6931_;
    }
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6932_: *mut LeanObject = *_args.add(0);
    let mut v_inst_6933_: *mut LeanObject = *_args.add(1);
    let mut v_toApplicative_6934_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6935_: *mut LeanObject = *_args.add(3);
    let mut v_always_6936_: *mut LeanObject = *_args.add(4);
    let mut v_inst_6937_: *mut LeanObject = *_args.add(5);
    let mut v_inst_6938_: *mut LeanObject = *_args.add(6);
    let mut v_inst_6939_: *mut LeanObject = *_args.add(7);
    let mut v_cls_6940_: *mut LeanObject = *_args.add(8);
    let mut v_collapsed_6941_: *mut LeanObject = *_args.add(9);
    let mut v_tag_6942_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_6943_: *mut LeanObject = *_args.add(11);
    let mut v_inst_6944_: *mut LeanObject = *_args.add(12);
    let mut v_msg_6945_: *mut LeanObject = *_args.add(13);
    let mut v___f_6946_: *mut LeanObject = *_args.add(14);
    let mut v_inst_6947_: *mut LeanObject = *_args.add(15);
    let mut v_opts_6948_: *mut LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_6949_: u8 = 0;
    let mut v_res_6950_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6949_ = (lean_unbox(v_collapsed_6941_) as u8);
    v_res_6950_ = l_Lean_withTraceNodeBefore___redArg___lam__7(
        v_k_6932_,
        v_inst_6933_,
        v_toApplicative_6934_,
        v_inst_6935_,
        v_always_6936_,
        v_inst_6937_,
        v_inst_6938_,
        v_inst_6939_,
        v_cls_6940_,
        v_collapsed_boxed_6949_,
        v_tag_6942_,
        v_toBind_6943_,
        v_inst_6944_,
        v_msg_6945_,
        v___f_6946_,
        v_inst_6947_,
        v_opts_6948_,
    );
    return v_res_6950_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg(
    mut v_inst_6951_: *mut LeanObject,
    mut v_inst_6952_: *mut LeanObject,
    mut v_inst_6953_: *mut LeanObject,
    mut v_inst_6954_: *mut LeanObject,
    mut v_inst_6955_: *mut LeanObject,
    mut v_always_6956_: *mut LeanObject,
    mut v_inst_6957_: *mut LeanObject,
    mut v_inst_6958_: *mut LeanObject,
    mut v_cls_6959_: *mut LeanObject,
    mut v_msg_6960_: *mut LeanObject,
    mut v_k_6961_: *mut LeanObject,
    mut v_collapsed_6962_: u8,
    mut v_tag_6963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6964_ = lean_ctor_get(v_inst_6951_, 0);
    lean_inc_ref(v_toApplicative_6964_);
    v_toBind_6965_ = lean_ctor_get(v_inst_6951_, 1);
    lean_inc_n(v_toBind_6965_, 2);
    lean_inc(v_inst_6954_);
    v___f_6966_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6966_, 0, v_inst_6954_);
    v___x_6967_ = lean_box((v_collapsed_6962_) as usize);
    lean_inc(v_inst_6955_);
    v___f_6968_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    lean_closure_set(v___f_6968_, 0, v_k_6961_);
    lean_closure_set(v___f_6968_, 1, v_inst_6952_);
    lean_closure_set(v___f_6968_, 2, v_toApplicative_6964_);
    lean_closure_set(v___f_6968_, 3, v_inst_6953_);
    lean_closure_set(v___f_6968_, 4, v_always_6956_);
    lean_closure_set(v___f_6968_, 5, v_inst_6951_);
    lean_closure_set(v___f_6968_, 6, v_inst_6954_);
    lean_closure_set(v___f_6968_, 7, v_inst_6958_);
    lean_closure_set(v___f_6968_, 8, v_cls_6959_);
    lean_closure_set(v___f_6968_, 9, v___x_6967_);
    lean_closure_set(v___f_6968_, 10, v_tag_6963_);
    lean_closure_set(v___f_6968_, 11, v_toBind_6965_);
    lean_closure_set(v___f_6968_, 12, v_inst_6957_);
    lean_closure_set(v___f_6968_, 13, v_msg_6960_);
    lean_closure_set(v___f_6968_, 14, v___f_6966_);
    lean_closure_set(v___f_6968_, 15, v_inst_6955_);
    v___x_6969_ = lean_apply_4(
        v_toBind_6965_,
        lean_box(0),
        lean_box(0),
        v_inst_6955_,
        v___f_6968_,
    );
    return v___x_6969_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___boxed(
    mut v_inst_6970_: *mut LeanObject,
    mut v_inst_6971_: *mut LeanObject,
    mut v_inst_6972_: *mut LeanObject,
    mut v_inst_6973_: *mut LeanObject,
    mut v_inst_6974_: *mut LeanObject,
    mut v_always_6975_: *mut LeanObject,
    mut v_inst_6976_: *mut LeanObject,
    mut v_inst_6977_: *mut LeanObject,
    mut v_cls_6978_: *mut LeanObject,
    mut v_msg_6979_: *mut LeanObject,
    mut v_k_6980_: *mut LeanObject,
    mut v_collapsed_6981_: *mut LeanObject,
    mut v_tag_6982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_6983_: u8 = 0;
    let mut v_res_6984_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6983_ = (lean_unbox(v_collapsed_6981_) as u8);
    v_res_6984_ = l_Lean_withTraceNodeBefore___redArg(
        v_inst_6970_,
        v_inst_6971_,
        v_inst_6972_,
        v_inst_6973_,
        v_inst_6974_,
        v_always_6975_,
        v_inst_6976_,
        v_inst_6977_,
        v_cls_6978_,
        v_msg_6979_,
        v_k_6980_,
        v_collapsed_boxed_6983_,
        v_tag_6982_,
    );
    return v_res_6984_;
}
pub unsafe fn l_Lean_withTraceNodeBefore(
    mut v_00_u03b1_6985_: *mut LeanObject,
    mut v_m_6986_: *mut LeanObject,
    mut v_inst_6987_: *mut LeanObject,
    mut v_inst_6988_: *mut LeanObject,
    mut v_00_u03b5_6989_: *mut LeanObject,
    mut v_inst_6990_: *mut LeanObject,
    mut v_inst_6991_: *mut LeanObject,
    mut v_inst_6992_: *mut LeanObject,
    mut v_always_6993_: *mut LeanObject,
    mut v_inst_6994_: *mut LeanObject,
    mut v_inst_6995_: *mut LeanObject,
    mut v_cls_6996_: *mut LeanObject,
    mut v_msg_6997_: *mut LeanObject,
    mut v_k_6998_: *mut LeanObject,
    mut v_collapsed_6999_: u8,
    mut v_tag_7000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7001_ = lean_ctor_get(v_inst_6987_, 0);
    lean_inc_ref(v_toApplicative_7001_);
    v_toBind_7002_ = lean_ctor_get(v_inst_6987_, 1);
    lean_inc_n(v_toBind_7002_, 2);
    lean_inc(v_inst_6991_);
    v___f_7003_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7003_, 0, v_inst_6991_);
    v___x_7004_ = lean_box((v_collapsed_6999_) as usize);
    lean_inc(v_inst_6992_);
    v___f_7005_ = lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    lean_closure_set(v___f_7005_, 0, v_k_6998_);
    lean_closure_set(v___f_7005_, 1, v_inst_6988_);
    lean_closure_set(v___f_7005_, 2, v_toApplicative_7001_);
    lean_closure_set(v___f_7005_, 3, v_inst_6990_);
    lean_closure_set(v___f_7005_, 4, v_always_6993_);
    lean_closure_set(v___f_7005_, 5, v_inst_6987_);
    lean_closure_set(v___f_7005_, 6, v_inst_6991_);
    lean_closure_set(v___f_7005_, 7, v_inst_6995_);
    lean_closure_set(v___f_7005_, 8, v_cls_6996_);
    lean_closure_set(v___f_7005_, 9, v___x_7004_);
    lean_closure_set(v___f_7005_, 10, v_tag_7000_);
    lean_closure_set(v___f_7005_, 11, v_toBind_7002_);
    lean_closure_set(v___f_7005_, 12, v_inst_6994_);
    lean_closure_set(v___f_7005_, 13, v_msg_6997_);
    lean_closure_set(v___f_7005_, 14, v___f_7003_);
    lean_closure_set(v___f_7005_, 15, v_inst_6992_);
    v___x_7006_ = lean_apply_4(
        v_toBind_7002_,
        lean_box(0),
        lean_box(0),
        v_inst_6992_,
        v___f_7005_,
    );
    return v___x_7006_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___boxed(
    mut v_00_u03b1_7007_: *mut LeanObject,
    mut v_m_7008_: *mut LeanObject,
    mut v_inst_7009_: *mut LeanObject,
    mut v_inst_7010_: *mut LeanObject,
    mut v_00_u03b5_7011_: *mut LeanObject,
    mut v_inst_7012_: *mut LeanObject,
    mut v_inst_7013_: *mut LeanObject,
    mut v_inst_7014_: *mut LeanObject,
    mut v_always_7015_: *mut LeanObject,
    mut v_inst_7016_: *mut LeanObject,
    mut v_inst_7017_: *mut LeanObject,
    mut v_cls_7018_: *mut LeanObject,
    mut v_msg_7019_: *mut LeanObject,
    mut v_k_7020_: *mut LeanObject,
    mut v_collapsed_7021_: *mut LeanObject,
    mut v_tag_7022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_7023_: u8 = 0;
    let mut v_res_7024_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_7023_ = (lean_unbox(v_collapsed_7021_) as u8);
    v_res_7024_ = l_Lean_withTraceNodeBefore(
        v_00_u03b1_7007_,
        v_m_7008_,
        v_inst_7009_,
        v_inst_7010_,
        v_00_u03b5_7011_,
        v_inst_7012_,
        v_inst_7013_,
        v_inst_7014_,
        v_always_7015_,
        v_inst_7016_,
        v_inst_7017_,
        v_cls_7018_,
        v_msg_7019_,
        v_k_7020_,
        v_collapsed_boxed_7023_,
        v_tag_7022_,
    );
    return v_res_7024_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__0(
    mut v_toApplicative_7025_: *mut LeanObject,
    mut v_____s_7026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_7027_ = lean_ctor_get(v_toApplicative_7025_, 1);
    lean_inc(v_toPure_7027_);
    lean_dec_ref(v_toApplicative_7025_);
    v___x_7028_ = lean_box(0);
    v___x_7029_ = lean_apply_2(v_toPure_7027_, lean_box(0), v___x_7028_);
    return v___x_7029_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__1(
    mut v_x_7030_: *mut LeanObject,
    mut v_x_7031_: *mut LeanObject,
) -> u8 {
    let mut v_fst_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: u8 = 0;
    v_fst_7032_ = lean_ctor_get(v_x_7030_, 0);
    v_fst_7033_ = lean_ctor_get(v_x_7031_, 0);
    v_fst_7034_ = lean_ctor_get(v_fst_7032_, 0);
    v_fst_7035_ = lean_ctor_get(v_fst_7033_, 0);
    v___x_7036_ = lean_nat_dec_lt(v_fst_7034_, v_fst_7035_);
    return v___x_7036_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__1___boxed(
    mut v_x_7037_: *mut LeanObject,
    mut v_x_7038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7039_: u8 = 0;
    let mut v_r_7040_: *mut LeanObject = core::ptr::null_mut();
    v_res_7039_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_7037_, v_x_7038_);
    lean_dec_ref(v_x_7038_);
    lean_dec_ref(v_x_7037_);
    v_r_7040_ = lean_box((v_res_7039_) as usize);
    return v_r_7040_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__2(
    mut v_x1_7041_: *mut LeanObject,
    mut v_x2_7042_: *mut LeanObject,
    mut v_x3_7043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    v___x_7044_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7044_, 0, v_x2_7042_);
    lean_ctor_set(v___x_7044_, 1, v_x3_7043_);
    v___x_7045_ = lean_array_push(v_x1_7041_, v___x_7044_);
    return v___x_7045_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__3(
    mut v_toApplicative_7046_: *mut LeanObject,
    mut v___x_7047_: *mut LeanObject,
    mut v_r_7048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_7049_ = lean_ctor_get(v_toApplicative_7046_, 1);
    lean_inc(v_toPure_7049_);
    lean_dec_ref(v_toApplicative_7046_);
    v___x_7050_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7050_, 0, v___x_7047_);
    v___x_7051_ = lean_apply_2(v_toPure_7049_, lean_box(0), v___x_7050_);
    return v___x_7051_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__4(
    mut v_____do__lift_7052_: *mut LeanObject,
    mut v___x_7053_: *mut LeanObject,
    mut v_fst_7054_: *mut LeanObject,
    mut v_snd_7055_: *mut LeanObject,
    mut v_logMessage_7056_: *mut LeanObject,
    mut v_toBind_7057_: *mut LeanObject,
    mut v___f_7058_: *mut LeanObject,
    mut v_____do__lift_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    v___x_7060_ = 0;
    v___x_7061_ = l_Lean_Elab_mkMessageCore(
        v_____do__lift_7052_,
        v_____do__lift_7059_,
        v___x_7053_,
        v___x_7060_,
        v_fst_7054_,
        v_snd_7055_,
    );
    v___x_7062_ = lean_apply_1(v_logMessage_7056_, v___x_7061_);
    v___x_7063_ = lean_apply_4(
        v_toBind_7057_,
        lean_box(0),
        lean_box(0),
        v___x_7062_,
        v___f_7058_,
    );
    return v___x_7063_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__4___boxed(
    mut v_____do__lift_7064_: *mut LeanObject,
    mut v___x_7065_: *mut LeanObject,
    mut v_fst_7066_: *mut LeanObject,
    mut v_snd_7067_: *mut LeanObject,
    mut v_logMessage_7068_: *mut LeanObject,
    mut v_toBind_7069_: *mut LeanObject,
    mut v___f_7070_: *mut LeanObject,
    mut v_____do__lift_7071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7072_: *mut LeanObject = core::ptr::null_mut();
    v_res_7072_ = l_Lean_addTraceAsMessages___redArg___lam__4(
        v_____do__lift_7064_,
        v___x_7065_,
        v_fst_7066_,
        v_snd_7067_,
        v_logMessage_7068_,
        v_toBind_7069_,
        v___f_7070_,
        v_____do__lift_7071_,
    );
    lean_dec(v_snd_7067_);
    lean_dec(v_fst_7066_);
    return v_res_7072_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__5(
    mut v___x_7073_: *mut LeanObject,
    mut v_fst_7074_: *mut LeanObject,
    mut v_snd_7075_: *mut LeanObject,
    mut v_logMessage_7076_: *mut LeanObject,
    mut v_toBind_7077_: *mut LeanObject,
    mut v___f_7078_: *mut LeanObject,
    mut v_toMonadFileMap_7079_: *mut LeanObject,
    mut v_____do__lift_7080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_7077_);
    v___f_7081_ = lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_7081_, 0, v_____do__lift_7080_);
    lean_closure_set(v___f_7081_, 1, v___x_7073_);
    lean_closure_set(v___f_7081_, 2, v_fst_7074_);
    lean_closure_set(v___f_7081_, 3, v_snd_7075_);
    lean_closure_set(v___f_7081_, 4, v_logMessage_7076_);
    lean_closure_set(v___f_7081_, 5, v_toBind_7077_);
    lean_closure_set(v___f_7081_, 6, v___f_7078_);
    v___x_7082_ = lean_apply_4(
        v_toBind_7077_,
        lean_box(0),
        lean_box(0),
        v_toMonadFileMap_7079_,
        v___f_7081_,
    );
    return v___x_7082_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__6(
    mut v___x_7083_: *mut LeanObject,
    mut v___x_7084_: u8,
    mut v_inst_7085_: *mut LeanObject,
    mut v_toBind_7086_: *mut LeanObject,
    mut v___f_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
    mut v_x_7089_: *mut LeanObject,
    mut v___y_7090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7097_: u8 = 0;
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: f64 = 0.0;
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getFileName_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_logMessage_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7091_ = lean_ctor_get(v_a_7088_, 0);
                lean_inc(v_fst_7091_);
                v_snd_7092_ = lean_ctor_get(v_a_7088_, 1);
                lean_inc(v_snd_7092_);
                lean_dec_ref(v_a_7088_);
                v_fst_7093_ = lean_ctor_get(v_fst_7091_, 0);
                v_snd_7094_ = lean_ctor_get(v_fst_7091_, 1);
                v_isSharedCheck_7114_ = (!lean_is_exclusive(v_fst_7091_)) as u8;
                if v_isSharedCheck_7114_ == 0 {
                    v___x_7096_ = v_fst_7091_;
                    v_isShared_7097_ = v_isSharedCheck_7114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_7094_);
                    lean_inc(v_fst_7093_);
                    lean_dec(v_fst_7091_);
                    v___x_7096_ = lean_box(0);
                    v_isShared_7097_ = v_isSharedCheck_7114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7098_ = lean_box(0);
                v___x_7099_ = lean_box(0);
                v___x_7100_ = lean_float_of_nat(v___x_7083_);
                v___x_7101_ = l_Lean_addTrace___redArg___lam__0___closed__1;
                v___x_7102_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_7102_, 0, v___x_7098_);
                lean_ctor_set(v___x_7102_, 1, v___x_7099_);
                lean_ctor_set(v___x_7102_, 2, v___x_7101_);
                lean_ctor_set_float(
                    v___x_7102_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_7100_,
                );
                lean_ctor_set_float(
                    v___x_7102_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_7100_,
                );
                lean_ctor_set_uint8(
                    v___x_7102_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_7084_,
                );
                v_toMonadFileMap_7103_ = lean_ctor_get(v_inst_7085_, 0);
                lean_inc(v_toMonadFileMap_7103_);
                v_getFileName_7104_ = lean_ctor_get(v_inst_7085_, 2);
                lean_inc(v_getFileName_7104_);
                v_logMessage_7105_ = lean_ctor_get(v_inst_7085_, 4);
                lean_inc(v_logMessage_7105_);
                lean_dec_ref(v_inst_7085_);
                v___x_7106_ = l_Lean_checkTraceOption___closed__1;
                v___x_7107_ = l_Lean_MessageData_nil;
                v___x_7108_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_7108_, 0, v___x_7102_);
                lean_ctor_set(v___x_7108_, 1, v___x_7107_);
                lean_ctor_set(v___x_7108_, 2, v_snd_7092_);
                if v_isShared_7097_ == 0 {
                    lean_ctor_set_tag(v___x_7096_, 8);
                    lean_ctor_set(v___x_7096_, 1, v___x_7108_);
                    lean_ctor_set(v___x_7096_, 0, v___x_7106_);
                    v___x_7110_ = v___x_7096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7113_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7113_, 0, v___x_7106_);
                    lean_ctor_set(v_reuseFailAlloc_7113_, 1, v___x_7108_);
                    v___x_7110_ = v_reuseFailAlloc_7113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toBind_7086_);
                v___f_7111_ = lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__5 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_7111_, 0, v___x_7110_);
                lean_closure_set(v___f_7111_, 1, v_fst_7093_);
                lean_closure_set(v___f_7111_, 2, v_snd_7094_);
                lean_closure_set(v___f_7111_, 3, v_logMessage_7105_);
                lean_closure_set(v___f_7111_, 4, v_toBind_7086_);
                lean_closure_set(v___f_7111_, 5, v___f_7087_);
                lean_closure_set(v___f_7111_, 6, v_toMonadFileMap_7103_);
                v___x_7112_ = lean_apply_4(
                    v_toBind_7086_,
                    lean_box(0),
                    lean_box(0),
                    v_getFileName_7104_,
                    v___f_7111_,
                );
                return v___x_7112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__6___boxed(
    mut v___x_7115_: *mut LeanObject,
    mut v___x_7116_: *mut LeanObject,
    mut v_inst_7117_: *mut LeanObject,
    mut v_toBind_7118_: *mut LeanObject,
    mut v___f_7119_: *mut LeanObject,
    mut v_a_7120_: *mut LeanObject,
    mut v_x_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1730__boxed_7123_: u8 = 0;
    let mut v_res_7124_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730__boxed_7123_ = (lean_unbox(v___x_7116_) as u8);
    v_res_7124_ = l_Lean_addTraceAsMessages___redArg___lam__6(
        v___x_7115_,
        v___x_1730__boxed_7123_,
        v_inst_7117_,
        v_toBind_7118_,
        v___f_7119_,
        v_a_7120_,
        v_x_7121_,
        v___y_7122_,
    );
    return v_res_7124_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__7(
    mut v___x_7125_: *mut LeanObject,
    mut v___f_7126_: *mut LeanObject,
    mut v_acc_7127_: *mut LeanObject,
    mut v_l_7128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    v___x_7129_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_7125_,
        v___f_7126_,
        v_acc_7127_,
        v_l_7128_,
    );
    return v___x_7129_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__8(
    mut v_toApplicative_7130_: *mut LeanObject,
    mut v___x_7131_: u8,
    mut v_inst_7132_: *mut LeanObject,
    mut v_toBind_7133_: *mut LeanObject,
    mut v_inst_7134_: *mut LeanObject,
    mut v___f_7135_: *mut LeanObject,
    mut v___f_7136_: *mut LeanObject,
    mut v___f_7137_: *mut LeanObject,
    mut v_____s_7138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7146_: usize = 0;
    let mut v___x_7147_: usize = 0;
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: u8 = 0;
    let mut v___y_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: u8 = 0;
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    let mut v_size_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: u8 = 0;
    let mut v___f_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: u8 = 0;
    let mut v___x_7181_: usize = 0;
    let mut v___x_7182_: usize = 0;
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: usize = 0;
    let mut v___x_7185_: usize = 0;
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7172_ = lean_ctor_get(v_____s_7138_, 0);
                lean_inc(v_size_7172_);
                v_buckets_7173_ = lean_ctor_get(v_____s_7138_, 1);
                lean_inc_ref(v_buckets_7173_);
                lean_dec_ref(v_____s_7138_);
                v___x_7174_ = lean_mk_empty_array_with_capacity(v_size_7172_);
                lean_dec(v_size_7172_);
                v___x_7175_ =
                    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9;
                v___x_7176_ = lean_unsigned_to_nat(0);
                v___x_7177_ = lean_array_get_size(v_buckets_7173_);
                v___x_7178_ = lean_nat_dec_lt(v___x_7176_, v___x_7177_);
                if v___x_7178_ == 0 {
                    lean_dec_ref(v_buckets_7173_);
                    lean_dec_ref(v___f_7137_);
                    v___y_7165_ = v___x_7174_;
                    state = 4;
                    continue;
                } else {
                    v___f_7179_ = lean_alloc_closure(
                        l_Lean_addTraceAsMessages___redArg___lam__7 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_7179_, 0, v___x_7175_);
                    lean_closure_set(v___f_7179_, 1, v___f_7137_);
                    v___x_7180_ = lean_nat_dec_le(v___x_7177_, v___x_7177_);
                    if v___x_7180_ == 0 {
                        if v___x_7178_ == 0 {
                            lean_dec_ref(v___f_7179_);
                            lean_dec_ref(v_buckets_7173_);
                            v___y_7165_ = v___x_7174_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7181_ = 0usize;
                            v___x_7182_ = lean_usize_of_nat(v___x_7177_);
                            v___x_7183_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_7175_,
                                    v___f_7179_,
                                    v_buckets_7173_,
                                    v___x_7181_,
                                    v___x_7182_,
                                    v___x_7174_,
                                );
                            v___y_7165_ = v___x_7183_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_7184_ = 0usize;
                        v___x_7185_ = lean_usize_of_nat(v___x_7177_);
                        v___x_7186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_7175_,
                            v___f_7179_,
                            v_buckets_7173_,
                            v___x_7184_,
                            v___x_7185_,
                            v___x_7174_,
                        );
                        v___y_7165_ = v___x_7186_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7142_ = lean_box(0);
                v___f_7143_ = lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__3 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_7143_, 0, v_toApplicative_7130_);
                lean_closure_set(v___f_7143_, 1, v___x_7142_);
                v___x_7144_ = lean_box((v___x_7131_) as usize);
                lean_inc(v_toBind_7133_);
                v___f_7145_ = lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    8,
                    5,
                );
                lean_closure_set(v___f_7145_, 0, v___y_7140_);
                lean_closure_set(v___f_7145_, 1, v___x_7144_);
                lean_closure_set(v___f_7145_, 2, v_inst_7132_);
                lean_closure_set(v___f_7145_, 3, v_toBind_7133_);
                lean_closure_set(v___f_7145_, 4, v___f_7143_);
                v_sz_7146_ = lean_array_size(v___y_7141_);
                v___x_7147_ = 0usize;
                v___x_7148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_7134_,
                    v___y_7141_,
                    v___f_7145_,
                    v_sz_7146_,
                    v___x_7147_,
                    v___x_7142_,
                );
                v___x_7149_ = lean_apply_4(
                    v_toBind_7133_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7148_,
                    v___f_7135_,
                );
                return v___x_7149_;
            }
            2 => {
                v___x_7156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    lean_box(0),
                    v___f_7136_,
                    v___y_7154_,
                    v___y_7152_,
                    v___y_7153_,
                    v___y_7155_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                lean_dec(v___y_7155_);
                lean_dec(v___y_7154_);
                v___y_7140_ = v___y_7151_;
                v___y_7141_ = v___x_7156_;
                state = 1;
                continue;
            }
            3 => {
                v___x_7163_ = lean_nat_dec_le(v___y_7162_, v___y_7160_);
                if v___x_7163_ == 0 {
                    lean_dec(v___y_7160_);
                    lean_inc(v___y_7162_);
                    v___y_7151_ = v___y_7158_;
                    v___y_7152_ = v___y_7159_;
                    v___y_7153_ = v___y_7162_;
                    v___y_7154_ = v___y_7161_;
                    v___y_7155_ = v___y_7162_;
                    state = 2;
                    continue;
                } else {
                    v___y_7151_ = v___y_7158_;
                    v___y_7152_ = v___y_7159_;
                    v___y_7153_ = v___y_7162_;
                    v___y_7154_ = v___y_7161_;
                    v___y_7155_ = v___y_7160_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_7166_ = lean_unsigned_to_nat(0);
                v___x_7167_ = lean_array_get_size(v___y_7165_);
                v___x_7168_ = lean_nat_dec_eq(v___x_7167_, v___x_7166_);
                if v___x_7168_ == 0 {
                    v___x_7169_ = lean_unsigned_to_nat(1);
                    v___x_7170_ = lean_nat_sub(v___x_7167_, v___x_7169_);
                    v___x_7171_ = lean_nat_dec_le(v___x_7166_, v___x_7170_);
                    if v___x_7171_ == 0 {
                        lean_inc(v___x_7170_);
                        v___y_7158_ = v___x_7166_;
                        v___y_7159_ = v___y_7165_;
                        v___y_7160_ = v___x_7170_;
                        v___y_7161_ = v___x_7167_;
                        v___y_7162_ = v___x_7170_;
                        state = 3;
                        continue;
                    } else {
                        v___y_7158_ = v___x_7166_;
                        v___y_7159_ = v___y_7165_;
                        v___y_7160_ = v___x_7170_;
                        v___y_7161_ = v___x_7167_;
                        v___y_7162_ = v___x_7166_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_7136_);
                    v___y_7140_ = v___x_7166_;
                    v___y_7141_ = v___y_7165_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__8___boxed(
    mut v_toApplicative_7187_: *mut LeanObject,
    mut v___x_7188_: *mut LeanObject,
    mut v_inst_7189_: *mut LeanObject,
    mut v_toBind_7190_: *mut LeanObject,
    mut v_inst_7191_: *mut LeanObject,
    mut v___f_7192_: *mut LeanObject,
    mut v___f_7193_: *mut LeanObject,
    mut v___f_7194_: *mut LeanObject,
    mut v_____s_7195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818__boxed_7196_: u8 = 0;
    let mut v_res_7197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818__boxed_7196_ = (lean_unbox(v___x_7188_) as u8);
    v_res_7197_ = l_Lean_addTraceAsMessages___redArg___lam__8(
        v_toApplicative_7187_,
        v___x_1818__boxed_7196_,
        v_inst_7189_,
        v_toBind_7190_,
        v_inst_7191_,
        v___f_7192_,
        v___f_7193_,
        v___f_7194_,
        v_____s_7195_,
    );
    return v_res_7197_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__9(
    mut v_traceElem_7198_: *mut LeanObject,
    mut v_toApplicative_7199_: *mut LeanObject,
    mut v___f_7200_: *mut LeanObject,
    mut v___f_7201_: *mut LeanObject,
    mut v_____s_7202_: *mut LeanObject,
    mut v___x_7203_: u8,
    mut v_____do__lift_7204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7209_: u8 = 0;
    let mut v___y_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7205_ = lean_ctor_get(v_traceElem_7198_, 0);
                v_msg_7206_ = lean_ctor_get(v_traceElem_7198_, 1);
                v_isSharedCheck_7231_ = (!lean_is_exclusive(v_traceElem_7198_)) as u8;
                if v_isSharedCheck_7231_ == 0 {
                    v___x_7208_ = v_traceElem_7198_;
                    v_isShared_7209_ = v_isSharedCheck_7231_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_msg_7206_);
                    lean_inc(v_ref_7205_);
                    lean_dec(v_traceElem_7198_);
                    v___x_7208_ = lean_box(0);
                    v_isShared_7209_ = v_isSharedCheck_7231_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_7223_ = l_Lean_replaceRef(v_ref_7205_, v_____do__lift_7204_);
                lean_dec(v_ref_7205_);
                v___x_7228_ = l_Lean_Syntax_getPos_x3f(v_ref_7223_, v___x_7203_);
                if lean_obj_tag(v___x_7228_) == 0 {
                    v___x_7229_ = lean_unsigned_to_nat(0);
                    v___y_7225_ = v___x_7229_;
                    state = 4;
                    continue;
                } else {
                    v_val_7230_ = lean_ctor_get(v___x_7228_, 0);
                    lean_inc(v_val_7230_);
                    lean_dec_ref_known(v___x_7228_, 1);
                    v___y_7225_ = v_val_7230_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v_toPure_7213_ = lean_ctor_get(v_toApplicative_7199_, 1);
                lean_inc(v_toPure_7213_);
                lean_dec_ref(v_toApplicative_7199_);
                if v_isShared_7209_ == 0 {
                    lean_ctor_set(v___x_7208_, 1, v___y_7212_);
                    lean_ctor_set(v___x_7208_, 0, v___y_7211_);
                    v___x_7215_ = v___x_7208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7222_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7222_, 0, v___y_7211_);
                    lean_ctor_set(v_reuseFailAlloc_7222_, 1, v___y_7212_);
                    v___x_7215_ = v_reuseFailAlloc_7222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7216_ = l_Lean_addTrace___redArg___lam__0___closed__2;
                lean_inc_ref(v___x_7215_);
                lean_inc_ref(v___f_7201_);
                lean_inc_ref(v___f_7200_);
                v___x_7217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
                    v___f_7200_,
                    v___f_7201_,
                    v_____s_7202_,
                    v___x_7215_,
                    v___x_7216_,
                );
                v___x_7218_ = lean_array_push(v___x_7217_, v_msg_7206_);
                v_pos2traces_7219_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___f_7200_,
                    v___f_7201_,
                    v_____s_7202_,
                    v___x_7215_,
                    v___x_7218_,
                );
                v___x_7220_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7220_, 0, v_pos2traces_7219_);
                v___x_7221_ = lean_apply_2(v_toPure_7213_, lean_box(0), v___x_7220_);
                return v___x_7221_;
            }
            4 => {
                v___x_7226_ = l_Lean_Syntax_getTailPos_x3f(v_ref_7223_, v___x_7203_);
                lean_dec(v_ref_7223_);
                if lean_obj_tag(v___x_7226_) == 0 {
                    lean_inc(v___y_7225_);
                    v___y_7211_ = v___y_7225_;
                    v___y_7212_ = v___y_7225_;
                    state = 2;
                    continue;
                } else {
                    v_val_7227_ = lean_ctor_get(v___x_7226_, 0);
                    lean_inc(v_val_7227_);
                    lean_dec_ref_known(v___x_7226_, 1);
                    v___y_7211_ = v___y_7225_;
                    v___y_7212_ = v_val_7227_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__9___boxed(
    mut v_traceElem_7232_: *mut LeanObject,
    mut v_toApplicative_7233_: *mut LeanObject,
    mut v___f_7234_: *mut LeanObject,
    mut v___f_7235_: *mut LeanObject,
    mut v_____s_7236_: *mut LeanObject,
    mut v___x_7237_: *mut LeanObject,
    mut v_____do__lift_7238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1943__boxed_7239_: u8 = 0;
    let mut v_res_7240_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943__boxed_7239_ = (lean_unbox(v___x_7237_) as u8);
    v_res_7240_ = l_Lean_addTraceAsMessages___redArg___lam__9(
        v_traceElem_7232_,
        v_toApplicative_7233_,
        v___f_7234_,
        v___f_7235_,
        v_____s_7236_,
        v___x_1943__boxed_7239_,
        v_____do__lift_7238_,
    );
    lean_dec(v_____do__lift_7238_);
    return v_res_7240_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__10(
    mut v_inst_7241_: *mut LeanObject,
    mut v_toApplicative_7242_: *mut LeanObject,
    mut v___f_7243_: *mut LeanObject,
    mut v___f_7244_: *mut LeanObject,
    mut v___x_7245_: u8,
    mut v_toBind_7246_: *mut LeanObject,
    mut v_traceElem_7247_: *mut LeanObject,
    mut v_____s_7248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
    v_getRef_7249_ = lean_ctor_get(v_inst_7241_, 0);
    lean_inc(v_getRef_7249_);
    lean_dec_ref(v_inst_7241_);
    v___x_7250_ = lean_box((v___x_7245_) as usize);
    v___f_7251_ = lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__9___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_7251_, 0, v_traceElem_7247_);
    lean_closure_set(v___f_7251_, 1, v_toApplicative_7242_);
    lean_closure_set(v___f_7251_, 2, v___f_7243_);
    lean_closure_set(v___f_7251_, 3, v___f_7244_);
    lean_closure_set(v___f_7251_, 4, v_____s_7248_);
    lean_closure_set(v___f_7251_, 5, v___x_7250_);
    v___x_7252_ = lean_apply_4(
        v_toBind_7246_,
        lean_box(0),
        lean_box(0),
        v_getRef_7249_,
        v___f_7251_,
    );
    return v___x_7252_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__10___boxed(
    mut v_inst_7253_: *mut LeanObject,
    mut v_toApplicative_7254_: *mut LeanObject,
    mut v___f_7255_: *mut LeanObject,
    mut v___f_7256_: *mut LeanObject,
    mut v___x_7257_: *mut LeanObject,
    mut v_toBind_7258_: *mut LeanObject,
    mut v_traceElem_7259_: *mut LeanObject,
    mut v_____s_7260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2003__boxed_7261_: u8 = 0;
    let mut v_res_7262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2003__boxed_7261_ = (lean_unbox(v___x_7257_) as u8);
    v_res_7262_ = l_Lean_addTraceAsMessages___redArg___lam__10(
        v_inst_7253_,
        v_toApplicative_7254_,
        v___f_7255_,
        v___f_7256_,
        v___x_2003__boxed_7261_,
        v_toBind_7258_,
        v_traceElem_7259_,
        v_____s_7260_,
    );
    return v_res_7262_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0() -> *mut LeanObject {
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7264_: *mut LeanObject = core::ptr::null_mut();
    v___x_7263_ = lean_alloc_closure(l_instDecidableEqRaw___boxed as *mut core::ffi::c_void, 2, 0);
    v___f_7264_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7264_, 0, v___x_7263_);
    return v___f_7264_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1() -> *mut LeanObject {
    let mut v___f_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7266_: *mut LeanObject = core::ptr::null_mut();
    v___f_7265_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__0),
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once),
        _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0,
    );
    v___f_7266_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7266_, 0, v___f_7265_);
    lean_closure_set(v___f_7266_, 1, v___f_7265_);
    return v___f_7266_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4() -> *mut LeanObject {
    let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    v___x_7270_ = lean_box(0);
    v___x_7271_ = lean_unsigned_to_nat(16);
    v___x_7272_ = lean_mk_array(v___x_7271_, v___x_7270_);
    return v___x_7272_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5() -> *mut LeanObject {
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_7275_: *mut LeanObject = core::ptr::null_mut();
    v___x_7273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__4),
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once),
        _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4,
    );
    v___x_7274_ = lean_unsigned_to_nat(0);
    v_pos2traces_7275_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_pos2traces_7275_, 0, v___x_7274_);
    lean_ctor_set(v_pos2traces_7275_, 1, v___x_7273_);
    return v_pos2traces_7275_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__11(
    mut v_inst_7276_: *mut LeanObject,
    mut v_toApplicative_7277_: *mut LeanObject,
    mut v_toBind_7278_: *mut LeanObject,
    mut v_inst_7279_: *mut LeanObject,
    mut v___f_7280_: *mut LeanObject,
    mut v_traces_7281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7282_: u8 = 0;
    v___x_7282_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_7281_);
    if v___x_7282_ == 0 {
        let mut v___f_7283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7286_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pos2traces_7287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
        v___f_7283_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__1),
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once),
            _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1,
        );
        v___f_7284_ = l_Lean_addTraceAsMessages___redArg___lam__11___closed__3;
        v___x_7285_ = lean_box((v___x_7282_) as usize);
        lean_inc(v_toBind_7278_);
        v___f_7286_ = lean_alloc_closure(
            l_Lean_addTraceAsMessages___redArg___lam__10___boxed as *mut core::ffi::c_void,
            8,
            6,
        );
        lean_closure_set(v___f_7286_, 0, v_inst_7276_);
        lean_closure_set(v___f_7286_, 1, v_toApplicative_7277_);
        lean_closure_set(v___f_7286_, 2, v___f_7283_);
        lean_closure_set(v___f_7286_, 3, v___f_7284_);
        lean_closure_set(v___f_7286_, 4, v___x_7285_);
        lean_closure_set(v___f_7286_, 5, v_toBind_7278_);
        v_pos2traces_7287_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__5),
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once),
            _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5,
        );
        v___x_7288_ = l_Lean_PersistentArray_forIn___redArg(
            v_inst_7279_,
            v_traces_7281_,
            v_pos2traces_7287_,
            v___f_7286_,
        );
        v___x_7289_ = lean_apply_4(
            v_toBind_7278_,
            lean_box(0),
            lean_box(0),
            v___x_7288_,
            v___f_7280_,
        );
        return v___x_7289_;
    } else {
        let mut v_toPure_7290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_7280_);
        lean_dec_ref(v_inst_7279_);
        lean_dec(v_toBind_7278_);
        lean_dec_ref(v_inst_7276_);
        v_toPure_7290_ = lean_ctor_get(v_toApplicative_7277_, 1);
        lean_inc(v_toPure_7290_);
        lean_dec_ref(v_toApplicative_7277_);
        v___x_7291_ = lean_box(0);
        v___x_7292_ = lean_apply_2(v_toPure_7290_, lean_box(0), v___x_7291_);
        return v___x_7292_;
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__11___boxed(
    mut v_inst_7293_: *mut LeanObject,
    mut v_toApplicative_7294_: *mut LeanObject,
    mut v_toBind_7295_: *mut LeanObject,
    mut v_inst_7296_: *mut LeanObject,
    mut v___f_7297_: *mut LeanObject,
    mut v_traces_7298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7299_: *mut LeanObject = core::ptr::null_mut();
    v_res_7299_ = l_Lean_addTraceAsMessages___redArg___lam__11(
        v_inst_7293_,
        v_toApplicative_7294_,
        v_toBind_7295_,
        v_inst_7296_,
        v___f_7297_,
        v_traces_7298_,
    );
    lean_dec_ref(v_traces_7298_);
    return v_res_7299_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__12(
    mut v_toApplicative_7300_: *mut LeanObject,
    mut v_inst_7301_: *mut LeanObject,
    mut v_toBind_7302_: *mut LeanObject,
    mut v_inst_7303_: *mut LeanObject,
    mut v___f_7304_: *mut LeanObject,
    mut v___f_7305_: *mut LeanObject,
    mut v___f_7306_: *mut LeanObject,
    mut v_inst_7307_: *mut LeanObject,
    mut v_inst_7308_: *mut LeanObject,
    mut v_____do__lift_7309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: u8 = 0;
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7314_ = l_Lean_KVMap_instValueBool;
                v___x_7315_ = l_Lean_KVMap_instValueString;
                v___x_7316_ = l_Lean_trace_profiler_output;
                v___x_7317_ =
                    l_Lean_Option_get_x3f___redArg(v___x_7315_, v_____do__lift_7309_, v___x_7316_);
                if lean_obj_tag(v___x_7317_) == 0 {
                    v___x_7318_ = l_Lean_trace_profiler_serve;
                    v___x_7319_ =
                        l_Lean_Option_get___redArg(v___x_7314_, v_____do__lift_7309_, v___x_7318_);
                    v___x_7320_ = (lean_unbox(v___x_7319_) as u8);
                    lean_dec(v___x_7319_);
                    if v___x_7320_ == 0 {
                        v___x_7321_ = 1;
                        v___x_7322_ = lean_box((v___x_7321_) as usize);
                        lean_inc_ref_n(v_inst_7303_, 2);
                        lean_inc_n(v_toBind_7302_, 2);
                        lean_inc_ref(v_toApplicative_7300_);
                        v___f_7323_ = lean_alloc_closure(
                            l_Lean_addTraceAsMessages___redArg___lam__8___boxed
                                as *mut core::ffi::c_void,
                            9,
                            8,
                        );
                        lean_closure_set(v___f_7323_, 0, v_toApplicative_7300_);
                        lean_closure_set(v___f_7323_, 1, v___x_7322_);
                        lean_closure_set(v___f_7323_, 2, v_inst_7301_);
                        lean_closure_set(v___f_7323_, 3, v_toBind_7302_);
                        lean_closure_set(v___f_7323_, 4, v_inst_7303_);
                        lean_closure_set(v___f_7323_, 5, v___f_7304_);
                        lean_closure_set(v___f_7323_, 6, v___f_7305_);
                        lean_closure_set(v___f_7323_, 7, v___f_7306_);
                        v___f_7324_ = lean_alloc_closure(
                            l_Lean_addTraceAsMessages___redArg___lam__11___boxed
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        lean_closure_set(v___f_7324_, 0, v_inst_7307_);
                        lean_closure_set(v___f_7324_, 1, v_toApplicative_7300_);
                        lean_closure_set(v___f_7324_, 2, v_toBind_7302_);
                        lean_closure_set(v___f_7324_, 3, v_inst_7303_);
                        lean_closure_set(v___f_7324_, 4, v___f_7323_);
                        v___x_7325_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                            v_inst_7303_,
                            v_inst_7308_,
                        );
                        v___x_7326_ = lean_apply_4(
                            v_toBind_7302_,
                            lean_box(0),
                            lean_box(0),
                            v___x_7325_,
                            v___f_7324_,
                        );
                        return v___x_7326_;
                    } else {
                        lean_dec_ref(v_inst_7308_);
                        lean_dec_ref(v_inst_7307_);
                        lean_dec_ref(v___f_7306_);
                        lean_dec_ref(v___f_7305_);
                        lean_dec(v___f_7304_);
                        lean_dec_ref(v_inst_7303_);
                        lean_dec(v_toBind_7302_);
                        lean_dec_ref(v_inst_7301_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_7317_, 1);
                    lean_dec_ref(v_inst_7308_);
                    lean_dec_ref(v_inst_7307_);
                    lean_dec_ref(v___f_7306_);
                    lean_dec_ref(v___f_7305_);
                    lean_dec(v___f_7304_);
                    lean_dec_ref(v_inst_7303_);
                    lean_dec(v_toBind_7302_);
                    lean_dec_ref(v_inst_7301_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_7311_ = lean_ctor_get(v_toApplicative_7300_, 1);
                lean_inc(v_toPure_7311_);
                lean_dec_ref(v_toApplicative_7300_);
                v___x_7312_ = lean_box(0);
                v___x_7313_ = lean_apply_2(v_toPure_7311_, lean_box(0), v___x_7312_);
                return v___x_7313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__12___boxed(
    mut v_toApplicative_7327_: *mut LeanObject,
    mut v_inst_7328_: *mut LeanObject,
    mut v_toBind_7329_: *mut LeanObject,
    mut v_inst_7330_: *mut LeanObject,
    mut v___f_7331_: *mut LeanObject,
    mut v___f_7332_: *mut LeanObject,
    mut v___f_7333_: *mut LeanObject,
    mut v_inst_7334_: *mut LeanObject,
    mut v_inst_7335_: *mut LeanObject,
    mut v_____do__lift_7336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7337_: *mut LeanObject = core::ptr::null_mut();
    v_res_7337_ = l_Lean_addTraceAsMessages___redArg___lam__12(
        v_toApplicative_7327_,
        v_inst_7328_,
        v_toBind_7329_,
        v_inst_7330_,
        v___f_7331_,
        v___f_7332_,
        v___f_7333_,
        v_inst_7334_,
        v_inst_7335_,
        v_____do__lift_7336_,
    );
    lean_dec_ref(v_____do__lift_7336_);
    return v_res_7337_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg(
    mut v_inst_7340_: *mut LeanObject,
    mut v_inst_7341_: *mut LeanObject,
    mut v_inst_7342_: *mut LeanObject,
    mut v_inst_7343_: *mut LeanObject,
    mut v_inst_7344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7345_ = lean_ctor_get(v_inst_7341_, 0);
    lean_inc_ref_n(v_toApplicative_7345_, 2);
    v_toBind_7346_ = lean_ctor_get(v_inst_7341_, 1);
    lean_inc_n(v_toBind_7346_, 2);
    v___f_7347_ = lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7347_, 0, v_toApplicative_7345_);
    v___f_7348_ = l_Lean_addTraceAsMessages___redArg___closed__0;
    v___f_7349_ = l_Lean_addTraceAsMessages___redArg___closed__1;
    v___f_7350_ = lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__12___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_7350_, 0, v_toApplicative_7345_);
    lean_closure_set(v___f_7350_, 1, v_inst_7343_);
    lean_closure_set(v___f_7350_, 2, v_toBind_7346_);
    lean_closure_set(v___f_7350_, 3, v_inst_7341_);
    lean_closure_set(v___f_7350_, 4, v___f_7347_);
    lean_closure_set(v___f_7350_, 5, v___f_7348_);
    lean_closure_set(v___f_7350_, 6, v___f_7349_);
    lean_closure_set(v___f_7350_, 7, v_inst_7342_);
    lean_closure_set(v___f_7350_, 8, v_inst_7344_);
    v___x_7351_ = lean_apply_4(
        v_toBind_7346_,
        lean_box(0),
        lean_box(0),
        v_inst_7340_,
        v___f_7350_,
    );
    return v___x_7351_;
}
pub unsafe fn l_Lean_addTraceAsMessages(
    mut v_m_7352_: *mut LeanObject,
    mut v_inst_7353_: *mut LeanObject,
    mut v_inst_7354_: *mut LeanObject,
    mut v_inst_7355_: *mut LeanObject,
    mut v_inst_7356_: *mut LeanObject,
    mut v_inst_7357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    v___x_7358_ = l_Lean_addTraceAsMessages___redArg(
        v_inst_7353_,
        v_inst_7354_,
        v_inst_7355_,
        v_inst_7356_,
        v_inst_7357_,
    );
    return v___x_7358_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    v___x_7400_ = lean_unsigned_to_nat(2826257906);
    v___x_7401_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7402_ = l_Lean_Name_num___override(v___x_7401_, v___x_7400_);
    return v___x_7402_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    v___x_7404_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7405_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7406_ = l_Lean_Name_str___override(v___x_7405_, v___x_7404_);
    return v___x_7406_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut LeanObject = core::ptr::null_mut();
    v___x_7408_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7409_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7410_ = l_Lean_Name_str___override(v___x_7409_, v___x_7408_);
    return v___x_7410_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    v___x_7411_ = lean_unsigned_to_nat(2);
    v___x_7412_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7413_ = l_Lean_Name_num___override(v___x_7412_, v___x_7411_);
    return v___x_7413_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: u8 = 0;
    let mut v___x_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    v___x_7415_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7416_ = 0;
    v___x_7417_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7418_ = l_Lean_registerTraceClass(v___x_7415_, v___x_7416_, v___x_7417_);
    return v___x_7418_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(
    mut v_a_7419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7420_: *mut LeanObject = core::ptr::null_mut();
    v_res_7420_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
    return v_res_7420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedTraceElem_default = _init_l_Lean_instInhabitedTraceElem_default();
    lean_mark_persistent(l_Lean_instInhabitedTraceElem_default);
    l_Lean_instInhabitedTraceElem = _init_l_Lean_instInhabitedTraceElem();
    lean_mark_persistent(l_Lean_instInhabitedTraceElem);
    l_Lean_instInhabitedTraceState_default = _init_l_Lean_instInhabitedTraceState_default();
    lean_mark_persistent(l_Lean_instInhabitedTraceState_default);
    l_Lean_instInhabitedTraceState = _init_l_Lean_instInhabitedTraceState();
    lean_mark_persistent(l_Lean_instInhabitedTraceState);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_inheritedTraceOptions = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_inheritedTraceOptions);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_threshold = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler_threshold);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_useHeartbeats = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler_useHeartbeats);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_output = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler_output);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_serve = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler_serve);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_output_pp = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_trace_profiler_output_pp);
    lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_MonadTrace_getInheritedTraceOptions___autoParam =
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam();
    lean_mark_persistent(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam);
    l_Lean_registerTraceClass___auto__1 = _init_l_Lean_registerTraceClass___auto__1();
    lean_mark_persistent(l_Lean_registerTraceClass___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_Trace(builtin);
}
