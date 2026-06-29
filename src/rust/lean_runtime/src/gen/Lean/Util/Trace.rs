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
static mut l_Lean_instInhabitedTraceElem_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTraceElem_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceElem_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceElem: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTraceState_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTraceState_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedTraceState_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTraceState_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTraceState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_inheritedTraceOptions: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value:
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value
        ) as *mut crate::leanh::LeanObject,
        18248147900842368367 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        17564138194259293689 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_MonadTrace_getInheritedTraceOptions___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_printTraces___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToStringFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_printTraces___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_printTraces___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_resetTraceState___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_resetTraceState___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resetTraceState___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resetTraceState___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_checkTraceOption___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_checkTraceOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkTraceOption___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_checkTraceOption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkTraceOption___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___redArg___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_addTrace___redArg___lam__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_addTrace___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___redArg___lam__0___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_addTrace___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 102, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<99> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 99, m_capacity: 99, m_length: 98, m_data: [97, 99, 116, 105, 118, 97, 116, 101, 32, 110, 101, 115, 116, 101, 100, 32, 116, 114, 97, 99, 101, 115, 32, 119, 105, 116, 104, 32, 101, 120, 101, 99, 117, 116, 105, 111, 110, 32, 116, 105, 109, 101, 32, 97, 98, 111, 118, 101, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 32, 97, 110, 100, 32, 97, 110, 110, 111, 116, 97, 116, 101, 32, 119, 105, 116, 104, 32, 116, 105, 109, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3029557009233611192 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<130> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 130, m_capacity: 130, m_length: 129, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 105, 110, 32, 109, 105, 108, 108, 105, 115, 101, 99, 111, 110, 100, 115, 32, 40, 111, 114, 32, 104, 101, 97, 114, 116, 98, 101, 97, 116, 115, 32, 105, 102, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 46, 117, 115, 101, 72, 101, 97, 114, 116, 98, 101, 97, 116, 115, 96, 32, 105, 115, 32, 116, 114, 117, 101, 41, 44, 32, 116, 114, 97, 99, 101, 115, 32, 98, 101, 108, 111, 119, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 98, 101, 32, 97, 99, 116, 105, 118, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9872414562944363921 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler_threshold: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 115, 101, 72, 101, 97, 114, 116, 98, 101, 97, 116, 115, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3582102001749243616 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 109, 101, 97, 115, 117, 114, 101, 32, 97, 110, 100, 32, 114, 101, 112, 111, 114, 116, 32, 104, 101, 97, 114, 116, 98, 101, 97, 116, 115, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 115, 101, 99, 111, 110, 100, 115, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4070060546168584281 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler_useHeartbeats: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 117, 116, 112, 117, 116, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4936720448426421523 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<86> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [111, 117, 116, 112, 117, 116, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 96, 32, 100, 97, 116, 97, 32, 105, 110, 32, 70, 105, 114, 101, 102, 111, 120, 32, 80, 114, 111, 102, 105, 108, 101, 114, 45, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 102, 111, 114, 109, 97, 116, 32, 116, 111, 32, 103, 105, 118, 101, 110, 32, 102, 105, 108, 101, 32, 112, 97, 116, 104, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_addTrace___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16374006435548021562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler_output: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 101, 114, 118, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9644734713936406706 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<126> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [115, 101, 114, 118, 101, 32, 116, 104, 101, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 96, 32, 100, 97, 116, 97, 32, 111, 118, 101, 114, 32, 72, 84, 84, 80, 32, 97, 110, 100, 32, 111, 112, 101, 110, 32, 105, 116, 32, 105, 110, 32, 96, 104, 116, 116, 112, 115, 58, 47, 47, 112, 114, 111, 102, 105, 108, 101, 114, 46, 102, 105, 114, 101, 102, 111, 120, 46, 99, 111, 109, 96, 59, 32, 98, 108, 111, 99, 107, 115, 32, 117, 110, 116, 105, 108, 32, 105, 110, 116, 101, 114, 114, 117, 112, 116, 101, 100, 32, 119, 105, 116, 104, 32, 67, 116, 114, 108, 43, 67, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5084970274551519787 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler_serve: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5412095016269638404 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4936720448426421523 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12287765182031389121 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<232> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 232, m_capacity: 232, m_length: 231, m_data: [105, 102, 32, 102, 97, 108, 115, 101, 44, 32, 108, 105, 109, 105, 116, 32, 116, 101, 120, 116, 32, 105, 110, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 115, 32, 116, 111, 32, 116, 114, 97, 99, 101, 32, 99, 108, 97, 115, 115, 32, 110, 97, 109, 101, 32, 97, 110, 100, 32, 96, 84, 114, 97, 99, 101, 68, 97, 116, 97, 46, 116, 97, 103, 96, 44, 32, 105, 102, 32, 97, 110, 121, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 119, 104, 101, 110, 32, 119, 101, 32, 97, 114, 101, 32, 105, 110, 116, 101, 114, 101, 115, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 116, 105, 109, 101, 32, 116, 97, 107, 101, 110, 32, 98, 121, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 115, 117, 98, 115, 121, 115, 116, 101, 109, 115, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 115, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 116, 104, 101, 32, 99, 111, 109, 109, 111, 110, 32, 99, 97, 115, 101, 46, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_checkTraceOption___closed__0_value) as *mut crate::leanh::LeanObject,10644982123717200237 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15799939003794391761 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16374006435548021562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15606591623558354660 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_trace_profiler_output_pp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0: f64 =
    0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_monoNanosNow___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_getNumHeartbeats___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_trace_profiler_threshold_unitAdjusted___closed__0: f64 = 0.0;
static mut l_Lean_instMonadAlwaysExceptEIO___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instMonadAlwaysExceptEIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_bombEmoji___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_bombEmoji___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_bombEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_bombEmoji: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_bombEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkEmoji___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_checkEmoji___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_checkEmoji: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_crossEmoji___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_crossEmoji___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_crossEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_crossEmoji: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_crossEmoji___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instExceptToTraceResultBool___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instExceptToTraceResultBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instExceptToTraceResultBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultBool___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instExceptToTraceResultOption___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instExceptToTraceResultOption___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instExceptToTraceResultOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instExceptToTraceResultExpr___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instExceptToTraceResultExpr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instExceptToTraceResultExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResultExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instExceptToTraceResult___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instExceptToTraceResult___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instExceptToTraceResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instExceptToTraceResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_withTraceNode_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_withTraceNode_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withTraceNode_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withTraceNode_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_registerTraceClass___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__1_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_registerTraceClass___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_registerTraceClass___auto__1___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7677164612348466033 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_registerTraceClass___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerTraceClass___auto__1___closed__3_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_registerTraceClass___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_registerTraceClass___auto__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerTraceClass___auto__1___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerTraceClass___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_registerTraceClass___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerTraceClass___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [0 as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_registerTraceClass___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerTraceClass___closed__1_value: crate::leanh::LeanStringObject<59> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 59,
        m_capacity: 59,
        m_length: 58,
        m_data: [
            101, 110, 97, 98, 108, 101, 47, 100, 105, 115, 97, 98, 108, 101, 32, 116, 114, 97, 99,
            105, 110, 103, 32, 102, 111, 114, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32,
            109, 111, 100, 117, 108, 101, 32, 97, 110, 100, 32, 115, 117, 98, 109, 111, 100, 117,
            108, 101, 115, 0,
        ],
    };
static mut l_Lean_registerTraceClass___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerTraceClass___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9871775667037945883 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value)
            as *mut crate::leanh::LeanObject,
        4570674678924417756 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value)
            as *mut crate::leanh::LeanObject,
        3326968124746134365 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value)
            as *mut crate::leanh::LeanObject,
        940684074193935882 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value)
            as *mut crate::leanh::LeanObject,
        14774476768116910908 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value)
            as *mut crate::leanh::LeanObject,
        17404204824591055365 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value)
            as *mut crate::leanh::LeanObject,
        8036185514257755965 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value)
            as *mut crate::leanh::LeanObject,
        17116161260408496210 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value)
            as *mut crate::leanh::LeanObject,
        13708106407786339395 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value)
            as *mut crate::leanh::LeanObject,
        17601562613467935004 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value)
            as *mut crate::leanh::LeanObject,
        9368229134555052249 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value)
            as *mut crate::leanh::LeanObject,
        14298422259736409839 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value)
            as *mut crate::leanh::LeanObject,
        5346268661279150583 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_registerTraceClass___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value)
            as *mut crate::leanh::LeanObject,
        7306243862518720553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
            as *mut crate::leanh::LeanObject,
        11510953549444071797 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value)
            as *mut crate::leanh::LeanObject,
        491622604497152460 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value)
            as *mut crate::leanh::LeanObject,
        13317951319906582257 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            2825612102870995038 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [116, 114, 97, 99, 101, 91, 0],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value)
                as *mut crate::leanh::LeanObject,
            18163029821153688220 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_doElemTrace_x5b___x5d_____00__closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_doElemTrace_x5b___x5d____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHashableRaw_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableProd___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___redArg___lam__11___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_addTraceAsMessages___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_addTraceAsMessages___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_addTraceAsMessages___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addTraceAsMessages___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_addTraceAsMessages___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_addTraceAsMessages___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTraceAsMessages___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16213016488940853032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11246366368068211756 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8857498384450530577 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9067059375846622420 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,16991972533670276437 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4136137159096495612 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15300736648833417205 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value) as *mut crate::leanh::LeanObject,7375598387208490336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13915489522383829438 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5175429902338115595 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_instInhabitedTraceElem_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Lean_instInhabitedMessageData_default;
    v___x_3712_ = crate::leanh::lean_box(0);
    v___x_3713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3713_, 0, v___x_3712_);
    crate::leanh::lean_ctor_set(v___x_3713_, 1, v___x_3711_);
    return v___x_3713_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceElem_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceElem_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceElem_default___closed__0_once),
        _init_l_Lean_instInhabitedTraceElem_default___closed__0,
    );
    return v___x_3714_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceElem() -> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_instInhabitedTraceElem_default;
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3717_ = lean_mk_empty_array_with_capacity(v___x_3716_);
    v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3719_: usize = 0;
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3719_ = 5usize;
    v___x_3720_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3721_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3722_ = lean_mk_empty_array_with_capacity(v___x_3721_);
    v___x_3723_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__0_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__0,
    );
    v___x_3724_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3724_, 0, v___x_3723_);
    crate::leanh::lean_ctor_set(v___x_3724_, 1, v___x_3722_);
    crate::leanh::lean_ctor_set(v___x_3724_, 2, v___x_3720_);
    crate::leanh::lean_ctor_set(v___x_3724_, 3, v___x_3720_);
    crate::leanh::lean_ctor_set_usize(v___x_3724_, 4, v___x_3719_);
    return v___x_3724_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u64 = 0;
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__1,
    );
    v___x_3726_ = 0u64;
    v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3725_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3727_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3726_,
    );
    return v___x_3727_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__2,
    );
    return v___x_3728_;
}
pub unsafe fn _init_l_Lean_instInhabitedTraceState() -> *mut crate::leanh::LeanObject {
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_instInhabitedTraceState_default;
    return v___x_3729_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3730_ = crate::leanh::lean_box(0);
    v___x_3731_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3732_ = lean_mk_array(v___x_3731_, v___x_3730_);
    return v___x_3732_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
    v___x_3734_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3735_, 0, v___x_3734_);
    crate::leanh::lean_ctor_set(v___x_3735_, 1, v___x_3733_);
    return v___x_3735_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3737_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
    v___x_3738_ = lean_st_mk_ref(v___x_3737_);
    v___x_3739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3739_, 0, v___x_3738_);
    return v___x_3739_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(
    mut v_a_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
    return v_res_3741_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10;
    v___x_3769_ = l_Lean_mkAtom(v___x_3768_);
    return v___x_3769_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3770_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14;
    v___x_3775_ = lean_string_utf8_byte_size(v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15,
    );
    v___x_3777_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3778_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14;
    v___x_3779_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3779_, 0, v___x_3778_);
    crate::leanh::lean_ctor_set(v___x_3779_, 1, v___x_3777_);
    crate::leanh::lean_ctor_set(v___x_3779_, 2, v___x_3776_);
    return v___x_3779_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = crate::leanh::lean_box(0);
    v___x_3786_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19;
    v___x_3787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16,
    );
    v___x_3788_ = crate::leanh::lean_box(2);
    v___x_3789_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3789_, 0, v___x_3788_);
    crate::leanh::lean_ctor_set(v___x_3789_, 1, v___x_3787_);
    crate::leanh::lean_ctor_set(v___x_3789_, 2, v___x_3786_);
    crate::leanh::lean_ctor_set(v___x_3789_, 3, v___x_3785_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3790_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20,
    );
    v___x_3791_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21,
    );
    v___x_3794_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11;
    v___x_3795_ = crate::leanh::lean_box(2);
    v___x_3796_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3795_);
    crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3794_);
    crate::leanh::lean_ctor_set(v___x_3796_, 2, v___x_3793_);
    return v___x_3796_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23,
    );
    v___x_3801_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
    v___x_3802_ = crate::leanh::lean_box(2);
    v___x_3803_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3803_, 0, v___x_3802_);
    crate::leanh::lean_ctor_set(v___x_3803_, 1, v___x_3801_);
    crate::leanh::lean_ctor_set(v___x_3803_, 2, v___x_3800_);
    return v___x_3803_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3804_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25,
    );
    v___x_3808_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7;
    v___x_3809_ = crate::leanh::lean_box(2);
    v___x_3810_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    crate::leanh::lean_ctor_set(v___x_3810_, 1, v___x_3808_);
    crate::leanh::lean_ctor_set(v___x_3810_, 2, v___x_3807_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3811_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27
        ),
        core::ptr::addr_of_mut!(
            l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once
        ),
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27,
    );
    v___x_3815_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4;
    v___x_3816_ = crate::leanh::lean_box(2);
    v___x_3817_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3816_);
    crate::leanh::lean_ctor_set(v___x_3817_, 1, v___x_3815_);
    crate::leanh::lean_ctor_set(v___x_3817_, 2, v___x_3814_);
    return v___x_3817_;
}
pub unsafe fn _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3818_ = crate::leanh::lean_obj_once(
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
    mut v_modifyTraceState_3819_: *mut crate::leanh::LeanObject,
    mut v_inst_3820_: *mut crate::leanh::LeanObject,
    mut v_f_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3822_ = crate::leanh::lean_apply_1(v_modifyTraceState_3819_, v_f_3821_);
    v___x_3823_ = crate::leanh::lean_apply_2(v_inst_3820_, crate::leanh::lean_box(0), v___x_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_instMonadTraceOfMonadLift___redArg(
    mut v_inst_3824_: *mut crate::leanh::LeanObject,
    mut v_inst_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___f_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_modifyTraceState_3826_ = crate::leanh::lean_ctor_get(v_inst_3825_, 0);
                v_getTraceState_3827_ = crate::leanh::lean_ctor_get(v_inst_3825_, 1);
                v_getInheritedTraceOptions_3828_ = crate::leanh::lean_ctor_get(v_inst_3825_, 2);
                v_isSharedCheck_3838_ = (!crate::leanh::lean_is_exclusive(v_inst_3825_)) as u8;
                if v_isSharedCheck_3838_ == 0 {
                    v___x_3830_ = v_inst_3825_;
                    v_isShared_3831_ = v_isSharedCheck_3838_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_getInheritedTraceOptions_3828_);
                    crate::leanh::lean_inc(v_getTraceState_3827_);
                    crate::leanh::lean_inc(v_modifyTraceState_3826_);
                    crate::leanh::lean_dec(v_inst_3825_);
                    v___x_3830_ = crate::leanh::lean_box(0);
                    v_isShared_3831_ = v_isSharedCheck_3838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_inst_3824_, 2);
                v___f_3832_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadTraceOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3832_, 0, v_modifyTraceState_3826_);
                crate::leanh::lean_closure_set(v___f_3832_, 1, v_inst_3824_);
                v___x_3833_ = crate::leanh::lean_apply_2(
                    v_inst_3824_,
                    crate::leanh::lean_box(0),
                    v_getTraceState_3827_,
                );
                v___x_3834_ = crate::leanh::lean_apply_2(
                    v_inst_3824_,
                    crate::leanh::lean_box(0),
                    v_getInheritedTraceOptions_3828_,
                );
                if v_isShared_3831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3830_, 2, v___x_3834_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 1, v___x_3833_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 0, v___f_3832_);
                    v___x_3836_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3837_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___f_3832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3837_, 2, v___x_3834_);
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
    mut v_m_3839_: *mut crate::leanh::LeanObject,
    mut v_n_3840_: *mut crate::leanh::LeanObject,
    mut v_inst_3841_: *mut crate::leanh::LeanObject,
    mut v_inst_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_3841_, v_inst_3842_);
    return v___x_3843_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__0(
    mut v_toPure_3844_: *mut crate::leanh::LeanObject,
    mut v_____s_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = crate::leanh::lean_box(0);
    v___x_3847_ =
        crate::leanh::lean_apply_2(v_toPure_3844_, crate::leanh::lean_box(0), v___x_3846_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__1(
    mut v___x_3848_: *mut crate::leanh::LeanObject,
    mut v_toPure_3849_: *mut crate::leanh::LeanObject,
    mut v_r_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3848_);
    v___x_3852_ =
        crate::leanh::lean_apply_2(v_toPure_3849_, crate::leanh::lean_box(0), v___x_3851_);
    return v___x_3852_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__2(
    mut v___f_3853_: *mut crate::leanh::LeanObject,
    mut v_inst_3854_: *mut crate::leanh::LeanObject,
    mut v_toBind_3855_: *mut crate::leanh::LeanObject,
    mut v___f_3856_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ =
        crate::leanh::lean_alloc_closure(l_IO_println___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3858_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3858_, 1, v___f_3853_);
    crate::leanh::lean_closure_set(v___x_3858_, 2, v_____do__lift_3857_);
    v___x_3859_ = crate::leanh::lean_apply_2(v_inst_3854_, crate::leanh::lean_box(0), v___x_3858_);
    v___x_3860_ = crate::leanh::lean_apply_4(
        v_toBind_3855_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3859_,
        v___f_3856_,
    );
    return v___x_3860_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__3(
    mut v_inst_3861_: *mut crate::leanh::LeanObject,
    mut v_toBind_3862_: *mut crate::leanh::LeanObject,
    mut v___f_3863_: *mut crate::leanh::LeanObject,
    mut v_x_3864_: *mut crate::leanh::LeanObject,
    mut v_____s_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msg_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_msg_3866_ = crate::leanh::lean_ctor_get(v_x_3864_, 1);
    crate::leanh::lean_inc_ref(v_msg_3866_);
    crate::leanh::lean_dec_ref(v_x_3864_);
    v___x_3867_ = crate::leanh::lean_box(0);
    v___x_3868_ = crate::leanh::lean_alloc_closure(
        l_Lean_MessageData_format___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3868_, 0, v_msg_3866_);
    crate::leanh::lean_closure_set(v___x_3868_, 1, v___x_3867_);
    v___x_3869_ =
        crate::leanh::lean_alloc_closure(l_BaseIO_toIO___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_3869_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3869_, 1, v___x_3868_);
    v___x_3870_ = crate::leanh::lean_apply_2(v_inst_3861_, crate::leanh::lean_box(0), v___x_3869_);
    v___x_3871_ = crate::leanh::lean_apply_4(
        v_toBind_3862_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3870_,
        v___f_3863_,
    );
    return v___x_3871_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__4(
    mut v_toPure_3872_: *mut crate::leanh::LeanObject,
    mut v___f_3873_: *mut crate::leanh::LeanObject,
    mut v_inst_3874_: *mut crate::leanh::LeanObject,
    mut v_toBind_3875_: *mut crate::leanh::LeanObject,
    mut v_inst_3876_: *mut crate::leanh::LeanObject,
    mut v___f_3877_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_traces_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_traces_3879_ = crate::leanh::lean_ctor_get(v_____do__lift_3878_, 0);
    v___x_3880_ = crate::leanh::lean_box(0);
    v___f_3881_ = crate::leanh::lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3881_, 0, v___x_3880_);
    crate::leanh::lean_closure_set(v___f_3881_, 1, v_toPure_3872_);
    crate::leanh::lean_inc_n(v_toBind_3875_, 2);
    crate::leanh::lean_inc(v_inst_3874_);
    v___f_3882_ = crate::leanh::lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3882_, 0, v___f_3873_);
    crate::leanh::lean_closure_set(v___f_3882_, 1, v_inst_3874_);
    crate::leanh::lean_closure_set(v___f_3882_, 2, v_toBind_3875_);
    crate::leanh::lean_closure_set(v___f_3882_, 3, v___f_3881_);
    v___f_3883_ = crate::leanh::lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3883_, 0, v_inst_3874_);
    crate::leanh::lean_closure_set(v___f_3883_, 1, v_toBind_3875_);
    crate::leanh::lean_closure_set(v___f_3883_, 2, v___f_3882_);
    v___x_3884_ = l_Lean_PersistentArray_forIn___redArg(
        v_inst_3876_,
        v_traces_3879_,
        v___x_3880_,
        v___f_3883_,
    );
    v___x_3885_ = crate::leanh::lean_apply_4(
        v_toBind_3875_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3884_,
        v___f_3877_,
    );
    return v___x_3885_;
}
pub unsafe fn l_Lean_printTraces___redArg___lam__4___boxed(
    mut v_toPure_3886_: *mut crate::leanh::LeanObject,
    mut v___f_3887_: *mut crate::leanh::LeanObject,
    mut v_inst_3888_: *mut crate::leanh::LeanObject,
    mut v_toBind_3889_: *mut crate::leanh::LeanObject,
    mut v_inst_3890_: *mut crate::leanh::LeanObject,
    mut v___f_3891_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Lean_printTraces___redArg___lam__4(
        v_toPure_3886_,
        v___f_3887_,
        v_inst_3888_,
        v_toBind_3889_,
        v_inst_3890_,
        v___f_3891_,
        v_____do__lift_3892_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_3892_);
    return v_res_3893_;
}
pub unsafe fn l_Lean_printTraces___redArg(
    mut v_inst_3895_: *mut crate::leanh::LeanObject,
    mut v_inst_3896_: *mut crate::leanh::LeanObject,
    mut v_inst_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3898_ = crate::leanh::lean_ctor_get(v_inst_3895_, 0);
    v_toBind_3899_ = crate::leanh::lean_ctor_get(v_inst_3895_, 1);
    crate::leanh::lean_inc_n(v_toBind_3899_, 2);
    v_getTraceState_3900_ = crate::leanh::lean_ctor_get(v_inst_3896_, 1);
    crate::leanh::lean_inc(v_getTraceState_3900_);
    crate::leanh::lean_dec_ref(v_inst_3896_);
    v_toPure_3901_ = crate::leanh::lean_ctor_get(v_toApplicative_3898_, 1);
    crate::leanh::lean_inc_n(v_toPure_3901_, 2);
    v___f_3902_ = l_Lean_printTraces___redArg___closed__0;
    v___f_3903_ = crate::leanh::lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3903_, 0, v_toPure_3901_);
    v___f_3904_ = crate::leanh::lean_alloc_closure(
        l_Lean_printTraces___redArg___lam__4___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_3904_, 0, v_toPure_3901_);
    crate::leanh::lean_closure_set(v___f_3904_, 1, v___f_3902_);
    crate::leanh::lean_closure_set(v___f_3904_, 2, v_inst_3897_);
    crate::leanh::lean_closure_set(v___f_3904_, 3, v_toBind_3899_);
    crate::leanh::lean_closure_set(v___f_3904_, 4, v_inst_3895_);
    crate::leanh::lean_closure_set(v___f_3904_, 5, v___f_3903_);
    v___x_3905_ = crate::leanh::lean_apply_4(
        v_toBind_3899_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getTraceState_3900_,
        v___f_3904_,
    );
    return v___x_3905_;
}
pub unsafe fn l_Lean_printTraces(
    mut v_m_3906_: *mut crate::leanh::LeanObject,
    mut v_inst_3907_: *mut crate::leanh::LeanObject,
    mut v_inst_3908_: *mut crate::leanh::LeanObject,
    mut v_inst_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Lean_printTraces___redArg(v_inst_3907_, v_inst_3908_, v_inst_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Lean_resetTraceState___redArg___lam__0(
    mut v_x_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3913_ = lean_mk_empty_array_with_capacity(v___x_3912_);
    crate::leanh::lean_dec_ref(v___x_3913_);
    v___x_3914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__2_once),
        _init_l_Lean_instInhabitedTraceState_default___closed__2,
    );
    return v___x_3914_;
}
pub unsafe fn l_Lean_resetTraceState___redArg___lam__0___boxed(
    mut v_x_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3916_ = l_Lean_resetTraceState___redArg___lam__0(v_x_3915_);
    crate::leanh::lean_dec_ref(v_x_3915_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_resetTraceState___redArg(
    mut v_inst_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_3919_ = crate::leanh::lean_ctor_get(v_inst_3918_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_3919_);
    crate::leanh::lean_dec_ref(v_inst_3918_);
    v___f_3920_ = l_Lean_resetTraceState___redArg___closed__0;
    v___x_3921_ = crate::leanh::lean_apply_1(v_modifyTraceState_3919_, v___f_3920_);
    return v___x_3921_;
}
pub unsafe fn l_Lean_resetTraceState(
    mut v_m_3922_: *mut crate::leanh::LeanObject,
    mut v_inst_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3924_ = l_Lean_resetTraceState___redArg(v_inst_3923_);
    return v___x_3924_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_x_3926_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3927_: u8 = 0;
    let mut v_key_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3926_) == 0 {
                    v___x_3927_ = 0;
                    return v___x_3927_;
                } else {
                    v_key_3928_ = crate::leanh::lean_ctor_get(v_x_3926_, 0);
                    v_tail_3929_ = crate::leanh::lean_ctor_get(v_x_3926_, 2);
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
    mut v_a_3932_: *mut crate::leanh::LeanObject,
    mut v_x_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3934_: u8 = 0;
    let mut v_r_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_3932_, v_x_3933_);
    crate::leanh::lean_dec(v_x_3933_);
    crate::leanh::lean_dec(v_a_3932_);
    v_r_3935_ = crate::leanh::lean_box((v_res_3934_) as usize);
    return v_r_3935_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: u64 = 0;
    v___x_3936_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3937_ = lean_uint64_of_nat(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(
    mut v_m_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v___x_3957_: u64 = 0;
    let mut v_hash_3958_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3940_ = crate::leanh::lean_ctor_get(v_m_3938_, 1);
                v___x_3941_ = lean_array_get_size(v_buckets_3940_);
                if crate::leanh::lean_obj_tag(v_a_3939_) == 0 {
                    v___x_3957_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_3943_ = v___x_3957_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3958_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
    mut v_m_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: u8 = 0;
    let mut v_r_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_3959_, v_a_3960_);
    crate::leanh::lean_dec(v_a_3960_);
    crate::leanh::lean_dec_ref(v_m_3959_);
    v_r_3962_ = crate::leanh::lean_box((v_res_3961_) as usize);
    return v_r_3962_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
    mut v_inherited_3963_: *mut crate::leanh::LeanObject,
    mut v_opts_3964_: *mut crate::leanh::LeanObject,
    mut v_opt_3965_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_pre_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3970_: u8 = 0;
    let mut v_map_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3971_ = crate::leanh::lean_ctor_get(v_opts_3964_, 0);
                v___x_3972_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3971_, v_opt_3965_);
                if crate::leanh::lean_obj_tag(v___x_3972_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_3973_ = crate::leanh::lean_ctor_get(v___x_3972_, 0);
                    crate::leanh::lean_inc(v_val_3973_);
                    crate::leanh::lean_dec_ref_known(v___x_3972_, 1);
                    if crate::leanh::lean_obj_tag(v_val_3973_) == 1 {
                        v_v_3974_ = crate::leanh::lean_ctor_get_uint8(v_val_3973_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_val_3973_, 0);
                        return v_v_3974_;
                    } else {
                        crate::leanh::lean_dec(v_val_3973_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_opt_3965_) == 1 {
                    v_pre_3967_ = crate::leanh::lean_ctor_get(v_opt_3965_, 0);
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
    mut v_inherited_3975_: *mut crate::leanh::LeanObject,
    mut v_opts_3976_: *mut crate::leanh::LeanObject,
    mut v_opt_3977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3978_: u8 = 0;
    let mut v_r_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
        v_inherited_3975_,
        v_opts_3976_,
        v_opt_3977_,
    );
    crate::leanh::lean_dec(v_opt_3977_);
    crate::leanh::lean_dec_ref(v_opts_3976_);
    crate::leanh::lean_dec_ref(v_inherited_3975_);
    v_r_3979_ = crate::leanh::lean_box((v_res_3978_) as usize);
    return v_r_3979_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(
    mut v_00_u03b2_3980_: *mut crate::leanh::LeanObject,
    mut v_m_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3983_: u8 = 0;
    v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_3981_, v_a_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(
    mut v_00_u03b2_3984_: *mut crate::leanh::LeanObject,
    mut v_m_3985_: *mut crate::leanh::LeanObject,
    mut v_a_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: u8 = 0;
    let mut v_r_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_3984_, v_m_3985_, v_a_3986_);
    crate::leanh::lean_dec(v_a_3986_);
    crate::leanh::lean_dec_ref(v_m_3985_);
    v_r_3988_ = crate::leanh::lean_box((v_res_3987_) as usize);
    return v_r_3988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(
    mut v_00_u03b2_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_x_3991_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3992_: u8 = 0;
    v___x_3992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_3990_, v_x_3991_);
    return v___x_3992_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_3993_: *mut crate::leanh::LeanObject,
    mut v_a_3994_: *mut crate::leanh::LeanObject,
    mut v_x_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3996_: u8 = 0;
    let mut v_r_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_3993_, v_a_3994_, v_x_3995_);
    crate::leanh::lean_dec(v_x_3995_);
    crate::leanh::lean_dec(v_a_3994_);
    v_r_3997_ = crate::leanh::lean_box((v_res_3996_) as usize);
    return v_r_3997_;
}
pub unsafe fn l_Lean_checkTraceOption(
    mut v_inherited_4001_: *mut crate::leanh::LeanObject,
    mut v_opts_4002_: *mut crate::leanh::LeanObject,
    mut v_cls_4003_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_hasTrace_4004_: u8 = 0;
    v_hasTrace_4004_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_4002_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4004_ == 0 {
        crate::leanh::lean_dec(v_cls_4003_);
        return v_hasTrace_4004_;
    } else {
        let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4007_: u8 = 0;
        v___x_4005_ = l_Lean_checkTraceOption___closed__1;
        v___x_4006_ = l_Lean_Name_append(v___x_4005_, v_cls_4003_);
        v___x_4007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inherited_4001_,
            v_opts_4002_,
            v___x_4006_,
        );
        crate::leanh::lean_dec(v___x_4006_);
        return v___x_4007_;
    }
}
pub unsafe fn l_Lean_checkTraceOption___boxed(
    mut v_inherited_4008_: *mut crate::leanh::LeanObject,
    mut v_opts_4009_: *mut crate::leanh::LeanObject,
    mut v_cls_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4011_: u8 = 0;
    let mut v_r_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_Lean_checkTraceOption(v_inherited_4008_, v_opts_4009_, v_cls_4010_);
    crate::leanh::lean_dec_ref(v_opts_4009_);
    crate::leanh::lean_dec_ref(v_inherited_4008_);
    v_r_4012_ = crate::leanh::lean_box((v_res_4011_) as usize);
    return v_r_4012_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__0(
    mut v_toPure_4013_: *mut crate::leanh::LeanObject,
    mut v_cls_4014_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4015_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasTrace_4017_: u8 = 0;
    v_hasTrace_4017_ = crate::leanh::lean_ctor_get_uint8(
        v_____do__lift_4016_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4017_ == 0 {
        let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_4014_);
        v___x_4018_ = crate::leanh::lean_box((v_hasTrace_4017_) as usize);
        v___x_4019_ =
            crate::leanh::lean_apply_2(v_toPure_4013_, crate::leanh::lean_box(0), v___x_4018_);
        return v___x_4019_;
    } else {
        let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: u8 = 0;
        let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4020_ = l_Lean_checkTraceOption___closed__1;
        v___x_4021_ = l_Lean_Name_append(v___x_4020_, v_cls_4014_);
        v___x_4022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_4015_,
            v_____do__lift_4016_,
            v___x_4021_,
        );
        crate::leanh::lean_dec(v___x_4021_);
        v___x_4023_ = crate::leanh::lean_box((v___x_4022_) as usize);
        v___x_4024_ =
            crate::leanh::lean_apply_2(v_toPure_4013_, crate::leanh::lean_box(0), v___x_4023_);
        return v___x_4024_;
    }
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(
    mut v_toPure_4025_: *mut crate::leanh::LeanObject,
    mut v_cls_4026_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4027_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_Lean_isTracingEnabledFor___redArg___lam__0(
        v_toPure_4025_,
        v_cls_4026_,
        v_____do__lift_4027_,
        v_____do__lift_4028_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_4028_);
    crate::leanh::lean_dec_ref(v_____do__lift_4027_);
    return v_res_4029_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg___lam__1(
    mut v_toPure_4030_: *mut crate::leanh::LeanObject,
    mut v_cls_4031_: *mut crate::leanh::LeanObject,
    mut v_toBind_4032_: *mut crate::leanh::LeanObject,
    mut v_inst_4033_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4035_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4035_, 0, v_toPure_4030_);
    crate::leanh::lean_closure_set(v___f_4035_, 1, v_cls_4031_);
    crate::leanh::lean_closure_set(v___f_4035_, 2, v_____do__lift_4034_);
    v___x_4036_ = crate::leanh::lean_apply_4(
        v_toBind_4032_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4033_,
        v___f_4035_,
    );
    return v___x_4036_;
}
pub unsafe fn l_Lean_isTracingEnabledFor___redArg(
    mut v_inst_4037_: *mut crate::leanh::LeanObject,
    mut v_inst_4038_: *mut crate::leanh::LeanObject,
    mut v_inst_4039_: *mut crate::leanh::LeanObject,
    mut v_cls_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4041_ = crate::leanh::lean_ctor_get(v_inst_4037_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4041_);
    v_toBind_4042_ = crate::leanh::lean_ctor_get(v_inst_4037_, 1);
    crate::leanh::lean_inc_n(v_toBind_4042_, 2);
    crate::leanh::lean_dec_ref(v_inst_4037_);
    v_getInheritedTraceOptions_4043_ = crate::leanh::lean_ctor_get(v_inst_4038_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4043_);
    crate::leanh::lean_dec_ref(v_inst_4038_);
    v_toPure_4044_ = crate::leanh::lean_ctor_get(v_toApplicative_4041_, 1);
    crate::leanh::lean_inc(v_toPure_4044_);
    crate::leanh::lean_dec_ref(v_toApplicative_4041_);
    v___f_4045_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4045_, 0, v_toPure_4044_);
    crate::leanh::lean_closure_set(v___f_4045_, 1, v_cls_4040_);
    crate::leanh::lean_closure_set(v___f_4045_, 2, v_toBind_4042_);
    crate::leanh::lean_closure_set(v___f_4045_, 3, v_inst_4039_);
    v___x_4046_ = crate::leanh::lean_apply_4(
        v_toBind_4042_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4043_,
        v___f_4045_,
    );
    return v___x_4046_;
}
pub unsafe fn l_Lean_isTracingEnabledFor(
    mut v_m_4047_: *mut crate::leanh::LeanObject,
    mut v_inst_4048_: *mut crate::leanh::LeanObject,
    mut v_inst_4049_: *mut crate::leanh::LeanObject,
    mut v_inst_4050_: *mut crate::leanh::LeanObject,
    mut v_cls_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4052_ = crate::leanh::lean_ctor_get(v_inst_4048_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4052_);
    v_toBind_4053_ = crate::leanh::lean_ctor_get(v_inst_4048_, 1);
    crate::leanh::lean_inc_n(v_toBind_4053_, 2);
    crate::leanh::lean_dec_ref(v_inst_4048_);
    v_getInheritedTraceOptions_4054_ = crate::leanh::lean_ctor_get(v_inst_4049_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4054_);
    crate::leanh::lean_dec_ref(v_inst_4049_);
    v_toPure_4055_ = crate::leanh::lean_ctor_get(v_toApplicative_4052_, 1);
    crate::leanh::lean_inc(v_toPure_4055_);
    crate::leanh::lean_dec_ref(v_toApplicative_4052_);
    v___f_4056_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4056_, 0, v_toPure_4055_);
    crate::leanh::lean_closure_set(v___f_4056_, 1, v_cls_4051_);
    crate::leanh::lean_closure_set(v___f_4056_, 2, v_toBind_4053_);
    crate::leanh::lean_closure_set(v___f_4056_, 3, v_inst_4050_);
    v___x_4057_ = crate::leanh::lean_apply_4(
        v_toBind_4053_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4054_,
        v___f_4056_,
    );
    return v___x_4057_;
}
pub unsafe fn lean_is_trace_class_enabled(
    mut v_opts_4058_: *mut crate::leanh::LeanObject,
    mut v_cls_4059_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_hasTrace_4061_: u8 = 0;
    v_hasTrace_4061_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_4058_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4061_ == 0 {
        crate::leanh::lean_dec(v_cls_4059_);
        crate::leanh::lean_dec_ref(v_opts_4058_);
        return v_hasTrace_4061_;
    } else {
        let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        crate::leanh::lean_dec(v___x_4065_);
        crate::leanh::lean_dec_ref(v_opts_4058_);
        crate::leanh::lean_dec(v___x_4063_);
        return v___x_4066_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(
    mut v_opts_4067_: *mut crate::leanh::LeanObject,
    mut v_cls_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4070_: u8 = 0;
    let mut v_r_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4070_ = lean_is_trace_class_enabled(v_opts_4067_, v_cls_4068_);
    v_r_4071_ = crate::leanh::lean_box((v_res_4070_) as usize);
    return v_r_4071_;
}
pub unsafe fn l_Lean_getTraces___redArg___lam__0(
    mut v_toPure_4072_: *mut crate::leanh::LeanObject,
    mut v_s_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_traces_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_traces_4074_ = crate::leanh::lean_ctor_get(v_s_4073_, 0);
    crate::leanh::lean_inc_ref(v_traces_4074_);
    crate::leanh::lean_dec_ref(v_s_4073_);
    v___x_4075_ =
        crate::leanh::lean_apply_2(v_toPure_4072_, crate::leanh::lean_box(0), v_traces_4074_);
    return v___x_4075_;
}
pub unsafe fn l_Lean_getTraces___redArg(
    mut v_inst_4076_: *mut crate::leanh::LeanObject,
    mut v_inst_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4078_ = crate::leanh::lean_ctor_get(v_inst_4076_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4078_);
    v_toBind_4079_ = crate::leanh::lean_ctor_get(v_inst_4076_, 1);
    crate::leanh::lean_inc(v_toBind_4079_);
    crate::leanh::lean_dec_ref(v_inst_4076_);
    v_getTraceState_4080_ = crate::leanh::lean_ctor_get(v_inst_4077_, 1);
    crate::leanh::lean_inc(v_getTraceState_4080_);
    crate::leanh::lean_dec_ref(v_inst_4077_);
    v_toPure_4081_ = crate::leanh::lean_ctor_get(v_toApplicative_4078_, 1);
    crate::leanh::lean_inc(v_toPure_4081_);
    crate::leanh::lean_dec_ref(v_toApplicative_4078_);
    v___f_4082_ = crate::leanh::lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4082_, 0, v_toPure_4081_);
    v___x_4083_ = crate::leanh::lean_apply_4(
        v_toBind_4079_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getTraceState_4080_,
        v___f_4082_,
    );
    return v___x_4083_;
}
pub unsafe fn l_Lean_getTraces(
    mut v_m_4084_: *mut crate::leanh::LeanObject,
    mut v_inst_4085_: *mut crate::leanh::LeanObject,
    mut v_inst_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4087_ = crate::leanh::lean_ctor_get(v_inst_4085_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4087_);
    v_toBind_4088_ = crate::leanh::lean_ctor_get(v_inst_4085_, 1);
    crate::leanh::lean_inc(v_toBind_4088_);
    crate::leanh::lean_dec_ref(v_inst_4085_);
    v_getTraceState_4089_ = crate::leanh::lean_ctor_get(v_inst_4086_, 1);
    crate::leanh::lean_inc(v_getTraceState_4089_);
    crate::leanh::lean_dec_ref(v_inst_4086_);
    v_toPure_4090_ = crate::leanh::lean_ctor_get(v_toApplicative_4087_, 1);
    crate::leanh::lean_inc(v_toPure_4090_);
    crate::leanh::lean_dec_ref(v_toApplicative_4087_);
    v___f_4091_ = crate::leanh::lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4091_, 0, v_toPure_4090_);
    v___x_4092_ = crate::leanh::lean_apply_4(
        v_toBind_4088_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getTraceState_4089_,
        v___f_4091_,
    );
    return v___x_4092_;
}
pub unsafe fn l_Lean_modifyTraces___redArg___lam__0(
    mut v_f_4093_: *mut crate::leanh::LeanObject,
    mut v_s_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_4095_: u64 = 0;
    let mut v_traces_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4095_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_4094_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4096_ = crate::leanh::lean_ctor_get(v_s_4094_, 0);
                v_isSharedCheck_4104_ = (!crate::leanh::lean_is_exclusive(v_s_4094_)) as u8;
                if v_isSharedCheck_4104_ == 0 {
                    v___x_4098_ = v_s_4094_;
                    v_isShared_4099_ = v_isSharedCheck_4104_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4096_);
                    crate::leanh::lean_dec(v_s_4094_);
                    v___x_4098_ = crate::leanh::lean_box(0);
                    v_isShared_4099_ = v_isSharedCheck_4104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4100_ = crate::leanh::lean_apply_1(v_f_4093_, v_traces_4096_);
                if v_isShared_4099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4098_, 0, v___x_4100_);
                    v___x_4102_ = v___x_4098_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4103_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_inst_4105_: *mut crate::leanh::LeanObject,
    mut v_f_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4107_ = crate::leanh::lean_ctor_get(v_inst_4105_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4107_);
    crate::leanh::lean_dec_ref(v_inst_4105_);
    v___f_4108_ = crate::leanh::lean_alloc_closure(
        l_Lean_modifyTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4108_, 0, v_f_4106_);
    v___x_4109_ = crate::leanh::lean_apply_1(v_modifyTraceState_4107_, v___f_4108_);
    return v___x_4109_;
}
pub unsafe fn l_Lean_modifyTraces(
    mut v_m_4110_: *mut crate::leanh::LeanObject,
    mut v_inst_4111_: *mut crate::leanh::LeanObject,
    mut v_f_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4113_ = crate::leanh::lean_ctor_get(v_inst_4111_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4113_);
    crate::leanh::lean_dec_ref(v_inst_4111_);
    v___f_4114_ = crate::leanh::lean_alloc_closure(
        l_Lean_modifyTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4114_, 0, v_f_4112_);
    v___x_4115_ = crate::leanh::lean_apply_1(v_modifyTraceState_4113_, v___f_4114_);
    return v___x_4115_;
}
pub unsafe fn l_Lean_setTraceState___redArg___lam__0(
    mut v_s_4116_: *mut crate::leanh::LeanObject,
    mut v_x_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_4116_);
    return v_s_4116_;
}
pub unsafe fn l_Lean_setTraceState___redArg___lam__0___boxed(
    mut v_s_4118_: *mut crate::leanh::LeanObject,
    mut v_x_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4120_ = l_Lean_setTraceState___redArg___lam__0(v_s_4118_, v_x_4119_);
    crate::leanh::lean_dec_ref(v_x_4119_);
    crate::leanh::lean_dec_ref(v_s_4118_);
    return v_res_4120_;
}
pub unsafe fn l_Lean_setTraceState___redArg(
    mut v_inst_4121_: *mut crate::leanh::LeanObject,
    mut v_s_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4123_ = crate::leanh::lean_ctor_get(v_inst_4121_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4123_);
    crate::leanh::lean_dec_ref(v_inst_4121_);
    v___f_4124_ = crate::leanh::lean_alloc_closure(
        l_Lean_setTraceState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4124_, 0, v_s_4122_);
    v___x_4125_ = crate::leanh::lean_apply_1(v_modifyTraceState_4123_, v___f_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Lean_setTraceState(
    mut v_m_4126_: *mut crate::leanh::LeanObject,
    mut v_inst_4127_: *mut crate::leanh::LeanObject,
    mut v_s_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4129_ = crate::leanh::lean_ctor_get(v_inst_4127_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4129_);
    crate::leanh::lean_dec_ref(v_inst_4127_);
    v___f_4130_ = crate::leanh::lean_alloc_closure(
        l_Lean_setTraceState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4130_, 0, v_s_4128_);
    v___x_4131_ = crate::leanh::lean_apply_1(v_modifyTraceState_4129_, v___f_4130_);
    return v___x_4131_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(
    mut v_s_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_4133_: u64 = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_unused_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4133_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_4132_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4143_ = (!crate::leanh::lean_is_exclusive(v_s_4132_)) as u8;
                if v_isSharedCheck_4143_ == 0 {
                    v_unused_4144_ = crate::leanh::lean_ctor_get(v_s_4132_, 0);
                    crate::leanh::lean_dec(v_unused_4144_);
                    v___x_4135_ = v_s_4132_;
                    v_isShared_4136_ = v_isSharedCheck_4143_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4132_);
                    v___x_4135_ = crate::leanh::lean_box(0);
                    v_isShared_4136_ = v_isSharedCheck_4143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4137_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_4138_ = lean_mk_empty_array_with_capacity(v___x_4137_);
                crate::leanh::lean_dec_ref(v___x_4138_);
                v___x_4139_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instInhabitedTraceState_default___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_instInhabitedTraceState_default___closed__1_once
                    ),
                    _init_l_Lean_instInhabitedTraceState_default___closed__1,
                );
                if v_isShared_4136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4139_);
                    v___x_4141_ = v___x_4135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4142_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_toPure_4145_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4146_: *mut crate::leanh::LeanObject,
    mut v_____r_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ =
        crate::leanh::lean_apply_2(v_toPure_4145_, crate::leanh::lean_box(0), v_oldTraces_4146_);
    return v___x_4148_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(
    mut v_toPure_4149_: *mut crate::leanh::LeanObject,
    mut v_modifyTraceState_4150_: *mut crate::leanh::LeanObject,
    mut v___f_4151_: *mut crate::leanh::LeanObject,
    mut v_toBind_4152_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4154_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4154_, 0, v_toPure_4149_);
    crate::leanh::lean_closure_set(v___f_4154_, 1, v_oldTraces_4153_);
    v___x_4155_ = crate::leanh::lean_apply_1(v_modifyTraceState_4150_, v___f_4151_);
    v___x_4156_ = crate::leanh::lean_apply_4(
        v_toBind_4152_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4155_,
        v___f_4154_,
    );
    return v___x_4156_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
    mut v_inst_4158_: *mut crate::leanh::LeanObject,
    mut v_inst_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4160_ = crate::leanh::lean_ctor_get(v_inst_4158_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4160_);
    v_toBind_4161_ = crate::leanh::lean_ctor_get(v_inst_4158_, 1);
    crate::leanh::lean_inc_n(v_toBind_4161_, 3);
    crate::leanh::lean_dec_ref(v_inst_4158_);
    v_modifyTraceState_4162_ = crate::leanh::lean_ctor_get(v_inst_4159_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4162_);
    v_getTraceState_4163_ = crate::leanh::lean_ctor_get(v_inst_4159_, 1);
    crate::leanh::lean_inc(v_getTraceState_4163_);
    crate::leanh::lean_dec_ref(v_inst_4159_);
    v_toPure_4164_ = crate::leanh::lean_ctor_get(v_toApplicative_4160_, 1);
    crate::leanh::lean_inc_n(v_toPure_4164_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_4160_);
    v___f_4165_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0;
    v___f_4166_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4166_, 0, v_toPure_4164_);
    crate::leanh::lean_closure_set(v___f_4166_, 1, v_modifyTraceState_4162_);
    crate::leanh::lean_closure_set(v___f_4166_, 2, v___f_4165_);
    crate::leanh::lean_closure_set(v___f_4166_, 3, v_toBind_4161_);
    v___f_4167_ = crate::leanh::lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4167_, 0, v_toPure_4164_);
    v___x_4168_ = crate::leanh::lean_apply_4(
        v_toBind_4161_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getTraceState_4163_,
        v___f_4167_,
    );
    v___x_4169_ = crate::leanh::lean_apply_4(
        v_toBind_4161_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4168_,
        v___f_4166_,
    );
    return v___x_4169_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces(
    mut v_m_4170_: *mut crate::leanh::LeanObject,
    mut v_inst_4171_: *mut crate::leanh::LeanObject,
    mut v_inst_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4173_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_4171_, v_inst_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Lean_addRawTrace___redArg___lam__0(
    mut v_ref_4174_: *mut crate::leanh::LeanObject,
    mut v_msg_4175_: *mut crate::leanh::LeanObject,
    mut v_s_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_4177_: u64 = 0;
    let mut v_traces_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4177_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_4176_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4178_ = crate::leanh::lean_ctor_get(v_s_4176_, 0);
                v_isSharedCheck_4187_ = (!crate::leanh::lean_is_exclusive(v_s_4176_)) as u8;
                if v_isSharedCheck_4187_ == 0 {
                    v___x_4180_ = v_s_4176_;
                    v_isShared_4181_ = v_isSharedCheck_4187_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4178_);
                    crate::leanh::lean_dec(v_s_4176_);
                    v___x_4180_ = crate::leanh::lean_box(0);
                    v_isShared_4181_ = v_isSharedCheck_4187_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4182_, 0, v_ref_4174_);
                crate::leanh::lean_ctor_set(v___x_4182_, 1, v_msg_4175_);
                v___x_4183_ = l_Lean_PersistentArray_push___redArg(v_traces_4178_, v___x_4182_);
                if v_isShared_4181_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4180_, 0, v___x_4183_);
                    v___x_4185_ = v___x_4180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4186_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4186_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_inst_4188_: *mut crate::leanh::LeanObject,
    mut v_ref_4189_: *mut crate::leanh::LeanObject,
    mut v_msg_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4191_ = crate::leanh::lean_ctor_get(v_inst_4188_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4191_);
    crate::leanh::lean_dec_ref(v_inst_4188_);
    v___f_4192_ = crate::leanh::lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4192_, 0, v_ref_4189_);
    crate::leanh::lean_closure_set(v___f_4192_, 1, v_msg_4190_);
    v___x_4193_ = crate::leanh::lean_apply_1(v_modifyTraceState_4191_, v___f_4192_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_addRawTrace___redArg___lam__2(
    mut v_inst_4194_: *mut crate::leanh::LeanObject,
    mut v_inst_4195_: *mut crate::leanh::LeanObject,
    mut v_msg_4196_: *mut crate::leanh::LeanObject,
    mut v_toBind_4197_: *mut crate::leanh::LeanObject,
    mut v_ref_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4199_ = crate::leanh::lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4199_, 0, v_inst_4194_);
    crate::leanh::lean_closure_set(v___f_4199_, 1, v_ref_4198_);
    v___x_4200_ = crate::leanh::lean_apply_1(v_inst_4195_, v_msg_4196_);
    v___x_4201_ = crate::leanh::lean_apply_4(
        v_toBind_4197_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4200_,
        v___f_4199_,
    );
    return v___x_4201_;
}
pub unsafe fn l_Lean_addRawTrace___redArg(
    mut v_inst_4202_: *mut crate::leanh::LeanObject,
    mut v_inst_4203_: *mut crate::leanh::LeanObject,
    mut v_inst_4204_: *mut crate::leanh::LeanObject,
    mut v_inst_4205_: *mut crate::leanh::LeanObject,
    mut v_msg_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4207_ = crate::leanh::lean_ctor_get(v_inst_4202_, 1);
    crate::leanh::lean_inc_n(v_toBind_4207_, 2);
    crate::leanh::lean_dec_ref(v_inst_4202_);
    v_getRef_4208_ = crate::leanh::lean_ctor_get(v_inst_4204_, 0);
    crate::leanh::lean_inc(v_getRef_4208_);
    crate::leanh::lean_dec_ref(v_inst_4204_);
    v___f_4209_ = crate::leanh::lean_alloc_closure(
        l_Lean_addRawTrace___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4209_, 0, v_inst_4203_);
    crate::leanh::lean_closure_set(v___f_4209_, 1, v_inst_4205_);
    crate::leanh::lean_closure_set(v___f_4209_, 2, v_msg_4206_);
    crate::leanh::lean_closure_set(v___f_4209_, 3, v_toBind_4207_);
    v___x_4210_ = crate::leanh::lean_apply_4(
        v_toBind_4207_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_4208_,
        v___f_4209_,
    );
    return v___x_4210_;
}
pub unsafe fn l_Lean_addRawTrace(
    mut v_m_4211_: *mut crate::leanh::LeanObject,
    mut v_inst_4212_: *mut crate::leanh::LeanObject,
    mut v_inst_4213_: *mut crate::leanh::LeanObject,
    mut v_inst_4214_: *mut crate::leanh::LeanObject,
    mut v_inst_4215_: *mut crate::leanh::LeanObject,
    mut v_msg_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: f64 = 0.0;
    v___x_4218_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4219_ = lean_float_of_nat(v___x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Lean_addTrace___redArg___lam__0(
    mut v_cls_4223_: *mut crate::leanh::LeanObject,
    mut v_msg_4224_: *mut crate::leanh::LeanObject,
    mut v_ref_4225_: *mut crate::leanh::LeanObject,
    mut v_s_4226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_4227_: u64 = 0;
    let mut v_traces_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: f64 = 0.0;
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4227_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_4226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4228_ = crate::leanh::lean_ctor_get(v_s_4226_, 0);
                v_isSharedCheck_4244_ = (!crate::leanh::lean_is_exclusive(v_s_4226_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4230_ = v_s_4226_;
                    v_isShared_4231_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4228_);
                    crate::leanh::lean_dec(v_s_4226_);
                    v___x_4230_ = crate::leanh::lean_box(0);
                    v_isShared_4231_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4232_ = crate::leanh::lean_box(0);
                v___x_4233_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                v___x_4234_ = 0;
                v___x_4235_ = l_Lean_addTrace___redArg___lam__0___closed__1;
                v___x_4236_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4236_, 0, v_cls_4223_);
                crate::leanh::lean_ctor_set(v___x_4236_, 1, v___x_4232_);
                crate::leanh::lean_ctor_set(v___x_4236_, 2, v___x_4235_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4236_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4233_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4236_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4233_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4236_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4234_,
                );
                v___x_4237_ = l_Lean_addTrace___redArg___lam__0___closed__2;
                v___x_4238_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4238_, 0, v___x_4236_);
                crate::leanh::lean_ctor_set(v___x_4238_, 1, v_msg_4224_);
                crate::leanh::lean_ctor_set(v___x_4238_, 2, v___x_4237_);
                v___x_4239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4239_, 0, v_ref_4225_);
                crate::leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                v___x_4240_ = l_Lean_PersistentArray_push___redArg(v_traces_4228_, v___x_4239_);
                if v_isShared_4231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4230_, 0, v___x_4240_);
                    v___x_4242_ = v___x_4230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_inst_4245_: *mut crate::leanh::LeanObject,
    mut v_cls_4246_: *mut crate::leanh::LeanObject,
    mut v_ref_4247_: *mut crate::leanh::LeanObject,
    mut v_msg_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyTraceState_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyTraceState_4249_ = crate::leanh::lean_ctor_get(v_inst_4245_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4249_);
    crate::leanh::lean_dec_ref(v_inst_4245_);
    v___f_4250_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4250_, 0, v_cls_4246_);
    crate::leanh::lean_closure_set(v___f_4250_, 1, v_msg_4248_);
    crate::leanh::lean_closure_set(v___f_4250_, 2, v_ref_4247_);
    v___x_4251_ = crate::leanh::lean_apply_1(v_modifyTraceState_4249_, v___f_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_addTrace___redArg___lam__2(
    mut v_inst_4252_: *mut crate::leanh::LeanObject,
    mut v_cls_4253_: *mut crate::leanh::LeanObject,
    mut v_inst_4254_: *mut crate::leanh::LeanObject,
    mut v_msg_4255_: *mut crate::leanh::LeanObject,
    mut v_toBind_4256_: *mut crate::leanh::LeanObject,
    mut v_ref_4257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4258_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4258_, 0, v_inst_4252_);
    crate::leanh::lean_closure_set(v___f_4258_, 1, v_cls_4253_);
    crate::leanh::lean_closure_set(v___f_4258_, 2, v_ref_4257_);
    v___x_4259_ = crate::leanh::lean_apply_1(v_inst_4254_, v_msg_4255_);
    v___x_4260_ = crate::leanh::lean_apply_4(
        v_toBind_4256_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4259_,
        v___f_4258_,
    );
    return v___x_4260_;
}
pub unsafe fn l_Lean_addTrace___redArg(
    mut v_inst_4261_: *mut crate::leanh::LeanObject,
    mut v_inst_4262_: *mut crate::leanh::LeanObject,
    mut v_inst_4263_: *mut crate::leanh::LeanObject,
    mut v_inst_4264_: *mut crate::leanh::LeanObject,
    mut v_cls_4265_: *mut crate::leanh::LeanObject,
    mut v_msg_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4267_ = crate::leanh::lean_ctor_get(v_inst_4261_, 1);
    crate::leanh::lean_inc_n(v_toBind_4267_, 2);
    crate::leanh::lean_dec_ref(v_inst_4261_);
    v_getRef_4268_ = crate::leanh::lean_ctor_get(v_inst_4263_, 0);
    crate::leanh::lean_inc(v_getRef_4268_);
    crate::leanh::lean_dec_ref(v_inst_4263_);
    v___f_4269_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTrace___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4269_, 0, v_inst_4262_);
    crate::leanh::lean_closure_set(v___f_4269_, 1, v_cls_4265_);
    crate::leanh::lean_closure_set(v___f_4269_, 2, v_inst_4264_);
    crate::leanh::lean_closure_set(v___f_4269_, 3, v_msg_4266_);
    crate::leanh::lean_closure_set(v___f_4269_, 4, v_toBind_4267_);
    v___x_4270_ = crate::leanh::lean_apply_4(
        v_toBind_4267_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_4268_,
        v___f_4269_,
    );
    return v___x_4270_;
}
pub unsafe fn l_Lean_addTrace(
    mut v_m_4271_: *mut crate::leanh::LeanObject,
    mut v_inst_4272_: *mut crate::leanh::LeanObject,
    mut v_inst_4273_: *mut crate::leanh::LeanObject,
    mut v_inst_4274_: *mut crate::leanh::LeanObject,
    mut v_inst_4275_: *mut crate::leanh::LeanObject,
    mut v_cls_4276_: *mut crate::leanh::LeanObject,
    mut v_msg_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toPure_4279_: *mut crate::leanh::LeanObject,
    mut v_msg_4280_: *mut crate::leanh::LeanObject,
    mut v_inst_4281_: *mut crate::leanh::LeanObject,
    mut v_inst_4282_: *mut crate::leanh::LeanObject,
    mut v_inst_4283_: *mut crate::leanh::LeanObject,
    mut v_inst_4284_: *mut crate::leanh::LeanObject,
    mut v_cls_4285_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4286_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_4286_ == 0 {
        let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_4285_);
        crate::leanh::lean_dec(v_inst_4284_);
        crate::leanh::lean_dec_ref(v_inst_4283_);
        crate::leanh::lean_dec_ref(v_inst_4282_);
        crate::leanh::lean_dec_ref(v_inst_4281_);
        crate::leanh::lean_dec_ref(v_msg_4280_);
        v___x_4287_ = crate::leanh::lean_box(0);
        v___x_4288_ =
            crate::leanh::lean_apply_2(v_toPure_4279_, crate::leanh::lean_box(0), v___x_4287_);
        return v___x_4288_;
    } else {
        let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4279_);
        v___x_4289_ = crate::leanh::lean_box(0);
        v___x_4290_ = crate::leanh::lean_apply_1(v_msg_4280_, v___x_4289_);
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
    mut v_toPure_4292_: *mut crate::leanh::LeanObject,
    mut v_msg_4293_: *mut crate::leanh::LeanObject,
    mut v_inst_4294_: *mut crate::leanh::LeanObject,
    mut v_inst_4295_: *mut crate::leanh::LeanObject,
    mut v_inst_4296_: *mut crate::leanh::LeanObject,
    mut v_inst_4297_: *mut crate::leanh::LeanObject,
    mut v_cls_4298_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_148__boxed_4300_: u8 = 0;
    let mut v_res_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_148__boxed_4300_ = (crate::leanh::lean_unbox(v_____do__lift_4299_) as u8);
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
    mut v_inst_4302_: *mut crate::leanh::LeanObject,
    mut v_inst_4303_: *mut crate::leanh::LeanObject,
    mut v_inst_4304_: *mut crate::leanh::LeanObject,
    mut v_inst_4305_: *mut crate::leanh::LeanObject,
    mut v_inst_4306_: *mut crate::leanh::LeanObject,
    mut v_cls_4307_: *mut crate::leanh::LeanObject,
    mut v_msg_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4309_ = crate::leanh::lean_ctor_get(v_inst_4302_, 0);
    v_toBind_4310_ = crate::leanh::lean_ctor_get(v_inst_4302_, 1);
    crate::leanh::lean_inc_n(v_toBind_4310_, 3);
    v_getInheritedTraceOptions_4311_ = crate::leanh::lean_ctor_get(v_inst_4303_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4311_);
    v_toPure_4312_ = crate::leanh::lean_ctor_get(v_toApplicative_4309_, 1);
    crate::leanh::lean_inc_n(v_toPure_4312_, 2);
    crate::leanh::lean_inc(v_cls_4307_);
    v___f_4313_ = crate::leanh::lean_alloc_closure(
        l_Lean_trace___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4313_, 0, v_toPure_4312_);
    crate::leanh::lean_closure_set(v___f_4313_, 1, v_msg_4308_);
    crate::leanh::lean_closure_set(v___f_4313_, 2, v_inst_4302_);
    crate::leanh::lean_closure_set(v___f_4313_, 3, v_inst_4303_);
    crate::leanh::lean_closure_set(v___f_4313_, 4, v_inst_4304_);
    crate::leanh::lean_closure_set(v___f_4313_, 5, v_inst_4305_);
    crate::leanh::lean_closure_set(v___f_4313_, 6, v_cls_4307_);
    v___f_4314_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4314_, 0, v_toPure_4312_);
    crate::leanh::lean_closure_set(v___f_4314_, 1, v_cls_4307_);
    crate::leanh::lean_closure_set(v___f_4314_, 2, v_toBind_4310_);
    crate::leanh::lean_closure_set(v___f_4314_, 3, v_inst_4306_);
    v___x_4315_ = crate::leanh::lean_apply_4(
        v_toBind_4310_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4311_,
        v___f_4314_,
    );
    v___x_4316_ = crate::leanh::lean_apply_4(
        v_toBind_4310_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4315_,
        v___f_4313_,
    );
    return v___x_4316_;
}
pub unsafe fn l_Lean_trace(
    mut v_m_4317_: *mut crate::leanh::LeanObject,
    mut v_inst_4318_: *mut crate::leanh::LeanObject,
    mut v_inst_4319_: *mut crate::leanh::LeanObject,
    mut v_inst_4320_: *mut crate::leanh::LeanObject,
    mut v_inst_4321_: *mut crate::leanh::LeanObject,
    mut v_inst_4322_: *mut crate::leanh::LeanObject,
    mut v_cls_4323_: *mut crate::leanh::LeanObject,
    mut v_msg_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4325_ = crate::leanh::lean_ctor_get(v_inst_4318_, 0);
    v_toBind_4326_ = crate::leanh::lean_ctor_get(v_inst_4318_, 1);
    crate::leanh::lean_inc_n(v_toBind_4326_, 3);
    v_getInheritedTraceOptions_4327_ = crate::leanh::lean_ctor_get(v_inst_4319_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4327_);
    v_toPure_4328_ = crate::leanh::lean_ctor_get(v_toApplicative_4325_, 1);
    crate::leanh::lean_inc_n(v_toPure_4328_, 2);
    crate::leanh::lean_inc(v_cls_4323_);
    v___f_4329_ = crate::leanh::lean_alloc_closure(
        l_Lean_trace___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4329_, 0, v_toPure_4328_);
    crate::leanh::lean_closure_set(v___f_4329_, 1, v_msg_4324_);
    crate::leanh::lean_closure_set(v___f_4329_, 2, v_inst_4318_);
    crate::leanh::lean_closure_set(v___f_4329_, 3, v_inst_4319_);
    crate::leanh::lean_closure_set(v___f_4329_, 4, v_inst_4320_);
    crate::leanh::lean_closure_set(v___f_4329_, 5, v_inst_4321_);
    crate::leanh::lean_closure_set(v___f_4329_, 6, v_cls_4323_);
    v___f_4330_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4330_, 0, v_toPure_4328_);
    crate::leanh::lean_closure_set(v___f_4330_, 1, v_cls_4323_);
    crate::leanh::lean_closure_set(v___f_4330_, 2, v_toBind_4326_);
    crate::leanh::lean_closure_set(v___f_4330_, 3, v_inst_4322_);
    v___x_4331_ = crate::leanh::lean_apply_4(
        v_toBind_4326_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4327_,
        v___f_4330_,
    );
    v___x_4332_ = crate::leanh::lean_apply_4(
        v_toBind_4326_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4331_,
        v___f_4329_,
    );
    return v___x_4332_;
}
pub unsafe fn l_Lean_traceM___redArg___lam__0(
    mut v_inst_4333_: *mut crate::leanh::LeanObject,
    mut v_inst_4334_: *mut crate::leanh::LeanObject,
    mut v_inst_4335_: *mut crate::leanh::LeanObject,
    mut v_inst_4336_: *mut crate::leanh::LeanObject,
    mut v_cls_4337_: *mut crate::leanh::LeanObject,
    mut v_msg_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toPure_4340_: *mut crate::leanh::LeanObject,
    mut v_toBind_4341_: *mut crate::leanh::LeanObject,
    mut v_mkMsg_4342_: *mut crate::leanh::LeanObject,
    mut v___f_4343_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4344_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_4344_ == 0 {
        let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_4343_);
        crate::leanh::lean_dec(v_mkMsg_4342_);
        crate::leanh::lean_dec(v_toBind_4341_);
        v___x_4345_ = crate::leanh::lean_box(0);
        v___x_4346_ =
            crate::leanh::lean_apply_2(v_toPure_4340_, crate::leanh::lean_box(0), v___x_4345_);
        return v___x_4346_;
    } else {
        let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4340_);
        v___x_4347_ = crate::leanh::lean_apply_4(
            v_toBind_4341_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_mkMsg_4342_,
            v___f_4343_,
        );
        return v___x_4347_;
    }
}
pub unsafe fn l_Lean_traceM___redArg___lam__1___boxed(
    mut v_toPure_4348_: *mut crate::leanh::LeanObject,
    mut v_toBind_4349_: *mut crate::leanh::LeanObject,
    mut v_mkMsg_4350_: *mut crate::leanh::LeanObject,
    mut v___f_4351_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_154__boxed_4353_: u8 = 0;
    let mut v_res_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_154__boxed_4353_ = (crate::leanh::lean_unbox(v_____do__lift_4352_) as u8);
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
    mut v_inst_4355_: *mut crate::leanh::LeanObject,
    mut v_inst_4356_: *mut crate::leanh::LeanObject,
    mut v_inst_4357_: *mut crate::leanh::LeanObject,
    mut v_inst_4358_: *mut crate::leanh::LeanObject,
    mut v_inst_4359_: *mut crate::leanh::LeanObject,
    mut v_cls_4360_: *mut crate::leanh::LeanObject,
    mut v_mkMsg_4361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4362_ = crate::leanh::lean_ctor_get(v_inst_4355_, 0);
    v_toBind_4363_ = crate::leanh::lean_ctor_get(v_inst_4355_, 1);
    crate::leanh::lean_inc_n(v_toBind_4363_, 4);
    v_getInheritedTraceOptions_4364_ = crate::leanh::lean_ctor_get(v_inst_4356_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4364_);
    v_toPure_4365_ = crate::leanh::lean_ctor_get(v_toApplicative_4362_, 1);
    crate::leanh::lean_inc_n(v_toPure_4365_, 2);
    crate::leanh::lean_inc(v_cls_4360_);
    v___f_4366_ = crate::leanh::lean_alloc_closure(
        l_Lean_traceM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4366_, 0, v_inst_4355_);
    crate::leanh::lean_closure_set(v___f_4366_, 1, v_inst_4356_);
    crate::leanh::lean_closure_set(v___f_4366_, 2, v_inst_4357_);
    crate::leanh::lean_closure_set(v___f_4366_, 3, v_inst_4358_);
    crate::leanh::lean_closure_set(v___f_4366_, 4, v_cls_4360_);
    v___f_4367_ = crate::leanh::lean_alloc_closure(
        l_Lean_traceM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4367_, 0, v_toPure_4365_);
    crate::leanh::lean_closure_set(v___f_4367_, 1, v_toBind_4363_);
    crate::leanh::lean_closure_set(v___f_4367_, 2, v_mkMsg_4361_);
    crate::leanh::lean_closure_set(v___f_4367_, 3, v___f_4366_);
    v___f_4368_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4368_, 0, v_toPure_4365_);
    crate::leanh::lean_closure_set(v___f_4368_, 1, v_cls_4360_);
    crate::leanh::lean_closure_set(v___f_4368_, 2, v_toBind_4363_);
    crate::leanh::lean_closure_set(v___f_4368_, 3, v_inst_4359_);
    v___x_4369_ = crate::leanh::lean_apply_4(
        v_toBind_4363_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4364_,
        v___f_4368_,
    );
    v___x_4370_ = crate::leanh::lean_apply_4(
        v_toBind_4363_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4369_,
        v___f_4367_,
    );
    return v___x_4370_;
}
pub unsafe fn l_Lean_traceM(
    mut v_m_4371_: *mut crate::leanh::LeanObject,
    mut v_inst_4372_: *mut crate::leanh::LeanObject,
    mut v_inst_4373_: *mut crate::leanh::LeanObject,
    mut v_inst_4374_: *mut crate::leanh::LeanObject,
    mut v_inst_4375_: *mut crate::leanh::LeanObject,
    mut v_inst_4376_: *mut crate::leanh::LeanObject,
    mut v_cls_4377_: *mut crate::leanh::LeanObject,
    mut v_mkMsg_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4379_ = crate::leanh::lean_ctor_get(v_inst_4372_, 0);
    v_toBind_4380_ = crate::leanh::lean_ctor_get(v_inst_4372_, 1);
    crate::leanh::lean_inc_n(v_toBind_4380_, 4);
    v_getInheritedTraceOptions_4381_ = crate::leanh::lean_ctor_get(v_inst_4373_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_4381_);
    v_toPure_4382_ = crate::leanh::lean_ctor_get(v_toApplicative_4379_, 1);
    crate::leanh::lean_inc_n(v_toPure_4382_, 2);
    crate::leanh::lean_inc(v_cls_4377_);
    v___f_4383_ = crate::leanh::lean_alloc_closure(
        l_Lean_traceM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4383_, 0, v_inst_4372_);
    crate::leanh::lean_closure_set(v___f_4383_, 1, v_inst_4373_);
    crate::leanh::lean_closure_set(v___f_4383_, 2, v_inst_4374_);
    crate::leanh::lean_closure_set(v___f_4383_, 3, v_inst_4375_);
    crate::leanh::lean_closure_set(v___f_4383_, 4, v_cls_4377_);
    v___f_4384_ = crate::leanh::lean_alloc_closure(
        l_Lean_traceM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4384_, 0, v_toPure_4382_);
    crate::leanh::lean_closure_set(v___f_4384_, 1, v_toBind_4380_);
    crate::leanh::lean_closure_set(v___f_4384_, 2, v_mkMsg_4378_);
    crate::leanh::lean_closure_set(v___f_4384_, 3, v___f_4383_);
    v___f_4385_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4385_, 0, v_toPure_4382_);
    crate::leanh::lean_closure_set(v___f_4385_, 1, v_cls_4377_);
    crate::leanh::lean_closure_set(v___f_4385_, 2, v_toBind_4380_);
    crate::leanh::lean_closure_set(v___f_4385_, 3, v_inst_4376_);
    v___x_4386_ = crate::leanh::lean_apply_4(
        v_toBind_4380_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_4381_,
        v___f_4385_,
    );
    v___x_4387_ = crate::leanh::lean_apply_4(
        v_toBind_4380_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4386_,
        v___f_4384_,
    );
    return v___x_4387_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(
    mut v_x_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msg_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_msg_4389_ = crate::leanh::lean_ctor_get(v_x_4388_, 1);
    crate::leanh::lean_inc_ref(v_msg_4389_);
    return v_msg_4389_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(
    mut v_x_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_4390_);
    crate::leanh::lean_dec_ref(v_x_4390_);
    return v_res_4391_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(
    mut v_ref_4392_: *mut crate::leanh::LeanObject,
    mut v_msg_4393_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4394_: *mut crate::leanh::LeanObject,
    mut v_s_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_4396_: u64 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_4396_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4405_ = (!crate::leanh::lean_is_exclusive(v_s_4395_)) as u8;
                if v_isSharedCheck_4405_ == 0 {
                    v_unused_4406_ = crate::leanh::lean_ctor_get(v_s_4395_, 0);
                    crate::leanh::lean_dec(v_unused_4406_);
                    v___x_4398_ = v_s_4395_;
                    v_isShared_4399_ = v_isSharedCheck_4405_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4395_);
                    v___x_4398_ = crate::leanh::lean_box(0);
                    v_isShared_4399_ = v_isSharedCheck_4405_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4400_, 0, v_ref_4392_);
                crate::leanh::lean_ctor_set(v___x_4400_, 1, v_msg_4393_);
                v___x_4401_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4394_, v___x_4400_);
                if v_isShared_4399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4398_, 0, v___x_4401_);
                    v___x_4403_ = v___x_4398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4404_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4404_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_ref_4407_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4408_: *mut crate::leanh::LeanObject,
    mut v_modifyTraceState_4409_: *mut crate::leanh::LeanObject,
    mut v_msg_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4411_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4411_, 0, v_ref_4407_);
    crate::leanh::lean_closure_set(v___f_4411_, 1, v_msg_4410_);
    crate::leanh::lean_closure_set(v___f_4411_, 2, v_oldTraces_4408_);
    v___x_4412_ = crate::leanh::lean_apply_1(v_modifyTraceState_4409_, v___f_4411_);
    return v___x_4412_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(
    mut v___f_4432_: *mut crate::leanh::LeanObject,
    mut v_data_4433_: *mut crate::leanh::LeanObject,
    mut v_msg_4434_: *mut crate::leanh::LeanObject,
    mut v_inst_4435_: *mut crate::leanh::LeanObject,
    mut v_toBind_4436_: *mut crate::leanh::LeanObject,
    mut v___f_4437_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4441_: usize = 0;
    let mut v___x_4442_: usize = 0;
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_4438_);
    v___x_4440_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9;
    v_sz_4441_ = lean_array_size(v___x_4439_);
    v___x_4442_ = 0usize;
    v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4440_,
        v___f_4432_,
        v_sz_4441_,
        v___x_4442_,
        v___x_4439_,
    );
    v_msg_4444_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v_msg_4444_, 0, v_data_4433_);
    crate::leanh::lean_ctor_set(v_msg_4444_, 1, v_msg_4434_);
    crate::leanh::lean_ctor_set(v_msg_4444_, 2, v___x_4443_);
    v___x_4445_ = crate::leanh::lean_apply_1(v_inst_4435_, v_msg_4444_);
    v___x_4446_ = crate::leanh::lean_apply_4(
        v_toBind_4436_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4445_,
        v___f_4437_,
    );
    return v___x_4446_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(
    mut v___f_4447_: *mut crate::leanh::LeanObject,
    mut v_data_4448_: *mut crate::leanh::LeanObject,
    mut v_msg_4449_: *mut crate::leanh::LeanObject,
    mut v_inst_4450_: *mut crate::leanh::LeanObject,
    mut v_toBind_4451_: *mut crate::leanh::LeanObject,
    mut v___f_4452_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4454_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(
        v___f_4447_,
        v_data_4448_,
        v_msg_4449_,
        v_inst_4450_,
        v_toBind_4451_,
        v___f_4452_,
        v_____do__lift_4453_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_4453_);
    return v_res_4454_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(
    mut v_ref_4455_: *mut crate::leanh::LeanObject,
    mut v_withRef_4456_: *mut crate::leanh::LeanObject,
    mut v___x_4457_: *mut crate::leanh::LeanObject,
    mut v_oldRef_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4459_ = l_Lean_replaceRef(v_ref_4455_, v_oldRef_4458_);
    v___x_4460_ = crate::leanh::lean_apply_3(
        v_withRef_4456_,
        crate::leanh::lean_box(0),
        v_ref_4459_,
        v___x_4457_,
    );
    return v___x_4460_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(
    mut v_ref_4461_: *mut crate::leanh::LeanObject,
    mut v_withRef_4462_: *mut crate::leanh::LeanObject,
    mut v___x_4463_: *mut crate::leanh::LeanObject,
    mut v_oldRef_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(
        v_ref_4461_,
        v_withRef_4462_,
        v___x_4463_,
        v_oldRef_4464_,
    );
    crate::leanh::lean_dec(v_oldRef_4464_);
    crate::leanh::lean_dec(v_ref_4461_);
    return v_res_4465_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(
    mut v_inst_4467_: *mut crate::leanh::LeanObject,
    mut v_inst_4468_: *mut crate::leanh::LeanObject,
    mut v_inst_4469_: *mut crate::leanh::LeanObject,
    mut v_inst_4470_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4471_: *mut crate::leanh::LeanObject,
    mut v_data_4472_: *mut crate::leanh::LeanObject,
    mut v_ref_4473_: *mut crate::leanh::LeanObject,
    mut v_msg_4474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTraceState_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4475_ = crate::leanh::lean_ctor_get(v_inst_4467_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4475_);
    v_toBind_4476_ = crate::leanh::lean_ctor_get(v_inst_4467_, 1);
    crate::leanh::lean_inc_n(v_toBind_4476_, 4);
    crate::leanh::lean_dec_ref(v_inst_4467_);
    v_modifyTraceState_4477_ = crate::leanh::lean_ctor_get(v_inst_4468_, 0);
    crate::leanh::lean_inc(v_modifyTraceState_4477_);
    v_getTraceState_4478_ = crate::leanh::lean_ctor_get(v_inst_4468_, 1);
    crate::leanh::lean_inc(v_getTraceState_4478_);
    crate::leanh::lean_dec_ref(v_inst_4468_);
    v_toPure_4479_ = crate::leanh::lean_ctor_get(v_toApplicative_4475_, 1);
    crate::leanh::lean_inc(v_toPure_4479_);
    crate::leanh::lean_dec_ref(v_toApplicative_4475_);
    v_getRef_4480_ = crate::leanh::lean_ctor_get(v_inst_4469_, 0);
    crate::leanh::lean_inc(v_getRef_4480_);
    v_withRef_4481_ = crate::leanh::lean_ctor_get(v_inst_4469_, 1);
    crate::leanh::lean_inc(v_withRef_4481_);
    crate::leanh::lean_dec_ref(v_inst_4469_);
    v___f_4482_ = crate::leanh::lean_alloc_closure(
        l_Lean_getTraces___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4482_, 0, v_toPure_4479_);
    v___x_4483_ = crate::leanh::lean_apply_4(
        v_toBind_4476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getTraceState_4478_,
        v___f_4482_,
    );
    v___f_4484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0;
    crate::leanh::lean_inc(v_ref_4473_);
    v___f_4485_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4485_, 0, v_ref_4473_);
    crate::leanh::lean_closure_set(v___f_4485_, 1, v_oldTraces_4471_);
    crate::leanh::lean_closure_set(v___f_4485_, 2, v_modifyTraceState_4477_);
    v___f_4486_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4486_, 0, v___f_4484_);
    crate::leanh::lean_closure_set(v___f_4486_, 1, v_data_4472_);
    crate::leanh::lean_closure_set(v___f_4486_, 2, v_msg_4474_);
    crate::leanh::lean_closure_set(v___f_4486_, 3, v_inst_4470_);
    crate::leanh::lean_closure_set(v___f_4486_, 4, v_toBind_4476_);
    crate::leanh::lean_closure_set(v___f_4486_, 5, v___f_4485_);
    v___x_4487_ = crate::leanh::lean_apply_4(
        v_toBind_4476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4483_,
        v___f_4486_,
    );
    v___f_4488_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4488_, 0, v_ref_4473_);
    crate::leanh::lean_closure_set(v___f_4488_, 1, v_withRef_4481_);
    crate::leanh::lean_closure_set(v___f_4488_, 2, v___x_4487_);
    v___x_4489_ = crate::leanh::lean_apply_4(
        v_toBind_4476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_4480_,
        v___f_4488_,
    );
    return v___x_4489_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode(
    mut v_m_4490_: *mut crate::leanh::LeanObject,
    mut v_inst_4491_: *mut crate::leanh::LeanObject,
    mut v_inst_4492_: *mut crate::leanh::LeanObject,
    mut v_inst_4493_: *mut crate::leanh::LeanObject,
    mut v_inst_4494_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_4495_: *mut crate::leanh::LeanObject,
    mut v_data_4496_: *mut crate::leanh::LeanObject,
    mut v_ref_4497_: *mut crate::leanh::LeanObject,
    mut v_msg_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_name_4500_: *mut crate::leanh::LeanObject,
    mut v_decl_4501_: *mut crate::leanh::LeanObject,
    mut v_ref_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4518_: u8 = 0;
    let mut v_unused_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4504_ = crate::leanh::lean_ctor_get(v_decl_4501_, 0);
                v_descr_4505_ = crate::leanh::lean_ctor_get(v_decl_4501_, 1);
                v_deprecation_x3f_4506_ = crate::leanh::lean_ctor_get(v_decl_4501_, 2);
                v___x_4507_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4508_ = (crate::leanh::lean_unbox(v_defValue_4504_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_4507_, 0 as u32, v___x_4508_);
                crate::leanh::lean_inc(v_deprecation_x3f_4506_);
                crate::leanh::lean_inc_ref(v_descr_4505_);
                crate::leanh::lean_inc_n(v_name_4500_, 2);
                v___x_4509_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4509_, 0, v_name_4500_);
                crate::leanh::lean_ctor_set(v___x_4509_, 1, v_ref_4502_);
                crate::leanh::lean_ctor_set(v___x_4509_, 2, v___x_4507_);
                crate::leanh::lean_ctor_set(v___x_4509_, 3, v_descr_4505_);
                crate::leanh::lean_ctor_set(v___x_4509_, 4, v_deprecation_x3f_4506_);
                v___x_4510_ = lean_register_option(v_name_4500_, v___x_4509_);
                if crate::leanh::lean_obj_tag(v___x_4510_) == 0 {
                    v_isSharedCheck_4518_ = (!crate::leanh::lean_is_exclusive(v___x_4510_)) as u8;
                    if v_isSharedCheck_4518_ == 0 {
                        v_unused_4519_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                        crate::leanh::lean_dec(v_unused_4519_);
                        v___x_4512_ = v___x_4510_;
                        v_isShared_4513_ = v_isSharedCheck_4518_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4510_);
                        v___x_4512_ = crate::leanh::lean_box(0);
                        v_isShared_4513_ = v_isSharedCheck_4518_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4500_);
                    v_a_4520_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                    v_isSharedCheck_4527_ = (!crate::leanh::lean_is_exclusive(v___x_4510_)) as u8;
                    if v_isSharedCheck_4527_ == 0 {
                        v___x_4522_ = v___x_4510_;
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4520_);
                        crate::leanh::lean_dec(v___x_4510_);
                        v___x_4522_ = crate::leanh::lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_4504_);
                v___x_4514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4514_, 0, v_name_4500_);
                crate::leanh::lean_ctor_set(v___x_4514_, 1, v_defValue_4504_);
                if v_isShared_4513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
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
                    v_reuseFailAlloc_4526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
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
    mut v_name_4528_: *mut crate::leanh::LeanObject,
    mut v_decl_4529_: *mut crate::leanh::LeanObject,
    mut v_ref_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_4528_, v_decl_4529_, v_ref_4530_);
    crate::leanh::lean_dec_ref(v_decl_4529_);
    return v_res_4532_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4548_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4549_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4550_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_;
    v___x_4551_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4548_, v___x_4549_, v___x_4550_);
    return v___x_4551_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(
    mut v_a_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4553_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
    return v_res_4553_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(
    mut v_name_4554_: *mut crate::leanh::LeanObject,
    mut v_decl_4555_: *mut crate::leanh::LeanObject,
    mut v_ref_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_unused_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4576_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4558_ = crate::leanh::lean_ctor_get(v_decl_4555_, 0);
                v_descr_4559_ = crate::leanh::lean_ctor_get(v_decl_4555_, 1);
                v_deprecation_x3f_4560_ = crate::leanh::lean_ctor_get(v_decl_4555_, 2);
                crate::leanh::lean_inc(v_defValue_4558_);
                v___x_4561_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4561_, 0, v_defValue_4558_);
                crate::leanh::lean_inc(v_deprecation_x3f_4560_);
                crate::leanh::lean_inc_ref(v_descr_4559_);
                crate::leanh::lean_inc_n(v_name_4554_, 2);
                v___x_4562_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4562_, 0, v_name_4554_);
                crate::leanh::lean_ctor_set(v___x_4562_, 1, v_ref_4556_);
                crate::leanh::lean_ctor_set(v___x_4562_, 2, v___x_4561_);
                crate::leanh::lean_ctor_set(v___x_4562_, 3, v_descr_4559_);
                crate::leanh::lean_ctor_set(v___x_4562_, 4, v_deprecation_x3f_4560_);
                v___x_4563_ = lean_register_option(v_name_4554_, v___x_4562_);
                if crate::leanh::lean_obj_tag(v___x_4563_) == 0 {
                    v_isSharedCheck_4571_ = (!crate::leanh::lean_is_exclusive(v___x_4563_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v_unused_4572_ = crate::leanh::lean_ctor_get(v___x_4563_, 0);
                        crate::leanh::lean_dec(v_unused_4572_);
                        v___x_4565_ = v___x_4563_;
                        v_isShared_4566_ = v_isSharedCheck_4571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4563_);
                        v___x_4565_ = crate::leanh::lean_box(0);
                        v_isShared_4566_ = v_isSharedCheck_4571_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4554_);
                    v_a_4573_ = crate::leanh::lean_ctor_get(v___x_4563_, 0);
                    v_isSharedCheck_4580_ = (!crate::leanh::lean_is_exclusive(v___x_4563_)) as u8;
                    if v_isSharedCheck_4580_ == 0 {
                        v___x_4575_ = v___x_4563_;
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4573_);
                        crate::leanh::lean_dec(v___x_4563_);
                        v___x_4575_ = crate::leanh::lean_box(0);
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_4558_);
                v___x_4567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4567_, 0, v_name_4554_);
                crate::leanh::lean_ctor_set(v___x_4567_, 1, v_defValue_4558_);
                if v_isShared_4566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4565_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
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
                    v_reuseFailAlloc_4579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
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
    mut v_name_4581_: *mut crate::leanh::LeanObject,
    mut v_decl_4582_: *mut crate::leanh::LeanObject,
    mut v_ref_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_4581_, v_decl_4582_, v_ref_4583_);
    crate::leanh::lean_dec_ref(v_decl_4582_);
    return v_res_4585_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4602_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4603_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_;
    v___x_4605_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_4602_, v___x_4603_, v___x_4604_);
    return v___x_4605_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(
    mut v_a_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4607_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
    return v_res_4607_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4626_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4627_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_;
    v___x_4628_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4625_, v___x_4626_, v___x_4627_);
    return v___x_4628_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(
    mut v_a_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
    return v_res_4630_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(
    mut v_name_4631_: *mut crate::leanh::LeanObject,
    mut v_decl_4632_: *mut crate::leanh::LeanObject,
    mut v_ref_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v_unused_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4635_ = crate::leanh::lean_ctor_get(v_decl_4632_, 0);
                v_descr_4636_ = crate::leanh::lean_ctor_get(v_decl_4632_, 1);
                v_deprecation_x3f_4637_ = crate::leanh::lean_ctor_get(v_decl_4632_, 2);
                crate::leanh::lean_inc(v_defValue_4635_);
                v___x_4638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4638_, 0, v_defValue_4635_);
                crate::leanh::lean_inc(v_deprecation_x3f_4637_);
                crate::leanh::lean_inc_ref(v_descr_4636_);
                crate::leanh::lean_inc_n(v_name_4631_, 2);
                v___x_4639_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4639_, 0, v_name_4631_);
                crate::leanh::lean_ctor_set(v___x_4639_, 1, v_ref_4633_);
                crate::leanh::lean_ctor_set(v___x_4639_, 2, v___x_4638_);
                crate::leanh::lean_ctor_set(v___x_4639_, 3, v_descr_4636_);
                crate::leanh::lean_ctor_set(v___x_4639_, 4, v_deprecation_x3f_4637_);
                v___x_4640_ = lean_register_option(v_name_4631_, v___x_4639_);
                if crate::leanh::lean_obj_tag(v___x_4640_) == 0 {
                    v_isSharedCheck_4648_ = (!crate::leanh::lean_is_exclusive(v___x_4640_)) as u8;
                    if v_isSharedCheck_4648_ == 0 {
                        v_unused_4649_ = crate::leanh::lean_ctor_get(v___x_4640_, 0);
                        crate::leanh::lean_dec(v_unused_4649_);
                        v___x_4642_ = v___x_4640_;
                        v_isShared_4643_ = v_isSharedCheck_4648_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4640_);
                        v___x_4642_ = crate::leanh::lean_box(0);
                        v_isShared_4643_ = v_isSharedCheck_4648_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4631_);
                    v_a_4650_ = crate::leanh::lean_ctor_get(v___x_4640_, 0);
                    v_isSharedCheck_4657_ = (!crate::leanh::lean_is_exclusive(v___x_4640_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4652_ = v___x_4640_;
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4650_);
                        crate::leanh::lean_dec(v___x_4640_);
                        v___x_4652_ = crate::leanh::lean_box(0);
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_4635_);
                v___x_4644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4644_, 0, v_name_4631_);
                crate::leanh::lean_ctor_set(v___x_4644_, 1, v_defValue_4635_);
                if v_isShared_4643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4642_, 0, v___x_4644_);
                    v___x_4646_ = v___x_4642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
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
                    v_reuseFailAlloc_4656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
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
    mut v_name_4658_: *mut crate::leanh::LeanObject,
    mut v_decl_4659_: *mut crate::leanh::LeanObject,
    mut v_ref_4660_: *mut crate::leanh::LeanObject,
    mut v_a_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_4658_, v_decl_4659_, v_ref_4660_);
    crate::leanh::lean_dec_ref(v_decl_4659_);
    return v_res_4662_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4681_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_;
    v___x_4682_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_4679_, v___x_4680_, v___x_4681_);
    return v___x_4682_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(
    mut v_a_4683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4684_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
    return v_res_4684_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4702_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4703_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4704_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_;
    v___x_4705_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4702_, v___x_4703_, v___x_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(
    mut v_a_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
    return v_res_4707_;
}
pub unsafe fn l_Lean_trace_profiler_isExporting(
    mut v_opts_4708_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l_Lean_KVMap_instValueBool;
    v___x_4710_ = l_Lean_KVMap_instValueString;
    v___x_4711_ = l_Lean_trace_profiler_output;
    v___x_4712_ = l_Lean_Option_get_x3f___redArg(v___x_4710_, v_opts_4708_, v___x_4711_);
    if crate::leanh::lean_obj_tag(v___x_4712_) == 0 {
        let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4715_: u8 = 0;
        v___x_4713_ = l_Lean_trace_profiler_serve;
        v___x_4714_ = l_Lean_Option_get___redArg(v___x_4709_, v_opts_4708_, v___x_4713_);
        v___x_4715_ = (crate::leanh::lean_unbox(v___x_4714_) as u8);
        crate::leanh::lean_dec(v___x_4714_);
        return v___x_4715_;
    } else {
        let mut v___x_4716_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_4712_, 1);
        v___x_4716_ = 1;
        return v___x_4716_;
    }
}
pub unsafe fn l_Lean_trace_profiler_isExporting___boxed(
    mut v_opts_4717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4718_: u8 = 0;
    let mut v_r_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4718_ = l_Lean_trace_profiler_isExporting(v_opts_4717_);
    crate::leanh::lean_dec_ref(v_opts_4717_);
    v_r_4719_ = crate::leanh::lean_box((v_res_4718_) as usize);
    return v_r_4719_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4740_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4741_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_;
    v___x_4742_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_4739_, v___x_4740_, v___x_4741_);
    return v___x_4742_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(
    mut v_a_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4744_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
    return v_res_4744_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0()
-> f64 {
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: f64 = 0.0;
    v___x_4745_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_4746_ = lean_float_of_nat(v___x_4745_);
    return v___x_4746_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(
    mut v_toApplicative_4747_: *mut crate::leanh::LeanObject,
    mut v_start_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_stop_4750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: f64 = 0.0;
    let mut v___x_4753_: f64 = 0.0;
    let mut v___x_4754_: f64 = 0.0;
    let mut v___x_4755_: f64 = 0.0;
    let mut v___x_4756_: f64 = 0.0;
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4751_ = crate::leanh::lean_ctor_get(v_toApplicative_4747_, 1);
    crate::leanh::lean_inc(v_toPure_4751_);
    crate::leanh::lean_dec_ref(v_toApplicative_4747_);
    v___x_4752_ = lean_float_of_nat(v_start_4748_);
    v___x_4753_ = crate::leanh::lean_float_once(
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
    v___x_4757_ = crate::leanh::lean_box_float(v___x_4754_);
    v___x_4758_ = crate::leanh::lean_box_float(v___x_4756_);
    v___x_4759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4759_, 0, v___x_4757_);
    crate::leanh::lean_ctor_set(v___x_4759_, 1, v___x_4758_);
    v___x_4760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4760_, 0, v_a_4749_);
    crate::leanh::lean_ctor_set(v___x_4760_, 1, v___x_4759_);
    v___x_4761_ =
        crate::leanh::lean_apply_2(v_toPure_4751_, crate::leanh::lean_box(0), v___x_4760_);
    return v___x_4761_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(
    mut v_toApplicative_4762_: *mut crate::leanh::LeanObject,
    mut v_start_4763_: *mut crate::leanh::LeanObject,
    mut v_toBind_4764_: *mut crate::leanh::LeanObject,
    mut v___x_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4767_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4767_, 0, v_toApplicative_4762_);
    crate::leanh::lean_closure_set(v___f_4767_, 1, v_start_4763_);
    crate::leanh::lean_closure_set(v___f_4767_, 2, v_a_4766_);
    v___x_4768_ = crate::leanh::lean_apply_4(
        v_toBind_4764_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4765_,
        v___f_4767_,
    );
    return v___x_4768_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(
    mut v_toApplicative_4769_: *mut crate::leanh::LeanObject,
    mut v_toBind_4770_: *mut crate::leanh::LeanObject,
    mut v___x_4771_: *mut crate::leanh::LeanObject,
    mut v_act_4772_: *mut crate::leanh::LeanObject,
    mut v_start_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_4770_);
    v___f_4774_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4774_, 0, v_toApplicative_4769_);
    crate::leanh::lean_closure_set(v___f_4774_, 1, v_start_4773_);
    crate::leanh::lean_closure_set(v___f_4774_, 2, v_toBind_4770_);
    crate::leanh::lean_closure_set(v___f_4774_, 3, v___x_4771_);
    v___x_4775_ = crate::leanh::lean_apply_4(
        v_toBind_4770_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_act_4772_,
        v___f_4774_,
    );
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(
    mut v_toApplicative_4776_: *mut crate::leanh::LeanObject,
    mut v_start_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_stop_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: f64 = 0.0;
    let mut v___x_4782_: f64 = 0.0;
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4780_ = crate::leanh::lean_ctor_get(v_toApplicative_4776_, 1);
    crate::leanh::lean_inc(v_toPure_4780_);
    crate::leanh::lean_dec_ref(v_toApplicative_4776_);
    v___x_4781_ = lean_float_of_nat(v_start_4777_);
    v___x_4782_ = lean_float_of_nat(v_stop_4779_);
    v___x_4783_ = crate::leanh::lean_box_float(v___x_4781_);
    v___x_4784_ = crate::leanh::lean_box_float(v___x_4782_);
    v___x_4785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4785_, 0, v___x_4783_);
    crate::leanh::lean_ctor_set(v___x_4785_, 1, v___x_4784_);
    v___x_4786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4786_, 0, v_a_4778_);
    crate::leanh::lean_ctor_set(v___x_4786_, 1, v___x_4785_);
    v___x_4787_ =
        crate::leanh::lean_apply_2(v_toPure_4780_, crate::leanh::lean_box(0), v___x_4786_);
    return v___x_4787_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(
    mut v_toApplicative_4788_: *mut crate::leanh::LeanObject,
    mut v_start_4789_: *mut crate::leanh::LeanObject,
    mut v_toBind_4790_: *mut crate::leanh::LeanObject,
    mut v___x_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4793_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4793_, 0, v_toApplicative_4788_);
    crate::leanh::lean_closure_set(v___f_4793_, 1, v_start_4789_);
    crate::leanh::lean_closure_set(v___f_4793_, 2, v_a_4792_);
    v___x_4794_ = crate::leanh::lean_apply_4(
        v_toBind_4790_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4791_,
        v___f_4793_,
    );
    return v___x_4794_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(
    mut v_toApplicative_4795_: *mut crate::leanh::LeanObject,
    mut v_toBind_4796_: *mut crate::leanh::LeanObject,
    mut v___x_4797_: *mut crate::leanh::LeanObject,
    mut v_act_4798_: *mut crate::leanh::LeanObject,
    mut v_start_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_4796_);
    v___f_4800_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4800_, 0, v_toApplicative_4795_);
    crate::leanh::lean_closure_set(v___f_4800_, 1, v_start_4799_);
    crate::leanh::lean_closure_set(v___f_4800_, 2, v_toBind_4796_);
    crate::leanh::lean_closure_set(v___f_4800_, 3, v___x_4797_);
    v___x_4801_ = crate::leanh::lean_apply_4(
        v_toBind_4796_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_act_4798_,
        v___f_4800_,
    );
    return v___x_4801_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(
    mut v_inst_4804_: *mut crate::leanh::LeanObject,
    mut v_inst_4805_: *mut crate::leanh::LeanObject,
    mut v_opts_4806_: *mut crate::leanh::LeanObject,
    mut v_act_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    v___x_4808_ = l_Lean_KVMap_instValueBool;
    v___x_4809_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4810_ = l_Lean_Option_get___redArg(v___x_4808_, v_opts_4806_, v___x_4809_);
    v___x_4811_ = (crate::leanh::lean_unbox(v___x_4810_) as u8);
    crate::leanh::lean_dec(v___x_4810_);
    if v___x_4811_ == 0 {
        let mut v_toApplicative_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4812_ = crate::leanh::lean_ctor_get(v_inst_4804_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4812_);
        v_toBind_4813_ = crate::leanh::lean_ctor_get(v_inst_4804_, 1);
        crate::leanh::lean_inc_n(v_toBind_4813_, 2);
        crate::leanh::lean_dec_ref(v_inst_4804_);
        v___x_4814_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_4815_ =
            crate::leanh::lean_apply_2(v_inst_4805_, crate::leanh::lean_box(0), v___x_4814_);
        crate::leanh::lean_inc(v___x_4815_);
        v___f_4816_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4816_, 0, v_toApplicative_4812_);
        crate::leanh::lean_closure_set(v___f_4816_, 1, v_toBind_4813_);
        crate::leanh::lean_closure_set(v___f_4816_, 2, v___x_4815_);
        crate::leanh::lean_closure_set(v___f_4816_, 3, v_act_4807_);
        v___x_4817_ = crate::leanh::lean_apply_4(
            v_toBind_4813_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4815_,
            v___f_4816_,
        );
        return v___x_4817_;
    } else {
        let mut v_toApplicative_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4818_ = crate::leanh::lean_ctor_get(v_inst_4804_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4818_);
        v_toBind_4819_ = crate::leanh::lean_ctor_get(v_inst_4804_, 1);
        crate::leanh::lean_inc_n(v_toBind_4819_, 2);
        crate::leanh::lean_dec_ref(v_inst_4804_);
        v___x_4820_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_4821_ =
            crate::leanh::lean_apply_2(v_inst_4805_, crate::leanh::lean_box(0), v___x_4820_);
        crate::leanh::lean_inc(v___x_4821_);
        v___f_4822_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4822_, 0, v_toApplicative_4818_);
        crate::leanh::lean_closure_set(v___f_4822_, 1, v_toBind_4819_);
        crate::leanh::lean_closure_set(v___f_4822_, 2, v___x_4821_);
        crate::leanh::lean_closure_set(v___f_4822_, 3, v_act_4807_);
        v___x_4823_ = crate::leanh::lean_apply_4(
            v_toBind_4819_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4821_,
            v___f_4822_,
        );
        return v___x_4823_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(
    mut v_inst_4824_: *mut crate::leanh::LeanObject,
    mut v_inst_4825_: *mut crate::leanh::LeanObject,
    mut v_opts_4826_: *mut crate::leanh::LeanObject,
    mut v_act_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4828_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(
        v_inst_4824_,
        v_inst_4825_,
        v_opts_4826_,
        v_act_4827_,
    );
    crate::leanh::lean_dec_ref(v_opts_4826_);
    return v_res_4828_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop(
    mut v_00_u03b1_4829_: *mut crate::leanh::LeanObject,
    mut v_m_4830_: *mut crate::leanh::LeanObject,
    mut v_inst_4831_: *mut crate::leanh::LeanObject,
    mut v_inst_4832_: *mut crate::leanh::LeanObject,
    mut v_opts_4833_: *mut crate::leanh::LeanObject,
    mut v_act_4834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: u8 = 0;
    v___x_4835_ = l_Lean_KVMap_instValueBool;
    v___x_4836_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4837_ = l_Lean_Option_get___redArg(v___x_4835_, v_opts_4833_, v___x_4836_);
    v___x_4838_ = (crate::leanh::lean_unbox(v___x_4837_) as u8);
    crate::leanh::lean_dec(v___x_4837_);
    if v___x_4838_ == 0 {
        let mut v_toApplicative_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4839_ = crate::leanh::lean_ctor_get(v_inst_4831_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4839_);
        v_toBind_4840_ = crate::leanh::lean_ctor_get(v_inst_4831_, 1);
        crate::leanh::lean_inc_n(v_toBind_4840_, 2);
        crate::leanh::lean_dec_ref(v_inst_4831_);
        v___x_4841_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_4842_ =
            crate::leanh::lean_apply_2(v_inst_4832_, crate::leanh::lean_box(0), v___x_4841_);
        crate::leanh::lean_inc(v___x_4842_);
        v___f_4843_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4843_, 0, v_toApplicative_4839_);
        crate::leanh::lean_closure_set(v___f_4843_, 1, v_toBind_4840_);
        crate::leanh::lean_closure_set(v___f_4843_, 2, v___x_4842_);
        crate::leanh::lean_closure_set(v___f_4843_, 3, v_act_4834_);
        v___x_4844_ = crate::leanh::lean_apply_4(
            v_toBind_4840_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4842_,
            v___f_4843_,
        );
        return v___x_4844_;
    } else {
        let mut v_toApplicative_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4845_ = crate::leanh::lean_ctor_get(v_inst_4831_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4845_);
        v_toBind_4846_ = crate::leanh::lean_ctor_get(v_inst_4831_, 1);
        crate::leanh::lean_inc_n(v_toBind_4846_, 2);
        crate::leanh::lean_dec_ref(v_inst_4831_);
        v___x_4847_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_4848_ =
            crate::leanh::lean_apply_2(v_inst_4832_, crate::leanh::lean_box(0), v___x_4847_);
        crate::leanh::lean_inc(v___x_4848_);
        v___f_4849_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4849_, 0, v_toApplicative_4845_);
        crate::leanh::lean_closure_set(v___f_4849_, 1, v_toBind_4846_);
        crate::leanh::lean_closure_set(v___f_4849_, 2, v___x_4848_);
        crate::leanh::lean_closure_set(v___f_4849_, 3, v_act_4834_);
        v___x_4850_ = crate::leanh::lean_apply_4(
            v_toBind_4846_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4848_,
            v___f_4849_,
        );
        return v___x_4850_;
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(
    mut v_00_u03b1_4851_: *mut crate::leanh::LeanObject,
    mut v_m_4852_: *mut crate::leanh::LeanObject,
    mut v_inst_4853_: *mut crate::leanh::LeanObject,
    mut v_inst_4854_: *mut crate::leanh::LeanObject,
    mut v_opts_4855_: *mut crate::leanh::LeanObject,
    mut v_act_4856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(
        v_00_u03b1_4851_,
        v_m_4852_,
        v_inst_4853_,
        v_inst_4854_,
        v_opts_4855_,
        v_act_4856_,
    );
    crate::leanh::lean_dec_ref(v_opts_4855_);
    return v_res_4857_;
}
pub unsafe fn _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0() -> f64 {
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: f64 = 0.0;
    v___x_4858_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4859_ = lean_float_of_nat(v___x_4858_);
    return v___x_4859_;
}
pub unsafe fn l_Lean_trace_profiler_threshold_unitAdjusted(
    mut v_o_4860_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: u8 = 0;
    v___x_4861_ = l_Lean_KVMap_instValueBool;
    v___x_4862_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_4863_ = l_Lean_Option_get___redArg(v___x_4861_, v_o_4860_, v___x_4862_);
    v___x_4864_ = (crate::leanh::lean_unbox(v___x_4863_) as u8);
    crate::leanh::lean_dec(v___x_4863_);
    if v___x_4864_ == 0 {
        let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4868_: f64 = 0.0;
        let mut v___x_4869_: f64 = 0.0;
        let mut v___x_4870_: f64 = 0.0;
        v___x_4865_ = l_Lean_KVMap_instValueNat;
        v___x_4866_ = l_Lean_trace_profiler_threshold;
        v___x_4867_ = l_Lean_Option_get___redArg(v___x_4865_, v_o_4860_, v___x_4866_);
        v___x_4868_ = lean_float_of_nat(v___x_4867_);
        v___x_4869_ = crate::leanh::lean_float_once(
            core::ptr::addr_of_mut!(l_Lean_trace_profiler_threshold_unitAdjusted___closed__0),
            core::ptr::addr_of_mut!(l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once),
            _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0,
        );
        v___x_4870_ = lean_float_div(v___x_4868_, v___x_4869_);
        return v___x_4870_;
    } else {
        let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4874_: f64 = 0.0;
        v___x_4871_ = l_Lean_KVMap_instValueNat;
        v___x_4872_ = l_Lean_trace_profiler_threshold;
        v___x_4873_ = l_Lean_Option_get___redArg(v___x_4871_, v_o_4860_, v___x_4872_);
        v___x_4874_ = lean_float_of_nat(v___x_4873_);
        return v___x_4874_;
    }
}
pub unsafe fn l_Lean_trace_profiler_threshold_unitAdjusted___boxed(
    mut v_o_4875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4876_: f64 = 0.0;
    let mut v_r_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4876_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_4875_);
    crate::leanh::lean_dec_ref(v_o_4875_);
    v_r_4877_ = crate::leanh::lean_box_float(v_res_4876_);
    return v_r_4877_;
}
pub unsafe fn _init_l_Lean_instMonadAlwaysExceptEIO___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4878_ = l_instMonadExceptOfEIO(crate::leanh::lean_box(0));
    return v___x_4878_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptEIO(
    mut v_00_u03b5_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instMonadAlwaysExceptEIO___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instMonadAlwaysExceptEIO___closed__0_once),
        _init_l_Lean_instMonadAlwaysExceptEIO___closed__0,
    );
    return v___x_4880_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateT___redArg(
    mut v_inst_4881_: *mut crate::leanh::LeanObject,
    mut v_always_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_always_4882_);
    v___f_4883_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4883_, 0, v_always_4882_);
    crate::leanh::lean_closure_set(v___f_4883_, 1, v_inst_4881_);
    v___f_4884_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonadExceptOf___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4884_, 0, v_always_4882_);
    v___x_4885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4885_, 0, v___f_4883_);
    crate::leanh::lean_ctor_set(v___x_4885_, 1, v___f_4884_);
    return v___x_4885_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateT(
    mut v_m_4886_: *mut crate::leanh::LeanObject,
    mut v_inst_4887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4888_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4889_: *mut crate::leanh::LeanObject,
    mut v_always_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_4887_, v_always_4890_);
    return v___x_4891_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(
    mut v_always_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_always_4892_);
    v___f_4893_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4893_, 0, v_always_4892_);
    v___f_4894_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4894_, 0, v_always_4892_);
    v___x_4895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4895_, 0, v___f_4893_);
    crate::leanh::lean_ctor_set(v___x_4895_, 1, v___f_4894_);
    return v___x_4895_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptStateRefT_x27(
    mut v_m_4896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4897_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_4898_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4899_: *mut crate::leanh::LeanObject,
    mut v_always_4900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_4900_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptReaderT___redArg(
    mut v_always_4902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_always_4902_);
    v___f_4903_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4903_, 0, v_always_4902_);
    v___f_4904_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4904_, 0, v_always_4902_);
    v___x_4905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4905_, 0, v___f_4903_);
    crate::leanh::lean_ctor_set(v___x_4905_, 1, v___f_4904_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptReaderT(
    mut v_m_4906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4907_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4908_: *mut crate::leanh::LeanObject,
    mut v_always_4909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4910_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_4909_);
    return v___x_4910_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(
    mut v_always_4911_: *mut crate::leanh::LeanObject,
    mut v_inst_4912_: *mut crate::leanh::LeanObject,
    mut v_inst_4913_: *mut crate::leanh::LeanObject,
    mut v_inst_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4915_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_4912_,
        v_inst_4913_,
        v_inst_4914_,
        v_always_4911_,
    );
    return v___x_4915_;
}
pub unsafe fn l_Lean_instMonadAlwaysExceptMonadCacheT(
    mut v_00_u03b1_4916_: *mut crate::leanh::LeanObject,
    mut v_m_4917_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4918_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_4919_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4920_: *mut crate::leanh::LeanObject,
    mut v_always_4921_: *mut crate::leanh::LeanObject,
    mut v_inst_4922_: *mut crate::leanh::LeanObject,
    mut v_inst_4923_: *mut crate::leanh::LeanObject,
    mut v_inst_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4925_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_4922_,
        v_inst_4923_,
        v_inst_4924_,
        v_always_4921_,
    );
    return v___x_4925_;
}
pub unsafe fn l_Lean_TraceResult_toEmoji(mut v_x_4932_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4932_ {
        0 => {
            let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4933_ = l_Lean_checkEmoji___closed__0;
            return v___x_4933_;
        }
        1 => {
            let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4934_ = l_Lean_crossEmoji___closed__0;
            return v___x_4934_;
        }
        _ => {
            let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4935_ = l_Lean_bombEmoji___closed__0;
            return v___x_4935_;
        }
    }
}
pub unsafe fn l_Lean_TraceResult_toEmoji___boxed(
    mut v_x_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_31__boxed_4937_: u8 = 0;
    let mut v_res_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_31__boxed_4937_ = (crate::leanh::lean_unbox(v_x_4936_) as u8);
    v_res_4938_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_4937_);
    return v_res_4938_;
}
pub unsafe fn l_Lean_instExceptToTraceResultBool___lam__0(
    mut v_x_4939_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4939_) == 0 {
        let mut v___x_4940_: u8 = 0;
        v___x_4940_ = 2;
        return v___x_4940_;
    } else {
        let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: u8 = 0;
        v_a_4941_ = crate::leanh::lean_ctor_get(v_x_4939_, 0);
        v___x_4942_ = (crate::leanh::lean_unbox(v_a_4941_) as u8);
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
    mut v_x_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4946_: u8 = 0;
    let mut v_r_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_4945_);
    crate::leanh::lean_dec_ref(v_x_4945_);
    v_r_4947_ = crate::leanh::lean_box((v_res_4946_) as usize);
    return v_r_4947_;
}
pub unsafe fn l_Lean_instExceptToTraceResultBool(
    mut v_00_u03b5_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4950_ = l_Lean_instExceptToTraceResultBool___closed__0;
    return v___f_4950_;
}
pub unsafe fn l_Lean_instExceptToTraceResultOption___lam__0(
    mut v_x_4951_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4951_) == 0 {
        let mut v___x_4952_: u8 = 0;
        v___x_4952_ = 2;
        return v___x_4952_;
    } else {
        let mut v_a_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4953_ = crate::leanh::lean_ctor_get(v_x_4951_, 0);
        if crate::leanh::lean_obj_tag(v_a_4953_) == 0 {
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
    mut v_x_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: u8 = 0;
    let mut v_r_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_4956_);
    crate::leanh::lean_dec_ref(v_x_4956_);
    v_r_4958_ = crate::leanh::lean_box((v_res_4957_) as usize);
    return v_r_4958_;
}
pub unsafe fn l_Lean_instExceptToTraceResultOption(
    mut v_00_u03b1_4960_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4962_ = l_Lean_instExceptToTraceResultOption___closed__0;
    return v___f_4962_;
}
pub unsafe fn l_Lean_instExceptToTraceResultExpr___lam__0(
    mut v_x_4963_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4963_) == 0 {
        let mut v___x_4964_: u8 = 0;
        v___x_4964_ = 2;
        return v___x_4964_;
    } else {
        let mut v_a_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: u8 = 0;
        v_a_4965_ = crate::leanh::lean_ctor_get(v_x_4963_, 0);
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
    mut v_x_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4970_: u8 = 0;
    let mut v_r_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_4969_);
    crate::leanh::lean_dec_ref(v_x_4969_);
    v_r_4971_ = crate::leanh::lean_box((v_res_4970_) as usize);
    return v_r_4971_;
}
pub unsafe fn l_Lean_instExceptToTraceResultExpr(
    mut v_00_u03b5_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4974_ = l_Lean_instExceptToTraceResultExpr___closed__0;
    return v___f_4974_;
}
pub unsafe fn l_Lean_instExceptToTraceResult___lam__0(
    mut v_x_4975_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4975_) == 0 {
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
    mut v_x_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4979_: u8 = 0;
    let mut v_r_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_instExceptToTraceResult___lam__0(v_x_4978_);
    crate::leanh::lean_dec_ref(v_x_4978_);
    v_r_4980_ = crate::leanh::lean_box((v_res_4979_) as usize);
    return v_r_4980_;
}
pub unsafe fn l_Lean_instExceptToTraceResult(
    mut v_00_u03b1_4982_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4984_ = l_Lean_instExceptToTraceResult___closed__0;
    return v___f_4984_;
}
pub unsafe fn l_Except_toTraceResult___redArg(
    mut v_inst_4985_: *mut crate::leanh::LeanObject,
    mut v_e_4986_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    v___x_4987_ = crate::leanh::lean_apply_1(v_inst_4985_, v_e_4986_);
    v___x_4988_ = (crate::leanh::lean_unbox(v___x_4987_) as u8);
    return v___x_4988_;
}
pub unsafe fn l_Except_toTraceResult___redArg___boxed(
    mut v_inst_4989_: *mut crate::leanh::LeanObject,
    mut v_e_4990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4991_: u8 = 0;
    let mut v_r_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4991_ = l_Except_toTraceResult___redArg(v_inst_4989_, v_e_4990_);
    v_r_4992_ = crate::leanh::lean_box((v_res_4991_) as usize);
    return v_r_4992_;
}
pub unsafe fn l_Except_toTraceResult(
    mut v_00_u03b1_4993_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_4994_: *mut crate::leanh::LeanObject,
    mut v_inst_4995_: *mut crate::leanh::LeanObject,
    mut v_e_4996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    v___x_4997_ = crate::leanh::lean_apply_1(v_inst_4995_, v_e_4996_);
    v___x_4998_ = (crate::leanh::lean_unbox(v___x_4997_) as u8);
    return v___x_4998_;
}
pub unsafe fn l_Except_toTraceResult___boxed(
    mut v_00_u03b1_4999_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_5000_: *mut crate::leanh::LeanObject,
    mut v_inst_5001_: *mut crate::leanh::LeanObject,
    mut v_e_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5003_: u8 = 0;
    let mut v_r_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5003_ =
        l_Except_toTraceResult(v_00_u03b1_4999_, v_00_u03b5_5000_, v_inst_5001_, v_e_5002_);
    v_r_5004_ = crate::leanh::lean_box((v_res_5003_) as usize);
    return v_r_5004_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5006_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0;
    v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
    return v___x_5007_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(
    mut v_inst_5008_: *mut crate::leanh::LeanObject,
    mut v_x_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5010_ = crate::leanh::lean_ctor_get(v_inst_5008_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5010_);
    crate::leanh::lean_dec_ref(v_inst_5008_);
    v_toPure_5011_ = crate::leanh::lean_ctor_get(v_toApplicative_5010_, 1);
    crate::leanh::lean_inc(v_toPure_5011_);
    crate::leanh::lean_dec_ref(v_toApplicative_5010_);
    v___x_5012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
    v___x_5013_ =
        crate::leanh::lean_apply_2(v_toPure_5011_, crate::leanh::lean_box(0), v___x_5012_);
    return v___x_5013_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(
    mut v_inst_5014_: *mut crate::leanh::LeanObject,
    mut v_x_5015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(
        v_inst_5014_,
        v_x_5015_,
    );
    crate::leanh::lean_dec(v_x_5015_);
    return v_res_5016_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(
    mut v_oldTraces_5017_: *mut crate::leanh::LeanObject,
    mut v_s_5018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tid_5019_: u64 = 0;
    let mut v_traces_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5023_: u8 = 0;
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tid_5019_ = crate::leanh::lean_ctor_get_uint64(
                    v_s_5018_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5020_ = crate::leanh::lean_ctor_get(v_s_5018_, 0);
                v_isSharedCheck_5028_ = (!crate::leanh::lean_is_exclusive(v_s_5018_)) as u8;
                if v_isSharedCheck_5028_ == 0 {
                    v___x_5022_ = v_s_5018_;
                    v_isShared_5023_ = v_isSharedCheck_5028_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5020_);
                    crate::leanh::lean_dec(v_s_5018_);
                    v___x_5022_ = crate::leanh::lean_box(0);
                    v_isShared_5023_ = v_isSharedCheck_5028_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5024_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5017_, v_traces_5020_);
                crate::leanh::lean_dec_ref(v_traces_5020_);
                if v_isShared_5023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5022_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5027_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_always_5029_: *mut crate::leanh::LeanObject,
    mut v_inst_5030_: *mut crate::leanh::LeanObject,
    mut v_fst_5031_: *mut crate::leanh::LeanObject,
    mut v_____r_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_5029_);
    v___x_5034_ = l_MonadExcept_ofExcept___redArg(v_inst_5030_, v___x_5033_, v_fst_5031_);
    return v___x_5034_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(
    mut v_inst_5035_: *mut crate::leanh::LeanObject,
    mut v___x_5036_: *mut crate::leanh::LeanObject,
    mut v_fst_5037_: *mut crate::leanh::LeanObject,
    mut v_____r_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5039_ = l_MonadExcept_ofExcept___redArg(v_inst_5035_, v___x_5036_, v_fst_5037_);
    return v___x_5039_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0;
    v___x_5042_ = l_Lean_stringToMessageData(v___x_5041_);
    return v___x_5042_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(
    mut v_inst_5043_: *mut crate::leanh::LeanObject,
    mut v_fst_5044_: *mut crate::leanh::LeanObject,
    mut v_inst_5045_: *mut crate::leanh::LeanObject,
    mut v_inst_5046_: *mut crate::leanh::LeanObject,
    mut v_inst_5047_: *mut crate::leanh::LeanObject,
    mut v_inst_5048_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5049_: *mut crate::leanh::LeanObject,
    mut v_ref_5050_: *mut crate::leanh::LeanObject,
    mut v_toBind_5051_: *mut crate::leanh::LeanObject,
    mut v___f_5052_: *mut crate::leanh::LeanObject,
    mut v_cls_5053_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5054_: u8,
    mut v_tag_5055_: *mut crate::leanh::LeanObject,
    mut v___x_5056_: u8,
    mut v_fst_5057_: f64,
    mut v_snd_5058_: f64,
    mut v_m_5059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: f64 = 0.0;
    let mut v_data_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_5060_ = crate::leanh::lean_apply_1(v_inst_5043_, v_fst_5044_);
                v___x_5061_ = (crate::leanh::lean_unbox(v_result_5060_) as u8);
                v___x_5062_ = l_Lean_TraceResult_toEmoji(v___x_5061_);
                v___x_5063_ = l_Lean_stringToMessageData(v___x_5062_);
                v___x_5064_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
                v___x_5065_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5065_, 0, v___x_5063_);
                crate::leanh::lean_ctor_set(v___x_5065_, 1, v___x_5064_);
                v_m_5066_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_m_5066_, 0, v___x_5065_);
                crate::leanh::lean_ctor_set(v_m_5066_, 1, v_m_5059_);
                v___x_5071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5071_, 0, v_result_5060_);
                v___x_5072_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                crate::leanh::lean_inc_ref(v_tag_5055_);
                crate::leanh::lean_inc_ref(v___x_5071_);
                crate::leanh::lean_inc(v_cls_5053_);
                v_data_5073_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_5073_, 0, v_cls_5053_);
                crate::leanh::lean_ctor_set(v_data_5073_, 1, v___x_5071_);
                crate::leanh::lean_ctor_set(v_data_5073_, 2, v_tag_5055_);
                crate::leanh::lean_ctor_set_float(
                    v_data_5073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5072_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_5073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5072_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_5073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5054_,
                );
                if v___x_5056_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5071_, 1);
                    crate::leanh::lean_dec_ref(v_tag_5055_);
                    crate::leanh::lean_dec(v_cls_5053_);
                    v_data_5068_ = v_data_5073_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_5073_, 3);
                    v_data_5074_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_5074_, 0, v_cls_5053_);
                    crate::leanh::lean_ctor_set(v_data_5074_, 1, v___x_5071_);
                    crate::leanh::lean_ctor_set(v_data_5074_, 2, v_tag_5055_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_5074_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_fst_5057_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v_data_5074_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v_snd_5058_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_5074_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
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
                v___x_5070_ = crate::leanh::lean_apply_4(
                    v_toBind_5051_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5075_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_fst_5076_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5077_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5078_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5079_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5080_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_oldTraces_5081_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_ref_5082_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_toBind_5083_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_5084_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_cls_5085_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_collapsed_5086_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_tag_5087_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_5088_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_fst_5089_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_snd_5090_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_m_5091_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5092_: u8 = 0;
    let mut v___x_677__boxed_5093_: u8 = 0;
    let mut v_fst_678__boxed_5094_: f64 = 0.0;
    let mut v_snd_679__boxed_5095_: f64 = 0.0;
    let mut v_res_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5092_ = (crate::leanh::lean_unbox(v_collapsed_5086_) as u8);
    v___x_677__boxed_5093_ = (crate::leanh::lean_unbox(v___x_5088_) as u8);
    v_fst_678__boxed_5094_ = crate::leanh::lean_unbox_float(v_fst_5089_);
    crate::leanh::lean_dec_ref(v_fst_5089_);
    v_snd_679__boxed_5095_ = crate::leanh::lean_unbox_float(v_snd_5090_);
    crate::leanh::lean_dec_ref(v_snd_5090_);
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
    mut v_always_5097_: *mut crate::leanh::LeanObject,
    mut v_inst_5098_: *mut crate::leanh::LeanObject,
    mut v_fst_5099_: *mut crate::leanh::LeanObject,
    mut v_inst_5100_: *mut crate::leanh::LeanObject,
    mut v_inst_5101_: *mut crate::leanh::LeanObject,
    mut v_inst_5102_: *mut crate::leanh::LeanObject,
    mut v_inst_5103_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5104_: *mut crate::leanh::LeanObject,
    mut v_toBind_5105_: *mut crate::leanh::LeanObject,
    mut v_cls_5106_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5107_: u8,
    mut v_tag_5108_: *mut crate::leanh::LeanObject,
    mut v___x_5109_: u8,
    mut v_fst_5110_: f64,
    mut v_snd_5111_: f64,
    mut v_msg_5112_: *mut crate::leanh::LeanObject,
    mut v___f_5113_: *mut crate::leanh::LeanObject,
    mut v_ref_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_always_5097_);
    v___x_5115_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_5097_);
    v_tryCatch_5116_ = crate::leanh::lean_ctor_get(v_always_5097_, 1);
    crate::leanh::lean_inc(v_tryCatch_5116_);
    crate::leanh::lean_dec_ref(v_always_5097_);
    crate::leanh::lean_inc_ref_n(v_fst_5099_, 2);
    crate::leanh::lean_inc_ref(v_inst_5098_);
    v___f_5117_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5117_, 0, v_inst_5098_);
    crate::leanh::lean_closure_set(v___f_5117_, 1, v___x_5115_);
    crate::leanh::lean_closure_set(v___f_5117_, 2, v_fst_5099_);
    v___x_5118_ = crate::leanh::lean_box((v_collapsed_5107_) as usize);
    v___x_5119_ = crate::leanh::lean_box((v___x_5109_) as usize);
    v___x_5120_ = crate::leanh::lean_box_float(v_fst_5110_);
    v___x_5121_ = crate::leanh::lean_box_float(v_snd_5111_);
    crate::leanh::lean_inc(v_toBind_5105_);
    v___f_5122_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_5122_, 0, v_inst_5100_);
    crate::leanh::lean_closure_set(v___f_5122_, 1, v_fst_5099_);
    crate::leanh::lean_closure_set(v___f_5122_, 2, v_inst_5098_);
    crate::leanh::lean_closure_set(v___f_5122_, 3, v_inst_5101_);
    crate::leanh::lean_closure_set(v___f_5122_, 4, v_inst_5102_);
    crate::leanh::lean_closure_set(v___f_5122_, 5, v_inst_5103_);
    crate::leanh::lean_closure_set(v___f_5122_, 6, v_oldTraces_5104_);
    crate::leanh::lean_closure_set(v___f_5122_, 7, v_ref_5114_);
    crate::leanh::lean_closure_set(v___f_5122_, 8, v_toBind_5105_);
    crate::leanh::lean_closure_set(v___f_5122_, 9, v___f_5117_);
    crate::leanh::lean_closure_set(v___f_5122_, 10, v_cls_5106_);
    crate::leanh::lean_closure_set(v___f_5122_, 11, v___x_5118_);
    crate::leanh::lean_closure_set(v___f_5122_, 12, v_tag_5108_);
    crate::leanh::lean_closure_set(v___f_5122_, 13, v___x_5119_);
    crate::leanh::lean_closure_set(v___f_5122_, 14, v___x_5120_);
    crate::leanh::lean_closure_set(v___f_5122_, 15, v___x_5121_);
    v___x_5123_ = crate::leanh::lean_apply_1(v_msg_5112_, v_fst_5099_);
    v___x_5124_ = crate::leanh::lean_apply_3(
        v_tryCatch_5116_,
        crate::leanh::lean_box(0),
        v___x_5123_,
        v___f_5113_,
    );
    v___x_5125_ = crate::leanh::lean_apply_4(
        v_toBind_5105_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5124_,
        v___f_5122_,
    );
    return v___x_5125_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_always_5126_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5127_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_fst_5128_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5129_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5130_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5131_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_5132_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_oldTraces_5133_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_toBind_5134_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_cls_5135_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_collapsed_5136_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_tag_5137_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_5138_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_fst_5139_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_snd_5140_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_msg_5141_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_5142_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_ref_5143_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5144_: u8 = 0;
    let mut v___x_729__boxed_5145_: u8 = 0;
    let mut v_fst_730__boxed_5146_: f64 = 0.0;
    let mut v_snd_731__boxed_5147_: f64 = 0.0;
    let mut v_res_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5144_ = (crate::leanh::lean_unbox(v_collapsed_5136_) as u8);
    v___x_729__boxed_5145_ = (crate::leanh::lean_unbox(v___x_5138_) as u8);
    v_fst_730__boxed_5146_ = crate::leanh::lean_unbox_float(v_fst_5139_);
    crate::leanh::lean_dec_ref(v_fst_5139_);
    v_snd_731__boxed_5147_ = crate::leanh::lean_unbox_float(v_snd_5140_);
    crate::leanh::lean_dec_ref(v_snd_5140_);
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
    mut v_inst_5149_: *mut crate::leanh::LeanObject,
    mut v_inst_5150_: *mut crate::leanh::LeanObject,
    mut v_inst_5151_: *mut crate::leanh::LeanObject,
    mut v_inst_5152_: *mut crate::leanh::LeanObject,
    mut v_always_5153_: *mut crate::leanh::LeanObject,
    mut v_inst_5154_: *mut crate::leanh::LeanObject,
    mut v_cls_5155_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5156_: u8,
    mut v_tag_5157_: *mut crate::leanh::LeanObject,
    mut v_opts_5158_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5159_: u8,
    mut v_oldTraces_5160_: *mut crate::leanh::LeanObject,
    mut v_msg_5161_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: u8 = 0;
    let mut v_toBind_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: f64 = 0.0;
    let mut v___x_5187_: f64 = 0.0;
    let mut v___x_5188_: f64 = 0.0;
    let mut v___x_5189_: f64 = 0.0;
    let mut v___x_5190_: u8 = 0;
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: u8 = 0;
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: f64 = 0.0;
    let mut v___x_5200_: f64 = 0.0;
    let mut v___x_5201_: f64 = 0.0;
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: f64 = 0.0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5163_ = l_Lean_KVMap_instValueBool;
                v_snd_5164_ = crate::leanh::lean_ctor_get(v_resStartStop_5162_, 1);
                crate::leanh::lean_inc(v_snd_5164_);
                v_fst_5165_ = crate::leanh::lean_ctor_get(v_resStartStop_5162_, 0);
                crate::leanh::lean_inc_n(v_fst_5165_, 2);
                crate::leanh::lean_dec_ref(v_resStartStop_5162_);
                v_fst_5166_ = crate::leanh::lean_ctor_get(v_snd_5164_, 0);
                crate::leanh::lean_inc(v_fst_5166_);
                v_snd_5167_ = crate::leanh::lean_ctor_get(v_snd_5164_, 1);
                crate::leanh::lean_inc(v_snd_5167_);
                crate::leanh::lean_dec(v_snd_5164_);
                crate::leanh::lean_inc_ref_n(v_inst_5149_, 2);
                v___f_5168_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_5168_, 0, v_inst_5149_);
                crate::leanh::lean_inc_ref(v_oldTraces_5160_);
                v___f_5169_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5169_, 0, v_oldTraces_5160_);
                crate::leanh::lean_inc_ref(v_always_5153_);
                v___f_5170_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5170_, 0, v_always_5153_);
                crate::leanh::lean_closure_set(v___f_5170_, 1, v_inst_5149_);
                crate::leanh::lean_closure_set(v___f_5170_, 2, v_fst_5165_);
                v___x_5171_ = l_Lean_trace_profiler;
                v___x_5172_ = l_Lean_Option_get___redArg(v___x_5163_, v_opts_5158_, v___x_5171_);
                v___x_5191_ = (crate::leanh::lean_unbox(v___x_5172_) as u8);
                if v___x_5191_ == 0 {
                    v___x_5192_ = (crate::leanh::lean_unbox(v___x_5172_) as u8);
                    v___y_5180_ = v___x_5192_;
                    state = 2;
                    continue;
                } else {
                    v___x_5193_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5194_ =
                        l_Lean_Option_get___redArg(v___x_5163_, v_opts_5158_, v___x_5193_);
                    v___x_5195_ = (crate::leanh::lean_unbox(v___x_5194_) as u8);
                    crate::leanh::lean_dec(v___x_5194_);
                    if v___x_5195_ == 0 {
                        v___x_5196_ = l_Lean_KVMap_instValueNat;
                        v___x_5197_ = l_Lean_trace_profiler_threshold;
                        v___x_5198_ =
                            l_Lean_Option_get___redArg(v___x_5196_, v_opts_5158_, v___x_5197_);
                        v___x_5199_ = lean_float_of_nat(v___x_5198_);
                        v___x_5200_ = crate::leanh::lean_float_once(
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
                v_toBind_5174_ = crate::leanh::lean_ctor_get(v_inst_5149_, 1);
                crate::leanh::lean_inc_n(v_toBind_5174_, 2);
                v_getRef_5175_ = crate::leanh::lean_ctor_get(v_inst_5151_, 0);
                crate::leanh::lean_inc(v_getRef_5175_);
                v___x_5176_ = crate::leanh::lean_box((v_collapsed_5156_) as usize);
                v___f_5177_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed as *mut core::ffi::c_void, 18, 17);
                crate::leanh::lean_closure_set(v___f_5177_, 0, v_always_5153_);
                crate::leanh::lean_closure_set(v___f_5177_, 1, v_inst_5149_);
                crate::leanh::lean_closure_set(v___f_5177_, 2, v_fst_5165_);
                crate::leanh::lean_closure_set(v___f_5177_, 3, v_inst_5154_);
                crate::leanh::lean_closure_set(v___f_5177_, 4, v_inst_5150_);
                crate::leanh::lean_closure_set(v___f_5177_, 5, v_inst_5151_);
                crate::leanh::lean_closure_set(v___f_5177_, 6, v_inst_5152_);
                crate::leanh::lean_closure_set(v___f_5177_, 7, v_oldTraces_5160_);
                crate::leanh::lean_closure_set(v___f_5177_, 8, v_toBind_5174_);
                crate::leanh::lean_closure_set(v___f_5177_, 9, v_cls_5155_);
                crate::leanh::lean_closure_set(v___f_5177_, 10, v___x_5176_);
                crate::leanh::lean_closure_set(v___f_5177_, 11, v_tag_5157_);
                crate::leanh::lean_closure_set(v___f_5177_, 12, v___x_5172_);
                crate::leanh::lean_closure_set(v___f_5177_, 13, v_fst_5166_);
                crate::leanh::lean_closure_set(v___f_5177_, 14, v_snd_5167_);
                crate::leanh::lean_closure_set(v___f_5177_, 15, v_msg_5161_);
                crate::leanh::lean_closure_set(v___f_5177_, 16, v___f_5168_);
                v___x_5178_ = crate::leanh::lean_apply_4(
                    v_toBind_5174_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_5175_,
                    v___f_5177_,
                );
                return v___x_5178_;
            }
            2 => {
                if v_clsEnabled_5159_ == 0 {
                    if v___y_5180_ == 0 {
                        crate::leanh::lean_dec(v___x_5172_);
                        crate::leanh::lean_dec_ref(v___f_5168_);
                        crate::leanh::lean_dec(v_snd_5167_);
                        crate::leanh::lean_dec(v_fst_5166_);
                        crate::leanh::lean_dec(v_fst_5165_);
                        crate::leanh::lean_dec(v_msg_5161_);
                        crate::leanh::lean_dec_ref(v_oldTraces_5160_);
                        crate::leanh::lean_dec_ref(v_tag_5157_);
                        crate::leanh::lean_dec(v_cls_5155_);
                        crate::leanh::lean_dec_ref(v_inst_5154_);
                        crate::leanh::lean_dec_ref(v_always_5153_);
                        crate::leanh::lean_dec(v_inst_5152_);
                        crate::leanh::lean_dec_ref(v_inst_5151_);
                        v_toBind_5181_ = crate::leanh::lean_ctor_get(v_inst_5149_, 1);
                        crate::leanh::lean_inc(v_toBind_5181_);
                        crate::leanh::lean_dec_ref(v_inst_5149_);
                        v_modifyTraceState_5182_ = crate::leanh::lean_ctor_get(v_inst_5150_, 0);
                        crate::leanh::lean_inc(v_modifyTraceState_5182_);
                        crate::leanh::lean_dec_ref(v_inst_5150_);
                        v___x_5183_ =
                            crate::leanh::lean_apply_1(v_modifyTraceState_5182_, v___f_5169_);
                        v___x_5184_ = crate::leanh::lean_apply_4(
                            v_toBind_5181_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5183_,
                            v___f_5170_,
                        );
                        return v___x_5184_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5170_);
                        crate::leanh::lean_dec_ref(v___f_5169_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_5170_);
                    crate::leanh::lean_dec_ref(v___f_5169_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5187_ = crate::leanh::lean_unbox_float(v_snd_5167_);
                v___x_5188_ = crate::leanh::lean_unbox_float(v_fst_5166_);
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
    mut v_inst_5206_: *mut crate::leanh::LeanObject,
    mut v_inst_5207_: *mut crate::leanh::LeanObject,
    mut v_inst_5208_: *mut crate::leanh::LeanObject,
    mut v_inst_5209_: *mut crate::leanh::LeanObject,
    mut v_always_5210_: *mut crate::leanh::LeanObject,
    mut v_inst_5211_: *mut crate::leanh::LeanObject,
    mut v_cls_5212_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5213_: *mut crate::leanh::LeanObject,
    mut v_tag_5214_: *mut crate::leanh::LeanObject,
    mut v_opts_5215_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5216_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5217_: *mut crate::leanh::LeanObject,
    mut v_msg_5218_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5220_: u8 = 0;
    let mut v_clsEnabled_boxed_5221_: u8 = 0;
    let mut v_res_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5220_ = (crate::leanh::lean_unbox(v_collapsed_5213_) as u8);
    v_clsEnabled_boxed_5221_ = (crate::leanh::lean_unbox(v_clsEnabled_5216_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_5215_);
    return v_res_5222_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
    mut v_00_u03b1_5223_: *mut crate::leanh::LeanObject,
    mut v_m_5224_: *mut crate::leanh::LeanObject,
    mut v_inst_5225_: *mut crate::leanh::LeanObject,
    mut v_inst_5226_: *mut crate::leanh::LeanObject,
    mut v_inst_5227_: *mut crate::leanh::LeanObject,
    mut v_inst_5228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_5229_: *mut crate::leanh::LeanObject,
    mut v_always_5230_: *mut crate::leanh::LeanObject,
    mut v_inst_5231_: *mut crate::leanh::LeanObject,
    mut v_cls_5232_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5233_: u8,
    mut v_tag_5234_: *mut crate::leanh::LeanObject,
    mut v_opts_5235_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5236_: u8,
    mut v_oldTraces_5237_: *mut crate::leanh::LeanObject,
    mut v_msg_5238_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_5241_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_m_5242_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5243_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5244_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5245_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5246_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_00_u03b5_5247_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_always_5248_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_5249_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_cls_5250_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_collapsed_5251_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_tag_5252_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_opts_5253_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_clsEnabled_5254_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_oldTraces_5255_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_msg_5256_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_resStartStop_5257_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5258_: u8 = 0;
    let mut v_clsEnabled_boxed_5259_: u8 = 0;
    let mut v_res_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5258_ = (crate::leanh::lean_unbox(v_collapsed_5251_) as u8);
    v_clsEnabled_boxed_5259_ = (crate::leanh::lean_unbox(v_clsEnabled_5254_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_5253_);
    return v_res_5260_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__0(
    mut v_inst_5261_: *mut crate::leanh::LeanObject,
    mut v_inst_5262_: *mut crate::leanh::LeanObject,
    mut v_inst_5263_: *mut crate::leanh::LeanObject,
    mut v_inst_5264_: *mut crate::leanh::LeanObject,
    mut v_always_5265_: *mut crate::leanh::LeanObject,
    mut v_inst_5266_: *mut crate::leanh::LeanObject,
    mut v_cls_5267_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5268_: u8,
    mut v_tag_5269_: *mut crate::leanh::LeanObject,
    mut v_opts_5270_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5271_: u8,
    mut v_oldTraces_5272_: *mut crate::leanh::LeanObject,
    mut v_msg_5273_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5276_: *mut crate::leanh::LeanObject,
    mut v_inst_5277_: *mut crate::leanh::LeanObject,
    mut v_inst_5278_: *mut crate::leanh::LeanObject,
    mut v_inst_5279_: *mut crate::leanh::LeanObject,
    mut v_always_5280_: *mut crate::leanh::LeanObject,
    mut v_inst_5281_: *mut crate::leanh::LeanObject,
    mut v_cls_5282_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5283_: *mut crate::leanh::LeanObject,
    mut v_tag_5284_: *mut crate::leanh::LeanObject,
    mut v_opts_5285_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5286_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5287_: *mut crate::leanh::LeanObject,
    mut v_msg_5288_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5290_: u8 = 0;
    let mut v_clsEnabled_boxed_5291_: u8 = 0;
    let mut v_res_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5290_ = (crate::leanh::lean_unbox(v_collapsed_5283_) as u8);
    v_clsEnabled_boxed_5291_ = (crate::leanh::lean_unbox(v_clsEnabled_5286_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_5285_);
    return v_res_5292_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__1(
    mut v_toPure_5293_: *mut crate::leanh::LeanObject,
    mut v_ex_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5295_, 0, v_ex_5294_);
    v___x_5296_ =
        crate::leanh::lean_apply_2(v_toPure_5293_, crate::leanh::lean_box(0), v___x_5295_);
    return v___x_5296_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__2(
    mut v_toPure_5297_: *mut crate::leanh::LeanObject,
    mut v_a_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5299_, 0, v_a_5298_);
    v___x_5300_ =
        crate::leanh::lean_apply_2(v_toPure_5297_, crate::leanh::lean_box(0), v___x_5299_);
    return v___x_5300_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__3(
    mut v_start_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_toPure_5303_: *mut crate::leanh::LeanObject,
    mut v_stop_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5305_: f64 = 0.0;
    let mut v___x_5306_: f64 = 0.0;
    let mut v___x_5307_: f64 = 0.0;
    let mut v___x_5308_: f64 = 0.0;
    let mut v___x_5309_: f64 = 0.0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5305_ = lean_float_of_nat(v_start_5301_);
    v___x_5306_ = crate::leanh::lean_float_once(
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
    v___x_5310_ = crate::leanh::lean_box_float(v___x_5307_);
    v___x_5311_ = crate::leanh::lean_box_float(v___x_5309_);
    v___x_5312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5312_, 0, v___x_5310_);
    crate::leanh::lean_ctor_set(v___x_5312_, 1, v___x_5311_);
    v___x_5313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5313_, 0, v_a_5302_);
    crate::leanh::lean_ctor_set(v___x_5313_, 1, v___x_5312_);
    v___x_5314_ =
        crate::leanh::lean_apply_2(v_toPure_5303_, crate::leanh::lean_box(0), v___x_5313_);
    return v___x_5314_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__4(
    mut v_start_5315_: *mut crate::leanh::LeanObject,
    mut v_toPure_5316_: *mut crate::leanh::LeanObject,
    mut v_toBind_5317_: *mut crate::leanh::LeanObject,
    mut v___x_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5320_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5320_, 0, v_start_5315_);
    crate::leanh::lean_closure_set(v___f_5320_, 1, v_a_5319_);
    crate::leanh::lean_closure_set(v___f_5320_, 2, v_toPure_5316_);
    v___x_5321_ = crate::leanh::lean_apply_4(
        v_toBind_5317_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5318_,
        v___f_5320_,
    );
    return v___x_5321_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__5(
    mut v_toPure_5322_: *mut crate::leanh::LeanObject,
    mut v_toBind_5323_: *mut crate::leanh::LeanObject,
    mut v___x_5324_: *mut crate::leanh::LeanObject,
    mut v___x_5325_: *mut crate::leanh::LeanObject,
    mut v_start_5326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5323_);
    v___f_5327_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5327_, 0, v_start_5326_);
    crate::leanh::lean_closure_set(v___f_5327_, 1, v_toPure_5322_);
    crate::leanh::lean_closure_set(v___f_5327_, 2, v_toBind_5323_);
    crate::leanh::lean_closure_set(v___f_5327_, 3, v___x_5324_);
    v___x_5328_ = crate::leanh::lean_apply_4(
        v_toBind_5323_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5325_,
        v___f_5327_,
    );
    return v___x_5328_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__6(
    mut v_start_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
    mut v_toPure_5331_: *mut crate::leanh::LeanObject,
    mut v_stop_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5333_: f64 = 0.0;
    let mut v___x_5334_: f64 = 0.0;
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5333_ = lean_float_of_nat(v_start_5329_);
    v___x_5334_ = lean_float_of_nat(v_stop_5332_);
    v___x_5335_ = crate::leanh::lean_box_float(v___x_5333_);
    v___x_5336_ = crate::leanh::lean_box_float(v___x_5334_);
    v___x_5337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5337_, 0, v___x_5335_);
    crate::leanh::lean_ctor_set(v___x_5337_, 1, v___x_5336_);
    v___x_5338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5338_, 0, v_a_5330_);
    crate::leanh::lean_ctor_set(v___x_5338_, 1, v___x_5337_);
    v___x_5339_ =
        crate::leanh::lean_apply_2(v_toPure_5331_, crate::leanh::lean_box(0), v___x_5338_);
    return v___x_5339_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__7(
    mut v_start_5340_: *mut crate::leanh::LeanObject,
    mut v_toPure_5341_: *mut crate::leanh::LeanObject,
    mut v_toBind_5342_: *mut crate::leanh::LeanObject,
    mut v___x_5343_: *mut crate::leanh::LeanObject,
    mut v_a_5344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5345_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5345_, 0, v_start_5340_);
    crate::leanh::lean_closure_set(v___f_5345_, 1, v_a_5344_);
    crate::leanh::lean_closure_set(v___f_5345_, 2, v_toPure_5341_);
    v___x_5346_ = crate::leanh::lean_apply_4(
        v_toBind_5342_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5343_,
        v___f_5345_,
    );
    return v___x_5346_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__8(
    mut v_toPure_5347_: *mut crate::leanh::LeanObject,
    mut v_toBind_5348_: *mut crate::leanh::LeanObject,
    mut v___x_5349_: *mut crate::leanh::LeanObject,
    mut v___x_5350_: *mut crate::leanh::LeanObject,
    mut v_start_5351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5348_);
    v___f_5352_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5352_, 0, v_start_5351_);
    crate::leanh::lean_closure_set(v___f_5352_, 1, v_toPure_5347_);
    crate::leanh::lean_closure_set(v___f_5352_, 2, v_toBind_5348_);
    crate::leanh::lean_closure_set(v___f_5352_, 3, v___x_5349_);
    v___x_5353_ = crate::leanh::lean_apply_4(
        v_toBind_5348_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5350_,
        v___f_5352_,
    );
    return v___x_5353_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__9(
    mut v_always_5354_: *mut crate::leanh::LeanObject,
    mut v_inst_5355_: *mut crate::leanh::LeanObject,
    mut v_inst_5356_: *mut crate::leanh::LeanObject,
    mut v_inst_5357_: *mut crate::leanh::LeanObject,
    mut v_inst_5358_: *mut crate::leanh::LeanObject,
    mut v_inst_5359_: *mut crate::leanh::LeanObject,
    mut v_cls_5360_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5361_: u8,
    mut v_tag_5362_: *mut crate::leanh::LeanObject,
    mut v_opts_5363_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5364_: u8,
    mut v_msg_5365_: *mut crate::leanh::LeanObject,
    mut v_toPure_5366_: *mut crate::leanh::LeanObject,
    mut v_toBind_5367_: *mut crate::leanh::LeanObject,
    mut v_k_5368_: *mut crate::leanh::LeanObject,
    mut v_inst_5369_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    v_tryCatch_5371_ = crate::leanh::lean_ctor_get(v_always_5354_, 1);
    crate::leanh::lean_inc(v_tryCatch_5371_);
    v___x_5372_ = crate::leanh::lean_box((v_collapsed_5361_) as usize);
    v___x_5373_ = crate::leanh::lean_box((v_clsEnabled_5364_) as usize);
    crate::leanh::lean_inc_ref(v_opts_5363_);
    v___f_5374_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_5374_, 0, v_inst_5355_);
    crate::leanh::lean_closure_set(v___f_5374_, 1, v_inst_5356_);
    crate::leanh::lean_closure_set(v___f_5374_, 2, v_inst_5357_);
    crate::leanh::lean_closure_set(v___f_5374_, 3, v_inst_5358_);
    crate::leanh::lean_closure_set(v___f_5374_, 4, v_always_5354_);
    crate::leanh::lean_closure_set(v___f_5374_, 5, v_inst_5359_);
    crate::leanh::lean_closure_set(v___f_5374_, 6, v_cls_5360_);
    crate::leanh::lean_closure_set(v___f_5374_, 7, v___x_5372_);
    crate::leanh::lean_closure_set(v___f_5374_, 8, v_tag_5362_);
    crate::leanh::lean_closure_set(v___f_5374_, 9, v_opts_5363_);
    crate::leanh::lean_closure_set(v___f_5374_, 10, v___x_5373_);
    crate::leanh::lean_closure_set(v___f_5374_, 11, v_oldTraces_5370_);
    crate::leanh::lean_closure_set(v___f_5374_, 12, v_msg_5365_);
    crate::leanh::lean_inc_n(v_toPure_5366_, 2);
    v___f_5375_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5375_, 0, v_toPure_5366_);
    v___f_5376_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5376_, 0, v_toPure_5366_);
    crate::leanh::lean_inc(v_toBind_5367_);
    v___x_5377_ = crate::leanh::lean_apply_4(
        v_toBind_5367_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_k_5368_,
        v___f_5376_,
    );
    v___x_5378_ = crate::leanh::lean_apply_3(
        v_tryCatch_5371_,
        crate::leanh::lean_box(0),
        v___x_5377_,
        v___f_5375_,
    );
    v___x_5379_ = l_Lean_KVMap_instValueBool;
    v___x_5380_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_5381_ = l_Lean_Option_get___redArg(v___x_5379_, v_opts_5363_, v___x_5380_);
    crate::leanh::lean_dec_ref(v_opts_5363_);
    v___x_5382_ = (crate::leanh::lean_unbox(v___x_5381_) as u8);
    crate::leanh::lean_dec(v___x_5381_);
    if v___x_5382_ == 0 {
        let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5383_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_5384_ =
            crate::leanh::lean_apply_2(v_inst_5369_, crate::leanh::lean_box(0), v___x_5383_);
        crate::leanh::lean_inc(v___x_5384_);
        crate::leanh::lean_inc_n(v_toBind_5367_, 2);
        v___f_5385_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__5 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5385_, 0, v_toPure_5366_);
        crate::leanh::lean_closure_set(v___f_5385_, 1, v_toBind_5367_);
        crate::leanh::lean_closure_set(v___f_5385_, 2, v___x_5384_);
        crate::leanh::lean_closure_set(v___f_5385_, 3, v___x_5378_);
        v___x_5386_ = crate::leanh::lean_apply_4(
            v_toBind_5367_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5384_,
            v___f_5385_,
        );
        v___x_5387_ = crate::leanh::lean_apply_4(
            v_toBind_5367_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5386_,
            v___f_5374_,
        );
        return v___x_5387_;
    } else {
        let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5388_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_5389_ =
            crate::leanh::lean_apply_2(v_inst_5369_, crate::leanh::lean_box(0), v___x_5388_);
        crate::leanh::lean_inc(v___x_5389_);
        crate::leanh::lean_inc_n(v_toBind_5367_, 2);
        v___f_5390_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__8 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5390_, 0, v_toPure_5366_);
        crate::leanh::lean_closure_set(v___f_5390_, 1, v_toBind_5367_);
        crate::leanh::lean_closure_set(v___f_5390_, 2, v___x_5389_);
        crate::leanh::lean_closure_set(v___f_5390_, 3, v___x_5378_);
        v___x_5391_ = crate::leanh::lean_apply_4(
            v_toBind_5367_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5389_,
            v___f_5390_,
        );
        v___x_5392_ = crate::leanh::lean_apply_4(
            v_toBind_5367_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5391_,
            v___f_5374_,
        );
        return v___x_5392_;
    }
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__9___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_always_5393_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5394_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5395_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5396_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5397_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5398_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_5399_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_5400_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_5401_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_5402_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_clsEnabled_5403_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_msg_5404_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toPure_5405_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toBind_5406_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_k_5407_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5408_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_oldTraces_5409_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_5410_: u8 = 0;
    let mut v_clsEnabled_boxed_5411_: u8 = 0;
    let mut v_res_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5410_ = (crate::leanh::lean_unbox(v_collapsed_5400_) as u8);
    v_clsEnabled_boxed_5411_ = (crate::leanh::lean_unbox(v_clsEnabled_5403_) as u8);
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
    mut v_always_5413_: *mut crate::leanh::LeanObject,
    mut v_inst_5414_: *mut crate::leanh::LeanObject,
    mut v_inst_5415_: *mut crate::leanh::LeanObject,
    mut v_inst_5416_: *mut crate::leanh::LeanObject,
    mut v_inst_5417_: *mut crate::leanh::LeanObject,
    mut v_inst_5418_: *mut crate::leanh::LeanObject,
    mut v_cls_5419_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5420_: u8,
    mut v_tag_5421_: *mut crate::leanh::LeanObject,
    mut v_opts_5422_: *mut crate::leanh::LeanObject,
    mut v_msg_5423_: *mut crate::leanh::LeanObject,
    mut v_toPure_5424_: *mut crate::leanh::LeanObject,
    mut v_toBind_5425_: *mut crate::leanh::LeanObject,
    mut v_k_5426_: *mut crate::leanh::LeanObject,
    mut v_inst_5427_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5428_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5429_ = crate::leanh::lean_box((v_collapsed_5420_) as usize);
                v___x_5430_ = crate::leanh::lean_box((v_clsEnabled_5428_) as usize);
                crate::leanh::lean_inc(v_k_5426_);
                crate::leanh::lean_inc(v_toBind_5425_);
                crate::leanh::lean_inc_ref(v_opts_5422_);
                crate::leanh::lean_inc_ref(v_inst_5415_);
                crate::leanh::lean_inc_ref(v_inst_5414_);
                v___f_5431_ = crate::leanh::lean_alloc_closure(
                    l_Lean_withTraceNode___redArg___lam__9___boxed as *mut core::ffi::c_void,
                    17,
                    16,
                );
                crate::leanh::lean_closure_set(v___f_5431_, 0, v_always_5413_);
                crate::leanh::lean_closure_set(v___f_5431_, 1, v_inst_5414_);
                crate::leanh::lean_closure_set(v___f_5431_, 2, v_inst_5415_);
                crate::leanh::lean_closure_set(v___f_5431_, 3, v_inst_5416_);
                crate::leanh::lean_closure_set(v___f_5431_, 4, v_inst_5417_);
                crate::leanh::lean_closure_set(v___f_5431_, 5, v_inst_5418_);
                crate::leanh::lean_closure_set(v___f_5431_, 6, v_cls_5419_);
                crate::leanh::lean_closure_set(v___f_5431_, 7, v___x_5429_);
                crate::leanh::lean_closure_set(v___f_5431_, 8, v_tag_5421_);
                crate::leanh::lean_closure_set(v___f_5431_, 9, v_opts_5422_);
                crate::leanh::lean_closure_set(v___f_5431_, 10, v___x_5430_);
                crate::leanh::lean_closure_set(v___f_5431_, 11, v_msg_5423_);
                crate::leanh::lean_closure_set(v___f_5431_, 12, v_toPure_5424_);
                crate::leanh::lean_closure_set(v___f_5431_, 13, v_toBind_5425_);
                crate::leanh::lean_closure_set(v___f_5431_, 14, v_k_5426_);
                crate::leanh::lean_closure_set(v___f_5431_, 15, v_inst_5427_);
                if v_clsEnabled_5428_ == 0 {
                    v___x_5435_ = l_Lean_KVMap_instValueBool;
                    v___x_5436_ = l_Lean_trace_profiler;
                    v___x_5437_ =
                        l_Lean_Option_get___redArg(v___x_5435_, v_opts_5422_, v___x_5436_);
                    crate::leanh::lean_dec_ref(v_opts_5422_);
                    v___x_5438_ = (crate::leanh::lean_unbox(v___x_5437_) as u8);
                    crate::leanh::lean_dec(v___x_5437_);
                    if v___x_5438_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_5431_);
                        crate::leanh::lean_dec(v_toBind_5425_);
                        crate::leanh::lean_dec_ref(v_inst_5415_);
                        crate::leanh::lean_dec_ref(v_inst_5414_);
                        return v_k_5426_;
                    } else {
                        crate::leanh::lean_dec(v_k_5426_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_5426_);
                    crate::leanh::lean_dec_ref(v_opts_5422_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5433_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_5414_,
                    v_inst_5415_,
                );
                v___x_5434_ = crate::leanh::lean_apply_4(
                    v_toBind_5425_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_always_5439_: *mut crate::leanh::LeanObject,
    mut v_inst_5440_: *mut crate::leanh::LeanObject,
    mut v_inst_5441_: *mut crate::leanh::LeanObject,
    mut v_inst_5442_: *mut crate::leanh::LeanObject,
    mut v_inst_5443_: *mut crate::leanh::LeanObject,
    mut v_inst_5444_: *mut crate::leanh::LeanObject,
    mut v_cls_5445_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5446_: *mut crate::leanh::LeanObject,
    mut v_tag_5447_: *mut crate::leanh::LeanObject,
    mut v_opts_5448_: *mut crate::leanh::LeanObject,
    mut v_msg_5449_: *mut crate::leanh::LeanObject,
    mut v_toPure_5450_: *mut crate::leanh::LeanObject,
    mut v_toBind_5451_: *mut crate::leanh::LeanObject,
    mut v_k_5452_: *mut crate::leanh::LeanObject,
    mut v_inst_5453_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5455_: u8 = 0;
    let mut v_clsEnabled_boxed_5456_: u8 = 0;
    let mut v_res_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5455_ = (crate::leanh::lean_unbox(v_collapsed_5446_) as u8);
    v_clsEnabled_boxed_5456_ = (crate::leanh::lean_unbox(v_clsEnabled_5454_) as u8);
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
    mut v_k_5458_: *mut crate::leanh::LeanObject,
    mut v_inst_5459_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_5460_: *mut crate::leanh::LeanObject,
    mut v_always_5461_: *mut crate::leanh::LeanObject,
    mut v_inst_5462_: *mut crate::leanh::LeanObject,
    mut v_inst_5463_: *mut crate::leanh::LeanObject,
    mut v_inst_5464_: *mut crate::leanh::LeanObject,
    mut v_inst_5465_: *mut crate::leanh::LeanObject,
    mut v_cls_5466_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5467_: u8,
    mut v_tag_5468_: *mut crate::leanh::LeanObject,
    mut v_msg_5469_: *mut crate::leanh::LeanObject,
    mut v_toBind_5470_: *mut crate::leanh::LeanObject,
    mut v_inst_5471_: *mut crate::leanh::LeanObject,
    mut v_inst_5472_: *mut crate::leanh::LeanObject,
    mut v_opts_5473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasTrace_5474_: u8 = 0;
    v_hasTrace_5474_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_5473_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5474_ == 0 {
        crate::leanh::lean_dec_ref(v_opts_5473_);
        crate::leanh::lean_dec(v_inst_5472_);
        crate::leanh::lean_dec(v_inst_5471_);
        crate::leanh::lean_dec(v_toBind_5470_);
        crate::leanh::lean_dec(v_msg_5469_);
        crate::leanh::lean_dec_ref(v_tag_5468_);
        crate::leanh::lean_dec(v_cls_5466_);
        crate::leanh::lean_dec_ref(v_inst_5465_);
        crate::leanh::lean_dec(v_inst_5464_);
        crate::leanh::lean_dec_ref(v_inst_5463_);
        crate::leanh::lean_dec_ref(v_inst_5462_);
        crate::leanh::lean_dec_ref(v_always_5461_);
        crate::leanh::lean_dec_ref(v_toApplicative_5460_);
        crate::leanh::lean_dec_ref(v_inst_5459_);
        return v_k_5458_;
    } else {
        let mut v_getInheritedTraceOptions_5475_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v_toPure_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_5475_ = crate::leanh::lean_ctor_get(v_inst_5459_, 2);
        crate::leanh::lean_inc(v_getInheritedTraceOptions_5475_);
        v_toPure_5476_ = crate::leanh::lean_ctor_get(v_toApplicative_5460_, 1);
        crate::leanh::lean_inc_n(v_toPure_5476_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_5460_);
        v___x_5477_ = crate::leanh::lean_box((v_collapsed_5467_) as usize);
        crate::leanh::lean_inc_n(v_toBind_5470_, 3);
        crate::leanh::lean_inc(v_cls_5466_);
        v___f_5478_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__10___boxed as *mut core::ffi::c_void,
            16,
            15,
        );
        crate::leanh::lean_closure_set(v___f_5478_, 0, v_always_5461_);
        crate::leanh::lean_closure_set(v___f_5478_, 1, v_inst_5462_);
        crate::leanh::lean_closure_set(v___f_5478_, 2, v_inst_5459_);
        crate::leanh::lean_closure_set(v___f_5478_, 3, v_inst_5463_);
        crate::leanh::lean_closure_set(v___f_5478_, 4, v_inst_5464_);
        crate::leanh::lean_closure_set(v___f_5478_, 5, v_inst_5465_);
        crate::leanh::lean_closure_set(v___f_5478_, 6, v_cls_5466_);
        crate::leanh::lean_closure_set(v___f_5478_, 7, v___x_5477_);
        crate::leanh::lean_closure_set(v___f_5478_, 8, v_tag_5468_);
        crate::leanh::lean_closure_set(v___f_5478_, 9, v_opts_5473_);
        crate::leanh::lean_closure_set(v___f_5478_, 10, v_msg_5469_);
        crate::leanh::lean_closure_set(v___f_5478_, 11, v_toPure_5476_);
        crate::leanh::lean_closure_set(v___f_5478_, 12, v_toBind_5470_);
        crate::leanh::lean_closure_set(v___f_5478_, 13, v_k_5458_);
        crate::leanh::lean_closure_set(v___f_5478_, 14, v_inst_5471_);
        v___f_5479_ = crate::leanh::lean_alloc_closure(
            l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5479_, 0, v_toPure_5476_);
        crate::leanh::lean_closure_set(v___f_5479_, 1, v_cls_5466_);
        crate::leanh::lean_closure_set(v___f_5479_, 2, v_toBind_5470_);
        crate::leanh::lean_closure_set(v___f_5479_, 3, v_inst_5472_);
        v___x_5480_ = crate::leanh::lean_apply_4(
            v_toBind_5470_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getInheritedTraceOptions_5475_,
            v___f_5479_,
        );
        v___x_5481_ = crate::leanh::lean_apply_4(
            v_toBind_5470_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5480_,
            v___f_5478_,
        );
        return v___x_5481_;
    }
}
pub unsafe fn l_Lean_withTraceNode___redArg___lam__13___boxed(
    mut v_k_5482_: *mut crate::leanh::LeanObject,
    mut v_inst_5483_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_5484_: *mut crate::leanh::LeanObject,
    mut v_always_5485_: *mut crate::leanh::LeanObject,
    mut v_inst_5486_: *mut crate::leanh::LeanObject,
    mut v_inst_5487_: *mut crate::leanh::LeanObject,
    mut v_inst_5488_: *mut crate::leanh::LeanObject,
    mut v_inst_5489_: *mut crate::leanh::LeanObject,
    mut v_cls_5490_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5491_: *mut crate::leanh::LeanObject,
    mut v_tag_5492_: *mut crate::leanh::LeanObject,
    mut v_msg_5493_: *mut crate::leanh::LeanObject,
    mut v_toBind_5494_: *mut crate::leanh::LeanObject,
    mut v_inst_5495_: *mut crate::leanh::LeanObject,
    mut v_inst_5496_: *mut crate::leanh::LeanObject,
    mut v_opts_5497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5498_: u8 = 0;
    let mut v_res_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5498_ = (crate::leanh::lean_unbox(v_collapsed_5491_) as u8);
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
    mut v_inst_5500_: *mut crate::leanh::LeanObject,
    mut v_inst_5501_: *mut crate::leanh::LeanObject,
    mut v_inst_5502_: *mut crate::leanh::LeanObject,
    mut v_inst_5503_: *mut crate::leanh::LeanObject,
    mut v_inst_5504_: *mut crate::leanh::LeanObject,
    mut v_always_5505_: *mut crate::leanh::LeanObject,
    mut v_inst_5506_: *mut crate::leanh::LeanObject,
    mut v_inst_5507_: *mut crate::leanh::LeanObject,
    mut v_cls_5508_: *mut crate::leanh::LeanObject,
    mut v_msg_5509_: *mut crate::leanh::LeanObject,
    mut v_k_5510_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5511_: u8,
    mut v_tag_5512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5513_ = crate::leanh::lean_ctor_get(v_inst_5500_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5513_);
    v_toBind_5514_ = crate::leanh::lean_ctor_get(v_inst_5500_, 1);
    crate::leanh::lean_inc_n(v_toBind_5514_, 2);
    v___x_5515_ = crate::leanh::lean_box((v_collapsed_5511_) as usize);
    crate::leanh::lean_inc(v_inst_5504_);
    v___f_5516_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__13___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_5516_, 0, v_k_5510_);
    crate::leanh::lean_closure_set(v___f_5516_, 1, v_inst_5501_);
    crate::leanh::lean_closure_set(v___f_5516_, 2, v_toApplicative_5513_);
    crate::leanh::lean_closure_set(v___f_5516_, 3, v_always_5505_);
    crate::leanh::lean_closure_set(v___f_5516_, 4, v_inst_5500_);
    crate::leanh::lean_closure_set(v___f_5516_, 5, v_inst_5502_);
    crate::leanh::lean_closure_set(v___f_5516_, 6, v_inst_5503_);
    crate::leanh::lean_closure_set(v___f_5516_, 7, v_inst_5507_);
    crate::leanh::lean_closure_set(v___f_5516_, 8, v_cls_5508_);
    crate::leanh::lean_closure_set(v___f_5516_, 9, v___x_5515_);
    crate::leanh::lean_closure_set(v___f_5516_, 10, v_tag_5512_);
    crate::leanh::lean_closure_set(v___f_5516_, 11, v_msg_5509_);
    crate::leanh::lean_closure_set(v___f_5516_, 12, v_toBind_5514_);
    crate::leanh::lean_closure_set(v___f_5516_, 13, v_inst_5506_);
    crate::leanh::lean_closure_set(v___f_5516_, 14, v_inst_5504_);
    v___x_5517_ = crate::leanh::lean_apply_4(
        v_toBind_5514_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5504_,
        v___f_5516_,
    );
    return v___x_5517_;
}
pub unsafe fn l_Lean_withTraceNode___redArg___boxed(
    mut v_inst_5518_: *mut crate::leanh::LeanObject,
    mut v_inst_5519_: *mut crate::leanh::LeanObject,
    mut v_inst_5520_: *mut crate::leanh::LeanObject,
    mut v_inst_5521_: *mut crate::leanh::LeanObject,
    mut v_inst_5522_: *mut crate::leanh::LeanObject,
    mut v_always_5523_: *mut crate::leanh::LeanObject,
    mut v_inst_5524_: *mut crate::leanh::LeanObject,
    mut v_inst_5525_: *mut crate::leanh::LeanObject,
    mut v_cls_5526_: *mut crate::leanh::LeanObject,
    mut v_msg_5527_: *mut crate::leanh::LeanObject,
    mut v_k_5528_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5529_: *mut crate::leanh::LeanObject,
    mut v_tag_5530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5531_: u8 = 0;
    let mut v_res_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5531_ = (crate::leanh::lean_unbox(v_collapsed_5529_) as u8);
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
    mut v_00_u03b1_5533_: *mut crate::leanh::LeanObject,
    mut v_m_5534_: *mut crate::leanh::LeanObject,
    mut v_inst_5535_: *mut crate::leanh::LeanObject,
    mut v_inst_5536_: *mut crate::leanh::LeanObject,
    mut v_inst_5537_: *mut crate::leanh::LeanObject,
    mut v_inst_5538_: *mut crate::leanh::LeanObject,
    mut v_inst_5539_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_5540_: *mut crate::leanh::LeanObject,
    mut v_always_5541_: *mut crate::leanh::LeanObject,
    mut v_inst_5542_: *mut crate::leanh::LeanObject,
    mut v_inst_5543_: *mut crate::leanh::LeanObject,
    mut v_cls_5544_: *mut crate::leanh::LeanObject,
    mut v_msg_5545_: *mut crate::leanh::LeanObject,
    mut v_k_5546_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5547_: u8,
    mut v_tag_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5549_ = crate::leanh::lean_ctor_get(v_inst_5535_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5549_);
    v_toBind_5550_ = crate::leanh::lean_ctor_get(v_inst_5535_, 1);
    crate::leanh::lean_inc_n(v_toBind_5550_, 2);
    v___x_5551_ = crate::leanh::lean_box((v_collapsed_5547_) as usize);
    crate::leanh::lean_inc(v_inst_5539_);
    v___f_5552_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__13___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_5552_, 0, v_k_5546_);
    crate::leanh::lean_closure_set(v___f_5552_, 1, v_inst_5536_);
    crate::leanh::lean_closure_set(v___f_5552_, 2, v_toApplicative_5549_);
    crate::leanh::lean_closure_set(v___f_5552_, 3, v_always_5541_);
    crate::leanh::lean_closure_set(v___f_5552_, 4, v_inst_5535_);
    crate::leanh::lean_closure_set(v___f_5552_, 5, v_inst_5537_);
    crate::leanh::lean_closure_set(v___f_5552_, 6, v_inst_5538_);
    crate::leanh::lean_closure_set(v___f_5552_, 7, v_inst_5543_);
    crate::leanh::lean_closure_set(v___f_5552_, 8, v_cls_5544_);
    crate::leanh::lean_closure_set(v___f_5552_, 9, v___x_5551_);
    crate::leanh::lean_closure_set(v___f_5552_, 10, v_tag_5548_);
    crate::leanh::lean_closure_set(v___f_5552_, 11, v_msg_5545_);
    crate::leanh::lean_closure_set(v___f_5552_, 12, v_toBind_5550_);
    crate::leanh::lean_closure_set(v___f_5552_, 13, v_inst_5542_);
    crate::leanh::lean_closure_set(v___f_5552_, 14, v_inst_5539_);
    v___x_5553_ = crate::leanh::lean_apply_4(
        v_toBind_5550_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5539_,
        v___f_5552_,
    );
    return v___x_5553_;
}
pub unsafe fn l_Lean_withTraceNode___boxed(
    mut v_00_u03b1_5554_: *mut crate::leanh::LeanObject,
    mut v_m_5555_: *mut crate::leanh::LeanObject,
    mut v_inst_5556_: *mut crate::leanh::LeanObject,
    mut v_inst_5557_: *mut crate::leanh::LeanObject,
    mut v_inst_5558_: *mut crate::leanh::LeanObject,
    mut v_inst_5559_: *mut crate::leanh::LeanObject,
    mut v_inst_5560_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_5561_: *mut crate::leanh::LeanObject,
    mut v_always_5562_: *mut crate::leanh::LeanObject,
    mut v_inst_5563_: *mut crate::leanh::LeanObject,
    mut v_inst_5564_: *mut crate::leanh::LeanObject,
    mut v_cls_5565_: *mut crate::leanh::LeanObject,
    mut v_msg_5566_: *mut crate::leanh::LeanObject,
    mut v_k_5567_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5568_: *mut crate::leanh::LeanObject,
    mut v_tag_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5570_: u8 = 0;
    let mut v_res_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5570_ = (crate::leanh::lean_unbox(v_collapsed_5568_) as u8);
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
    mut v_self_5572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_5573_ = crate::leanh::lean_ctor_get(v_self_5572_, 0);
    crate::leanh::lean_inc(v_fst_5573_);
    return v_fst_5573_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__0___boxed(
    mut v_self_5574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_5574_);
    crate::leanh::lean_dec_ref(v_self_5574_);
    return v_res_5575_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__1(
    mut v_toPure_5576_: *mut crate::leanh::LeanObject,
    mut v_x_5577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5577_) == 0 {
        let mut v_a_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5578_ = crate::leanh::lean_ctor_get(v_x_5577_, 0);
        crate::leanh::lean_inc(v_a_5578_);
        crate::leanh::lean_dec_ref_known(v_x_5577_, 1);
        v___x_5579_ = l_Lean_Exception_toMessageData(v_a_5578_);
        v___x_5580_ =
            crate::leanh::lean_apply_2(v_toPure_5576_, crate::leanh::lean_box(0), v___x_5579_);
        return v___x_5580_;
    } else {
        let mut v_a_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5581_ = crate::leanh::lean_ctor_get(v_x_5577_, 0);
        crate::leanh::lean_inc(v_a_5581_);
        crate::leanh::lean_dec_ref_known(v_x_5577_, 1);
        v_snd_5582_ = crate::leanh::lean_ctor_get(v_a_5581_, 1);
        crate::leanh::lean_inc(v_snd_5582_);
        crate::leanh::lean_dec(v_a_5581_);
        v___x_5583_ =
            crate::leanh::lean_apply_2(v_toPure_5576_, crate::leanh::lean_box(0), v_snd_5582_);
        return v___x_5583_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__4(
    mut v_toPure_5584_: *mut crate::leanh::LeanObject,
    mut v_ex_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5586_, 0, v_ex_5585_);
    v___x_5587_ =
        crate::leanh::lean_apply_2(v_toPure_5584_, crate::leanh::lean_box(0), v___x_5586_);
    return v___x_5587_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__2(
    mut v_toPure_5588_: *mut crate::leanh::LeanObject,
    mut v_a_5589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5590_, 0, v_a_5589_);
    v___x_5591_ =
        crate::leanh::lean_apply_2(v_toPure_5588_, crate::leanh::lean_box(0), v___x_5590_);
    return v___x_5591_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__3(
    mut v_inst_5592_: *mut crate::leanh::LeanObject,
    mut v_inst_5593_: *mut crate::leanh::LeanObject,
    mut v_inst_5594_: *mut crate::leanh::LeanObject,
    mut v_inst_5595_: *mut crate::leanh::LeanObject,
    mut v_inst_5596_: *mut crate::leanh::LeanObject,
    mut v___f_5597_: *mut crate::leanh::LeanObject,
    mut v_cls_5598_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5599_: u8,
    mut v_tag_5600_: *mut crate::leanh::LeanObject,
    mut v_opts_5601_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5602_: u8,
    mut v_oldTraces_5603_: *mut crate::leanh::LeanObject,
    mut v_msg_5604_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5607_: *mut crate::leanh::LeanObject,
    mut v_inst_5608_: *mut crate::leanh::LeanObject,
    mut v_inst_5609_: *mut crate::leanh::LeanObject,
    mut v_inst_5610_: *mut crate::leanh::LeanObject,
    mut v_inst_5611_: *mut crate::leanh::LeanObject,
    mut v___f_5612_: *mut crate::leanh::LeanObject,
    mut v_cls_5613_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5614_: *mut crate::leanh::LeanObject,
    mut v_tag_5615_: *mut crate::leanh::LeanObject,
    mut v_opts_5616_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5617_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5618_: *mut crate::leanh::LeanObject,
    mut v_msg_5619_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5621_: u8 = 0;
    let mut v_clsEnabled_boxed_5622_: u8 = 0;
    let mut v_res_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5621_ = (crate::leanh::lean_unbox(v_collapsed_5614_) as u8);
    v_clsEnabled_boxed_5622_ = (crate::leanh::lean_unbox(v_clsEnabled_5617_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_5616_);
    return v_res_5623_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__5(
    mut v_start_5624_: *mut crate::leanh::LeanObject,
    mut v_a_5625_: *mut crate::leanh::LeanObject,
    mut v_toPure_5626_: *mut crate::leanh::LeanObject,
    mut v_stop_5627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5628_: f64 = 0.0;
    let mut v___x_5629_: f64 = 0.0;
    let mut v___x_5630_: f64 = 0.0;
    let mut v___x_5631_: f64 = 0.0;
    let mut v___x_5632_: f64 = 0.0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5628_ = lean_float_of_nat(v_start_5624_);
    v___x_5629_ = crate::leanh::lean_float_once(
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
    v___x_5633_ = crate::leanh::lean_box_float(v___x_5630_);
    v___x_5634_ = crate::leanh::lean_box_float(v___x_5632_);
    v___x_5635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5635_, 0, v___x_5633_);
    crate::leanh::lean_ctor_set(v___x_5635_, 1, v___x_5634_);
    v___x_5636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5636_, 0, v_a_5625_);
    crate::leanh::lean_ctor_set(v___x_5636_, 1, v___x_5635_);
    v___x_5637_ =
        crate::leanh::lean_apply_2(v_toPure_5626_, crate::leanh::lean_box(0), v___x_5636_);
    return v___x_5637_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__6(
    mut v_start_5638_: *mut crate::leanh::LeanObject,
    mut v_toPure_5639_: *mut crate::leanh::LeanObject,
    mut v_toBind_5640_: *mut crate::leanh::LeanObject,
    mut v___x_5641_: *mut crate::leanh::LeanObject,
    mut v_a_5642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5643_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5643_, 0, v_start_5638_);
    crate::leanh::lean_closure_set(v___f_5643_, 1, v_a_5642_);
    crate::leanh::lean_closure_set(v___f_5643_, 2, v_toPure_5639_);
    v___x_5644_ = crate::leanh::lean_apply_4(
        v_toBind_5640_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5641_,
        v___f_5643_,
    );
    return v___x_5644_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__7(
    mut v_toPure_5645_: *mut crate::leanh::LeanObject,
    mut v_toBind_5646_: *mut crate::leanh::LeanObject,
    mut v___x_5647_: *mut crate::leanh::LeanObject,
    mut v___x_5648_: *mut crate::leanh::LeanObject,
    mut v_start_5649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5646_);
    v___f_5650_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5650_, 0, v_start_5649_);
    crate::leanh::lean_closure_set(v___f_5650_, 1, v_toPure_5645_);
    crate::leanh::lean_closure_set(v___f_5650_, 2, v_toBind_5646_);
    crate::leanh::lean_closure_set(v___f_5650_, 3, v___x_5647_);
    v___x_5651_ = crate::leanh::lean_apply_4(
        v_toBind_5646_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5648_,
        v___f_5650_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__8(
    mut v_start_5652_: *mut crate::leanh::LeanObject,
    mut v_a_5653_: *mut crate::leanh::LeanObject,
    mut v_toPure_5654_: *mut crate::leanh::LeanObject,
    mut v_stop_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5656_: f64 = 0.0;
    let mut v___x_5657_: f64 = 0.0;
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5656_ = lean_float_of_nat(v_start_5652_);
    v___x_5657_ = lean_float_of_nat(v_stop_5655_);
    v___x_5658_ = crate::leanh::lean_box_float(v___x_5656_);
    v___x_5659_ = crate::leanh::lean_box_float(v___x_5657_);
    v___x_5660_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5660_, 0, v___x_5658_);
    crate::leanh::lean_ctor_set(v___x_5660_, 1, v___x_5659_);
    v___x_5661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5661_, 0, v_a_5653_);
    crate::leanh::lean_ctor_set(v___x_5661_, 1, v___x_5660_);
    v___x_5662_ =
        crate::leanh::lean_apply_2(v_toPure_5654_, crate::leanh::lean_box(0), v___x_5661_);
    return v___x_5662_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__9(
    mut v_start_5663_: *mut crate::leanh::LeanObject,
    mut v_toPure_5664_: *mut crate::leanh::LeanObject,
    mut v_toBind_5665_: *mut crate::leanh::LeanObject,
    mut v___x_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5668_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5668_, 0, v_start_5663_);
    crate::leanh::lean_closure_set(v___f_5668_, 1, v_a_5667_);
    crate::leanh::lean_closure_set(v___f_5668_, 2, v_toPure_5664_);
    v___x_5669_ = crate::leanh::lean_apply_4(
        v_toBind_5665_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5666_,
        v___f_5668_,
    );
    return v___x_5669_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__10(
    mut v_toPure_5670_: *mut crate::leanh::LeanObject,
    mut v_toBind_5671_: *mut crate::leanh::LeanObject,
    mut v___x_5672_: *mut crate::leanh::LeanObject,
    mut v___x_5673_: *mut crate::leanh::LeanObject,
    mut v_start_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5671_);
    v___f_5675_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5675_, 0, v_start_5674_);
    crate::leanh::lean_closure_set(v___f_5675_, 1, v_toPure_5670_);
    crate::leanh::lean_closure_set(v___f_5675_, 2, v_toBind_5671_);
    crate::leanh::lean_closure_set(v___f_5675_, 3, v___x_5672_);
    v___x_5676_ = crate::leanh::lean_apply_4(
        v_toBind_5671_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5673_,
        v___f_5675_,
    );
    return v___x_5676_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__11(
    mut v_inst_5677_: *mut crate::leanh::LeanObject,
    mut v_inst_5678_: *mut crate::leanh::LeanObject,
    mut v_inst_5679_: *mut crate::leanh::LeanObject,
    mut v_inst_5680_: *mut crate::leanh::LeanObject,
    mut v_inst_5681_: *mut crate::leanh::LeanObject,
    mut v___f_5682_: *mut crate::leanh::LeanObject,
    mut v_cls_5683_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5684_: u8,
    mut v_tag_5685_: *mut crate::leanh::LeanObject,
    mut v_opts_5686_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5687_: u8,
    mut v_msg_5688_: *mut crate::leanh::LeanObject,
    mut v_toBind_5689_: *mut crate::leanh::LeanObject,
    mut v_k_5690_: *mut crate::leanh::LeanObject,
    mut v___f_5691_: *mut crate::leanh::LeanObject,
    mut v___f_5692_: *mut crate::leanh::LeanObject,
    mut v_inst_5693_: *mut crate::leanh::LeanObject,
    mut v_toPure_5694_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u8 = 0;
    v_tryCatch_5696_ = crate::leanh::lean_ctor_get(v_inst_5677_, 1);
    crate::leanh::lean_inc(v_tryCatch_5696_);
    v___x_5697_ = crate::leanh::lean_box((v_collapsed_5684_) as usize);
    v___x_5698_ = crate::leanh::lean_box((v_clsEnabled_5687_) as usize);
    crate::leanh::lean_inc_ref(v_opts_5686_);
    v___f_5699_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_5699_, 0, v_inst_5678_);
    crate::leanh::lean_closure_set(v___f_5699_, 1, v_inst_5679_);
    crate::leanh::lean_closure_set(v___f_5699_, 2, v_inst_5680_);
    crate::leanh::lean_closure_set(v___f_5699_, 3, v_inst_5681_);
    crate::leanh::lean_closure_set(v___f_5699_, 4, v_inst_5677_);
    crate::leanh::lean_closure_set(v___f_5699_, 5, v___f_5682_);
    crate::leanh::lean_closure_set(v___f_5699_, 6, v_cls_5683_);
    crate::leanh::lean_closure_set(v___f_5699_, 7, v___x_5697_);
    crate::leanh::lean_closure_set(v___f_5699_, 8, v_tag_5685_);
    crate::leanh::lean_closure_set(v___f_5699_, 9, v_opts_5686_);
    crate::leanh::lean_closure_set(v___f_5699_, 10, v___x_5698_);
    crate::leanh::lean_closure_set(v___f_5699_, 11, v_oldTraces_5695_);
    crate::leanh::lean_closure_set(v___f_5699_, 12, v_msg_5688_);
    crate::leanh::lean_inc(v_toBind_5689_);
    v___x_5700_ = crate::leanh::lean_apply_4(
        v_toBind_5689_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_k_5690_,
        v___f_5691_,
    );
    v___x_5701_ = crate::leanh::lean_apply_3(
        v_tryCatch_5696_,
        crate::leanh::lean_box(0),
        v___x_5700_,
        v___f_5692_,
    );
    v___x_5702_ = l_Lean_KVMap_instValueBool;
    v___x_5703_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_5704_ = l_Lean_Option_get___redArg(v___x_5702_, v_opts_5686_, v___x_5703_);
    crate::leanh::lean_dec_ref(v_opts_5686_);
    v___x_5705_ = (crate::leanh::lean_unbox(v___x_5704_) as u8);
    crate::leanh::lean_dec(v___x_5704_);
    if v___x_5705_ == 0 {
        let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5706_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_5707_ =
            crate::leanh::lean_apply_2(v_inst_5693_, crate::leanh::lean_box(0), v___x_5706_);
        crate::leanh::lean_inc(v___x_5707_);
        crate::leanh::lean_inc_n(v_toBind_5689_, 2);
        v___f_5708_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__7 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5708_, 0, v_toPure_5694_);
        crate::leanh::lean_closure_set(v___f_5708_, 1, v_toBind_5689_);
        crate::leanh::lean_closure_set(v___f_5708_, 2, v___x_5707_);
        crate::leanh::lean_closure_set(v___f_5708_, 3, v___x_5701_);
        v___x_5709_ = crate::leanh::lean_apply_4(
            v_toBind_5689_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5707_,
            v___f_5708_,
        );
        v___x_5710_ = crate::leanh::lean_apply_4(
            v_toBind_5689_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5709_,
            v___f_5699_,
        );
        return v___x_5710_;
    } else {
        let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5711_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_5712_ =
            crate::leanh::lean_apply_2(v_inst_5693_, crate::leanh::lean_box(0), v___x_5711_);
        crate::leanh::lean_inc(v___x_5712_);
        crate::leanh::lean_inc_n(v_toBind_5689_, 2);
        v___f_5713_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__10 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5713_, 0, v_toPure_5694_);
        crate::leanh::lean_closure_set(v___f_5713_, 1, v_toBind_5689_);
        crate::leanh::lean_closure_set(v___f_5713_, 2, v___x_5712_);
        crate::leanh::lean_closure_set(v___f_5713_, 3, v___x_5701_);
        v___x_5714_ = crate::leanh::lean_apply_4(
            v_toBind_5689_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5712_,
            v___f_5713_,
        );
        v___x_5715_ = crate::leanh::lean_apply_4(
            v_toBind_5689_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5714_,
            v___f_5699_,
        );
        return v___x_5715_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__11___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5716_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5717_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5718_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5719_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5720_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_5721_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_5722_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_5723_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_5724_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_5725_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_clsEnabled_5726_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_msg_5727_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_5728_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_k_5729_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_5730_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___f_5731_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5732_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_toPure_5733_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_oldTraces_5734_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_collapsed_boxed_5735_: u8 = 0;
    let mut v_clsEnabled_boxed_5736_: u8 = 0;
    let mut v_res_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5735_ = (crate::leanh::lean_unbox(v_collapsed_5723_) as u8);
    v_clsEnabled_boxed_5736_ = (crate::leanh::lean_unbox(v_clsEnabled_5726_) as u8);
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
    mut v_inst_5738_: *mut crate::leanh::LeanObject,
    mut v_inst_5739_: *mut crate::leanh::LeanObject,
    mut v_inst_5740_: *mut crate::leanh::LeanObject,
    mut v_inst_5741_: *mut crate::leanh::LeanObject,
    mut v_inst_5742_: *mut crate::leanh::LeanObject,
    mut v___f_5743_: *mut crate::leanh::LeanObject,
    mut v_cls_5744_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5745_: u8,
    mut v_tag_5746_: *mut crate::leanh::LeanObject,
    mut v_opts_5747_: *mut crate::leanh::LeanObject,
    mut v_msg_5748_: *mut crate::leanh::LeanObject,
    mut v_toBind_5749_: *mut crate::leanh::LeanObject,
    mut v_k_5750_: *mut crate::leanh::LeanObject,
    mut v___f_5751_: *mut crate::leanh::LeanObject,
    mut v___f_5752_: *mut crate::leanh::LeanObject,
    mut v_inst_5753_: *mut crate::leanh::LeanObject,
    mut v_toPure_5754_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5755_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5756_ = crate::leanh::lean_box((v_collapsed_5745_) as usize);
                v___x_5757_ = crate::leanh::lean_box((v_clsEnabled_5755_) as usize);
                crate::leanh::lean_inc(v_k_5750_);
                crate::leanh::lean_inc(v_toBind_5749_);
                crate::leanh::lean_inc_ref(v_opts_5747_);
                crate::leanh::lean_inc_ref(v_inst_5740_);
                crate::leanh::lean_inc_ref(v_inst_5739_);
                v___f_5758_ = crate::leanh::lean_alloc_closure(
                    l_Lean_withTraceNode_x27___redArg___lam__11___boxed as *mut core::ffi::c_void,
                    19,
                    18,
                );
                crate::leanh::lean_closure_set(v___f_5758_, 0, v_inst_5738_);
                crate::leanh::lean_closure_set(v___f_5758_, 1, v_inst_5739_);
                crate::leanh::lean_closure_set(v___f_5758_, 2, v_inst_5740_);
                crate::leanh::lean_closure_set(v___f_5758_, 3, v_inst_5741_);
                crate::leanh::lean_closure_set(v___f_5758_, 4, v_inst_5742_);
                crate::leanh::lean_closure_set(v___f_5758_, 5, v___f_5743_);
                crate::leanh::lean_closure_set(v___f_5758_, 6, v_cls_5744_);
                crate::leanh::lean_closure_set(v___f_5758_, 7, v___x_5756_);
                crate::leanh::lean_closure_set(v___f_5758_, 8, v_tag_5746_);
                crate::leanh::lean_closure_set(v___f_5758_, 9, v_opts_5747_);
                crate::leanh::lean_closure_set(v___f_5758_, 10, v___x_5757_);
                crate::leanh::lean_closure_set(v___f_5758_, 11, v_msg_5748_);
                crate::leanh::lean_closure_set(v___f_5758_, 12, v_toBind_5749_);
                crate::leanh::lean_closure_set(v___f_5758_, 13, v_k_5750_);
                crate::leanh::lean_closure_set(v___f_5758_, 14, v___f_5751_);
                crate::leanh::lean_closure_set(v___f_5758_, 15, v___f_5752_);
                crate::leanh::lean_closure_set(v___f_5758_, 16, v_inst_5753_);
                crate::leanh::lean_closure_set(v___f_5758_, 17, v_toPure_5754_);
                if v_clsEnabled_5755_ == 0 {
                    v___x_5762_ = l_Lean_KVMap_instValueBool;
                    v___x_5763_ = l_Lean_trace_profiler;
                    v___x_5764_ =
                        l_Lean_Option_get___redArg(v___x_5762_, v_opts_5747_, v___x_5763_);
                    crate::leanh::lean_dec_ref(v_opts_5747_);
                    v___x_5765_ = (crate::leanh::lean_unbox(v___x_5764_) as u8);
                    crate::leanh::lean_dec(v___x_5764_);
                    if v___x_5765_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_5758_);
                        crate::leanh::lean_dec(v_toBind_5749_);
                        crate::leanh::lean_dec_ref(v_inst_5740_);
                        crate::leanh::lean_dec_ref(v_inst_5739_);
                        return v_k_5750_;
                    } else {
                        crate::leanh::lean_dec(v_k_5750_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_5750_);
                    crate::leanh::lean_dec_ref(v_opts_5747_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5760_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_5739_,
                    v_inst_5740_,
                );
                v___x_5761_ = crate::leanh::lean_apply_4(
                    v_toBind_5749_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5766_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5767_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5768_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5769_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5770_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_5771_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_5772_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_5773_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_5774_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_5775_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_msg_5776_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_5777_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_k_5778_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_5779_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_5780_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5781_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_toPure_5782_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_clsEnabled_5783_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5784_: u8 = 0;
    let mut v_clsEnabled_boxed_5785_: u8 = 0;
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5784_ = (crate::leanh::lean_unbox(v_collapsed_5773_) as u8);
    v_clsEnabled_boxed_5785_ = (crate::leanh::lean_unbox(v_clsEnabled_5783_) as u8);
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
    mut v_k_5787_: *mut crate::leanh::LeanObject,
    mut v_inst_5788_: *mut crate::leanh::LeanObject,
    mut v_inst_5789_: *mut crate::leanh::LeanObject,
    mut v_inst_5790_: *mut crate::leanh::LeanObject,
    mut v_inst_5791_: *mut crate::leanh::LeanObject,
    mut v_inst_5792_: *mut crate::leanh::LeanObject,
    mut v___f_5793_: *mut crate::leanh::LeanObject,
    mut v_cls_5794_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5795_: u8,
    mut v_tag_5796_: *mut crate::leanh::LeanObject,
    mut v_msg_5797_: *mut crate::leanh::LeanObject,
    mut v_toBind_5798_: *mut crate::leanh::LeanObject,
    mut v___f_5799_: *mut crate::leanh::LeanObject,
    mut v___f_5800_: *mut crate::leanh::LeanObject,
    mut v_inst_5801_: *mut crate::leanh::LeanObject,
    mut v_toPure_5802_: *mut crate::leanh::LeanObject,
    mut v___f_5803_: *mut crate::leanh::LeanObject,
    mut v_opts_5804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasTrace_5805_: u8 = 0;
    v_hasTrace_5805_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_5804_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5805_ == 0 {
        crate::leanh::lean_dec_ref(v_opts_5804_);
        crate::leanh::lean_dec(v___f_5803_);
        crate::leanh::lean_dec(v_toPure_5802_);
        crate::leanh::lean_dec(v_inst_5801_);
        crate::leanh::lean_dec(v___f_5800_);
        crate::leanh::lean_dec(v___f_5799_);
        crate::leanh::lean_dec(v_toBind_5798_);
        crate::leanh::lean_dec(v_msg_5797_);
        crate::leanh::lean_dec_ref(v_tag_5796_);
        crate::leanh::lean_dec(v_cls_5794_);
        crate::leanh::lean_dec_ref(v___f_5793_);
        crate::leanh::lean_dec(v_inst_5792_);
        crate::leanh::lean_dec_ref(v_inst_5791_);
        crate::leanh::lean_dec_ref(v_inst_5790_);
        crate::leanh::lean_dec_ref(v_inst_5789_);
        crate::leanh::lean_dec_ref(v_inst_5788_);
        return v_k_5787_;
    } else {
        let mut v_getInheritedTraceOptions_5806_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_5806_ = crate::leanh::lean_ctor_get(v_inst_5788_, 2);
        crate::leanh::lean_inc(v_getInheritedTraceOptions_5806_);
        v___x_5807_ = crate::leanh::lean_box((v_collapsed_5795_) as usize);
        crate::leanh::lean_inc_n(v_toBind_5798_, 2);
        v___f_5808_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode_x27___redArg___lam__12___boxed as *mut core::ffi::c_void,
            18,
            17,
        );
        crate::leanh::lean_closure_set(v___f_5808_, 0, v_inst_5789_);
        crate::leanh::lean_closure_set(v___f_5808_, 1, v_inst_5790_);
        crate::leanh::lean_closure_set(v___f_5808_, 2, v_inst_5788_);
        crate::leanh::lean_closure_set(v___f_5808_, 3, v_inst_5791_);
        crate::leanh::lean_closure_set(v___f_5808_, 4, v_inst_5792_);
        crate::leanh::lean_closure_set(v___f_5808_, 5, v___f_5793_);
        crate::leanh::lean_closure_set(v___f_5808_, 6, v_cls_5794_);
        crate::leanh::lean_closure_set(v___f_5808_, 7, v___x_5807_);
        crate::leanh::lean_closure_set(v___f_5808_, 8, v_tag_5796_);
        crate::leanh::lean_closure_set(v___f_5808_, 9, v_opts_5804_);
        crate::leanh::lean_closure_set(v___f_5808_, 10, v_msg_5797_);
        crate::leanh::lean_closure_set(v___f_5808_, 11, v_toBind_5798_);
        crate::leanh::lean_closure_set(v___f_5808_, 12, v_k_5787_);
        crate::leanh::lean_closure_set(v___f_5808_, 13, v___f_5799_);
        crate::leanh::lean_closure_set(v___f_5808_, 14, v___f_5800_);
        crate::leanh::lean_closure_set(v___f_5808_, 15, v_inst_5801_);
        crate::leanh::lean_closure_set(v___f_5808_, 16, v_toPure_5802_);
        v___x_5809_ = crate::leanh::lean_apply_4(
            v_toBind_5798_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getInheritedTraceOptions_5806_,
            v___f_5803_,
        );
        v___x_5810_ = crate::leanh::lean_apply_4(
            v_toBind_5798_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5809_,
            v___f_5808_,
        );
        return v___x_5810_;
    }
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___lam__13___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5811_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5812_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5813_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5814_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_5815_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5816_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_5817_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_cls_5818_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_collapsed_5819_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_tag_5820_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_msg_5821_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_5822_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___f_5823_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_5824_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5825_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_toPure_5826_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_5827_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_opts_5828_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_5829_: u8 = 0;
    let mut v_res_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5829_ = (crate::leanh::lean_unbox(v_collapsed_5819_) as u8);
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
    mut v_inst_5832_: *mut crate::leanh::LeanObject,
    mut v_inst_5833_: *mut crate::leanh::LeanObject,
    mut v_inst_5834_: *mut crate::leanh::LeanObject,
    mut v_inst_5835_: *mut crate::leanh::LeanObject,
    mut v_inst_5836_: *mut crate::leanh::LeanObject,
    mut v_inst_5837_: *mut crate::leanh::LeanObject,
    mut v_inst_5838_: *mut crate::leanh::LeanObject,
    mut v_cls_5839_: *mut crate::leanh::LeanObject,
    mut v_k_5840_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5841_: u8,
    mut v_tag_5842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5843_ = crate::leanh::lean_ctor_get(v_inst_5832_, 0);
    v_toFunctor_5844_ = crate::leanh::lean_ctor_get(v_toApplicative_5843_, 0);
    v_toBind_5845_ = crate::leanh::lean_ctor_get(v_inst_5832_, 1);
    crate::leanh::lean_inc_n(v_toBind_5845_, 3);
    v_toPure_5846_ = crate::leanh::lean_ctor_get(v_toApplicative_5843_, 1);
    crate::leanh::lean_inc_n(v_toPure_5846_, 5);
    v_map_5847_ = crate::leanh::lean_ctor_get(v_toFunctor_5844_, 0);
    crate::leanh::lean_inc(v_map_5847_);
    v___f_5848_ = l_Lean_withTraceNode_x27___redArg___closed__0;
    v_msg_5849_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v_msg_5849_, 0, v_toPure_5846_);
    crate::leanh::lean_inc(v_inst_5836_);
    crate::leanh::lean_inc(v_cls_5839_);
    v___f_5850_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5850_, 0, v_toPure_5846_);
    crate::leanh::lean_closure_set(v___f_5850_, 1, v_cls_5839_);
    crate::leanh::lean_closure_set(v___f_5850_, 2, v_toBind_5845_);
    crate::leanh::lean_closure_set(v___f_5850_, 3, v_inst_5836_);
    v___f_5851_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5851_, 0, v_toPure_5846_);
    v___f_5852_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5852_, 0, v_toPure_5846_);
    v___f_5853_ = l_Lean_instExceptToTraceResult___closed__0;
    v___x_5854_ = crate::leanh::lean_box((v_collapsed_5841_) as usize);
    v___f_5855_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__13___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_5855_, 0, v_k_5840_);
    crate::leanh::lean_closure_set(v___f_5855_, 1, v_inst_5833_);
    crate::leanh::lean_closure_set(v___f_5855_, 2, v_inst_5837_);
    crate::leanh::lean_closure_set(v___f_5855_, 3, v_inst_5832_);
    crate::leanh::lean_closure_set(v___f_5855_, 4, v_inst_5834_);
    crate::leanh::lean_closure_set(v___f_5855_, 5, v_inst_5835_);
    crate::leanh::lean_closure_set(v___f_5855_, 6, v___f_5853_);
    crate::leanh::lean_closure_set(v___f_5855_, 7, v_cls_5839_);
    crate::leanh::lean_closure_set(v___f_5855_, 8, v___x_5854_);
    crate::leanh::lean_closure_set(v___f_5855_, 9, v_tag_5842_);
    crate::leanh::lean_closure_set(v___f_5855_, 10, v_msg_5849_);
    crate::leanh::lean_closure_set(v___f_5855_, 11, v_toBind_5845_);
    crate::leanh::lean_closure_set(v___f_5855_, 12, v___f_5852_);
    crate::leanh::lean_closure_set(v___f_5855_, 13, v___f_5851_);
    crate::leanh::lean_closure_set(v___f_5855_, 14, v_inst_5838_);
    crate::leanh::lean_closure_set(v___f_5855_, 15, v_toPure_5846_);
    crate::leanh::lean_closure_set(v___f_5855_, 16, v___f_5850_);
    v___x_5856_ = crate::leanh::lean_apply_4(
        v_toBind_5845_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5836_,
        v___f_5855_,
    );
    v___x_5857_ = crate::leanh::lean_apply_4(
        v_map_5847_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_5848_,
        v___x_5856_,
    );
    return v___x_5857_;
}
pub unsafe fn l_Lean_withTraceNode_x27___redArg___boxed(
    mut v_inst_5858_: *mut crate::leanh::LeanObject,
    mut v_inst_5859_: *mut crate::leanh::LeanObject,
    mut v_inst_5860_: *mut crate::leanh::LeanObject,
    mut v_inst_5861_: *mut crate::leanh::LeanObject,
    mut v_inst_5862_: *mut crate::leanh::LeanObject,
    mut v_inst_5863_: *mut crate::leanh::LeanObject,
    mut v_inst_5864_: *mut crate::leanh::LeanObject,
    mut v_cls_5865_: *mut crate::leanh::LeanObject,
    mut v_k_5866_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5867_: *mut crate::leanh::LeanObject,
    mut v_tag_5868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5869_: u8 = 0;
    let mut v_res_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5869_ = (crate::leanh::lean_unbox(v_collapsed_5867_) as u8);
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
    mut v_00_u03b1_5871_: *mut crate::leanh::LeanObject,
    mut v_m_5872_: *mut crate::leanh::LeanObject,
    mut v_inst_5873_: *mut crate::leanh::LeanObject,
    mut v_inst_5874_: *mut crate::leanh::LeanObject,
    mut v_inst_5875_: *mut crate::leanh::LeanObject,
    mut v_inst_5876_: *mut crate::leanh::LeanObject,
    mut v_inst_5877_: *mut crate::leanh::LeanObject,
    mut v_inst_5878_: *mut crate::leanh::LeanObject,
    mut v_inst_5879_: *mut crate::leanh::LeanObject,
    mut v_cls_5880_: *mut crate::leanh::LeanObject,
    mut v_k_5881_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5882_: u8,
    mut v_tag_5883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5884_ = crate::leanh::lean_ctor_get(v_inst_5873_, 0);
    v_toFunctor_5885_ = crate::leanh::lean_ctor_get(v_toApplicative_5884_, 0);
    v_toBind_5886_ = crate::leanh::lean_ctor_get(v_inst_5873_, 1);
    crate::leanh::lean_inc_n(v_toBind_5886_, 3);
    v_toPure_5887_ = crate::leanh::lean_ctor_get(v_toApplicative_5884_, 1);
    crate::leanh::lean_inc_n(v_toPure_5887_, 5);
    v_map_5888_ = crate::leanh::lean_ctor_get(v_toFunctor_5885_, 0);
    crate::leanh::lean_inc(v_map_5888_);
    v___f_5889_ = l_Lean_withTraceNode_x27___redArg___closed__0;
    v_msg_5890_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v_msg_5890_, 0, v_toPure_5887_);
    crate::leanh::lean_inc(v_inst_5877_);
    crate::leanh::lean_inc(v_cls_5880_);
    v___f_5891_ = crate::leanh::lean_alloc_closure(
        l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5891_, 0, v_toPure_5887_);
    crate::leanh::lean_closure_set(v___f_5891_, 1, v_cls_5880_);
    crate::leanh::lean_closure_set(v___f_5891_, 2, v_toBind_5886_);
    crate::leanh::lean_closure_set(v___f_5891_, 3, v_inst_5877_);
    v___f_5892_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5892_, 0, v_toPure_5887_);
    v___f_5893_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5893_, 0, v_toPure_5887_);
    v___f_5894_ = l_Lean_instExceptToTraceResult___closed__0;
    v___x_5895_ = crate::leanh::lean_box((v_collapsed_5882_) as usize);
    v___f_5896_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode_x27___redArg___lam__13___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_5896_, 0, v_k_5881_);
    crate::leanh::lean_closure_set(v___f_5896_, 1, v_inst_5874_);
    crate::leanh::lean_closure_set(v___f_5896_, 2, v_inst_5878_);
    crate::leanh::lean_closure_set(v___f_5896_, 3, v_inst_5873_);
    crate::leanh::lean_closure_set(v___f_5896_, 4, v_inst_5875_);
    crate::leanh::lean_closure_set(v___f_5896_, 5, v_inst_5876_);
    crate::leanh::lean_closure_set(v___f_5896_, 6, v___f_5894_);
    crate::leanh::lean_closure_set(v___f_5896_, 7, v_cls_5880_);
    crate::leanh::lean_closure_set(v___f_5896_, 8, v___x_5895_);
    crate::leanh::lean_closure_set(v___f_5896_, 9, v_tag_5883_);
    crate::leanh::lean_closure_set(v___f_5896_, 10, v_msg_5890_);
    crate::leanh::lean_closure_set(v___f_5896_, 11, v_toBind_5886_);
    crate::leanh::lean_closure_set(v___f_5896_, 12, v___f_5893_);
    crate::leanh::lean_closure_set(v___f_5896_, 13, v___f_5892_);
    crate::leanh::lean_closure_set(v___f_5896_, 14, v_inst_5879_);
    crate::leanh::lean_closure_set(v___f_5896_, 15, v_toPure_5887_);
    crate::leanh::lean_closure_set(v___f_5896_, 16, v___f_5891_);
    v___x_5897_ = crate::leanh::lean_apply_4(
        v_toBind_5886_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5877_,
        v___f_5896_,
    );
    v___x_5898_ = crate::leanh::lean_apply_4(
        v_map_5888_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_5889_,
        v___x_5897_,
    );
    return v___x_5898_;
}
pub unsafe fn l_Lean_withTraceNode_x27___boxed(
    mut v_00_u03b1_5899_: *mut crate::leanh::LeanObject,
    mut v_m_5900_: *mut crate::leanh::LeanObject,
    mut v_inst_5901_: *mut crate::leanh::LeanObject,
    mut v_inst_5902_: *mut crate::leanh::LeanObject,
    mut v_inst_5903_: *mut crate::leanh::LeanObject,
    mut v_inst_5904_: *mut crate::leanh::LeanObject,
    mut v_inst_5905_: *mut crate::leanh::LeanObject,
    mut v_inst_5906_: *mut crate::leanh::LeanObject,
    mut v_inst_5907_: *mut crate::leanh::LeanObject,
    mut v_cls_5908_: *mut crate::leanh::LeanObject,
    mut v_k_5909_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5910_: *mut crate::leanh::LeanObject,
    mut v_tag_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5912_: u8 = 0;
    let mut v_res_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5912_ = (crate::leanh::lean_unbox(v_collapsed_5910_) as u8);
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
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5922_ = l_Lean_registerTraceClass___auto__1___closed__3;
    v___x_5923_ = l_Lean_mkAtom(v___x_5922_);
    return v___x_5923_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5924_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__4_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__4,
    );
    v___x_5925_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5926_ = lean_array_push(v___x_5925_, v___x_5924_);
    return v___x_5926_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__5_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__5,
    );
    v___x_5928_ = l_Lean_registerTraceClass___auto__1___closed__2;
    v___x_5929_ = crate::leanh::lean_box(2);
    v___x_5930_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5930_, 0, v___x_5929_);
    crate::leanh::lean_ctor_set(v___x_5930_, 1, v___x_5928_);
    crate::leanh::lean_ctor_set(v___x_5930_, 2, v___x_5927_);
    return v___x_5930_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__6_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__6,
    );
    v___x_5932_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__7),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__7_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__7,
    );
    v___x_5935_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11;
    v___x_5936_ = crate::leanh::lean_box(2);
    v___x_5937_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5937_, 0, v___x_5936_);
    crate::leanh::lean_ctor_set(v___x_5937_, 1, v___x_5935_);
    crate::leanh::lean_ctor_set(v___x_5937_, 2, v___x_5934_);
    return v___x_5937_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__8),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__8_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__8,
    );
    v___x_5939_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5940_ = lean_array_push(v___x_5939_, v___x_5938_);
    return v___x_5940_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5941_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__9_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__9,
    );
    v___x_5942_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
    v___x_5943_ = crate::leanh::lean_box(2);
    v___x_5944_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5944_, 0, v___x_5943_);
    crate::leanh::lean_ctor_set(v___x_5944_, 1, v___x_5942_);
    crate::leanh::lean_ctor_set(v___x_5944_, 2, v___x_5941_);
    return v___x_5944_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5945_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__10_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__10,
    );
    v___x_5946_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5947_ = lean_array_push(v___x_5946_, v___x_5945_);
    return v___x_5947_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__11_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__11,
    );
    v___x_5949_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7;
    v___x_5950_ = crate::leanh::lean_box(2);
    v___x_5951_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5951_, 0, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 1, v___x_5949_);
    crate::leanh::lean_ctor_set(v___x_5951_, 2, v___x_5948_);
    return v___x_5951_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5952_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__12_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__12,
    );
    v___x_5953_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5;
    v___x_5954_ = lean_array_push(v___x_5953_, v___x_5952_);
    return v___x_5954_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5955_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__13_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__13,
    );
    v___x_5956_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4;
    v___x_5957_ = crate::leanh::lean_box(2);
    v___x_5958_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5958_, 0, v___x_5957_);
    crate::leanh::lean_ctor_set(v___x_5958_, 1, v___x_5956_);
    crate::leanh::lean_ctor_set(v___x_5958_, 2, v___x_5955_);
    return v___x_5958_;
}
pub unsafe fn _init_l_Lean_registerTraceClass___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5959_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Lean_registerTraceClass___auto__1___closed__14_once),
        _init_l_Lean_registerTraceClass___auto__1___closed__14,
    );
    return v___x_5959_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_5960_: *mut crate::leanh::LeanObject,
    mut v_x_5961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u64 = 0;
    let mut v_hash_5989_: u64 = 0;
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5961_) == 0 {
                    return v_x_5960_;
                } else {
                    v_key_5962_ = crate::leanh::lean_ctor_get(v_x_5961_, 0);
                    v_value_5963_ = crate::leanh::lean_ctor_get(v_x_5961_, 1);
                    v_tail_5964_ = crate::leanh::lean_ctor_get(v_x_5961_, 2);
                    v_isSharedCheck_5990_ = (!crate::leanh::lean_is_exclusive(v_x_5961_)) as u8;
                    if v_isSharedCheck_5990_ == 0 {
                        v___x_5966_ = v_x_5961_;
                        v_isShared_5967_ = v_isSharedCheck_5990_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5964_);
                        crate::leanh::lean_inc(v_value_5963_);
                        crate::leanh::lean_inc(v_key_5962_);
                        crate::leanh::lean_dec(v_x_5961_);
                        v___x_5966_ = crate::leanh::lean_box(0);
                        v_isShared_5967_ = v_isSharedCheck_5990_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5968_ = lean_array_get_size(v_x_5960_);
                if crate::leanh::lean_obj_tag(v_key_5962_) == 0 {
                    v___x_5988_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_5970_ = v___x_5988_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5989_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_5962_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
                crate::leanh::lean_inc(v___x_5982_);
                if v_isShared_5967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5966_, 2, v___x_5982_);
                    v___x_5984_ = v___x_5966_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_key_5962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 1, v_value_5963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 2, v___x_5982_);
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
    mut v_i_5991_: *mut crate::leanh::LeanObject,
    mut v_source_5992_: *mut crate::leanh::LeanObject,
    mut v_target_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: u8 = 0;
    let mut v_es_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5994_ = lean_array_get_size(v_source_5992_);
                v___x_5995_ = lean_nat_dec_lt(v_i_5991_, v___x_5994_);
                if v___x_5995_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5992_);
                    crate::leanh::lean_dec(v_i_5991_);
                    return v_target_5993_;
                } else {
                    v_es_5996_ = lean_array_fget(v_source_5992_, v_i_5991_);
                    v___x_5997_ = crate::leanh::lean_box(0);
                    v_source_5998_ = lean_array_fset(v_source_5992_, v_i_5991_, v___x_5997_);
                    v_target_5999_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_5993_, v_es_5996_);
                    v___x_6000_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6001_ = lean_nat_add(v_i_5991_, v___x_6000_);
                    crate::leanh::lean_dec(v_i_5991_);
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
    mut v_data_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6004_ = lean_array_get_size(v_data_6003_);
    v___x_6005_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6006_ = lean_nat_mul(v___x_6004_, v___x_6005_);
    v___x_6007_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6008_ = crate::leanh::lean_box(0);
    v___x_6009_ = lean_mk_array(v_nbuckets_6006_, v___x_6008_);
    v___x_6010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_6007_, v_data_6003_, v___x_6009_);
    return v___x_6010_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(
    mut v_m_6011_: *mut crate::leanh::LeanObject,
    mut v_a_6012_: *mut crate::leanh::LeanObject,
    mut v_b_6013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: u8 = 0;
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: u8 = 0;
    let mut v_val_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_unused_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u64 = 0;
    let mut v_hash_6056_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6014_ = crate::leanh::lean_ctor_get(v_m_6011_, 0);
                v_buckets_6015_ = crate::leanh::lean_ctor_get(v_m_6011_, 1);
                v___x_6016_ = lean_array_get_size(v_buckets_6015_);
                if crate::leanh::lean_obj_tag(v_a_6012_) == 0 {
                    v___x_6055_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
                    v___y_6018_ = v___x_6055_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6056_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_6012_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
                    crate::leanh::lean_inc_ref(v_buckets_6015_);
                    crate::leanh::lean_inc(v_size_6014_);
                    v_isSharedCheck_6052_ = (!crate::leanh::lean_is_exclusive(v_m_6011_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v_unused_6053_ = crate::leanh::lean_ctor_get(v_m_6011_, 1);
                        crate::leanh::lean_dec(v_unused_6053_);
                        v_unused_6054_ = crate::leanh::lean_ctor_get(v_m_6011_, 0);
                        crate::leanh::lean_dec(v_unused_6054_);
                        v___x_6033_ = v_m_6011_;
                        v_isShared_6034_ = v_isSharedCheck_6052_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_6011_);
                        v___x_6033_ = crate::leanh::lean_box(0);
                        v_isShared_6034_ = v_isSharedCheck_6052_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_6013_);
                    crate::leanh::lean_dec(v_a_6012_);
                    return v_m_6011_;
                }
            }
            2 => {
                v___x_6035_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_6036_ = lean_nat_add(v_size_6014_, v___x_6035_);
                crate::leanh::lean_dec(v_size_6014_);
                crate::leanh::lean_inc(v_bkt_6030_);
                v___x_6037_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6037_, 0, v_a_6012_);
                crate::leanh::lean_ctor_set(v___x_6037_, 1, v_b_6013_);
                crate::leanh::lean_ctor_set(v___x_6037_, 2, v_bkt_6030_);
                v_buckets_x27_6038_ = lean_array_uset(v_buckets_6015_, v___x_6029_, v___x_6037_);
                v___x_6039_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_6040_ = lean_nat_mul(v_size_x27_6036_, v___x_6039_);
                v___x_6041_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6042_ = lean_nat_div(v___x_6040_, v___x_6041_);
                crate::leanh::lean_dec(v___x_6040_);
                v___x_6043_ = lean_array_get_size(v_buckets_x27_6038_);
                v___x_6044_ = lean_nat_dec_le(v___x_6042_, v___x_6043_);
                crate::leanh::lean_dec(v___x_6042_);
                if v___x_6044_ == 0 {
                    v_val_6045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_6038_);
                    if v_isShared_6034_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6033_, 1, v_val_6045_);
                        crate::leanh::lean_ctor_set(v___x_6033_, 0, v_size_x27_6036_);
                        v___x_6047_ = v___x_6033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_size_x27_6036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 1, v_val_6045_);
                        v___x_6047_ = v_reuseFailAlloc_6048_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_6034_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6033_, 1, v_buckets_x27_6038_);
                        crate::leanh::lean_ctor_set(v___x_6033_, 0, v_size_x27_6036_);
                        v___x_6050_ = v___x_6033_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6051_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_size_x27_6036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_buckets_x27_6038_);
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
    mut v_traceClassName_6060_: *mut crate::leanh::LeanObject,
    mut v_inherited_6061_: u8,
    mut v_ref_6062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionName_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut v_unused_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6064_ = l_Lean_checkTraceOption___closed__1;
                v_optionName_6065_ = l_Lean_Name_append(v___x_6064_, v_traceClassName_6060_);
                v___x_6066_ = l_Lean_registerTraceClass___closed__0;
                v___x_6067_ = l_Lean_registerTraceClass___closed__1;
                v___x_6068_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_optionName_6065_, 2);
                v___x_6069_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6069_, 0, v_optionName_6065_);
                crate::leanh::lean_ctor_set(v___x_6069_, 1, v_ref_6062_);
                crate::leanh::lean_ctor_set(v___x_6069_, 2, v___x_6066_);
                crate::leanh::lean_ctor_set(v___x_6069_, 3, v___x_6067_);
                crate::leanh::lean_ctor_set(v___x_6069_, 4, v___x_6068_);
                v___x_6070_ = lean_register_option(v_optionName_6065_, v___x_6069_);
                if crate::leanh::lean_obj_tag(v___x_6070_) == 0 {
                    v_isSharedCheck_6086_ = (!crate::leanh::lean_is_exclusive(v___x_6070_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v_unused_6087_ = crate::leanh::lean_ctor_get(v___x_6070_, 0);
                        crate::leanh::lean_dec(v_unused_6087_);
                        v___x_6072_ = v___x_6070_;
                        v_isShared_6073_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6070_);
                        v___x_6072_ = crate::leanh::lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6086_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_optionName_6065_);
                    return v___x_6070_;
                }
            }
            1 => {
                if v_inherited_6061_ == 0 {
                    crate::leanh::lean_dec(v_optionName_6065_);
                    v___x_6074_ = crate::leanh::lean_box(0);
                    if v_isShared_6073_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6072_, 0, v___x_6074_);
                        v___x_6076_ = v___x_6072_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6074_);
                        v___x_6076_ = v_reuseFailAlloc_6077_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6078_ = l_Lean_inheritedTraceOptions;
                    v___x_6079_ = lean_st_ref_take(v___x_6078_);
                    v___x_6080_ = crate::leanh::lean_box(0);
                    v___x_6081_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_6079_, v_optionName_6065_, v___x_6080_);
                    v___x_6082_ = lean_st_ref_set(v___x_6078_, v___x_6081_);
                    if v_isShared_6073_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6072_, 0, v___x_6082_);
                        v___x_6084_ = v___x_6072_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6085_, 0, v___x_6082_);
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
    mut v_traceClassName_6088_: *mut crate::leanh::LeanObject,
    mut v_inherited_6089_: *mut crate::leanh::LeanObject,
    mut v_ref_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inherited_boxed_6092_: u8 = 0;
    let mut v_res_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inherited_boxed_6092_ = (crate::leanh::lean_unbox(v_inherited_6089_) as u8);
    v_res_6093_ =
        l_Lean_registerTraceClass(v_traceClassName_6088_, v_inherited_boxed_6092_, v_ref_6090_);
    return v_res_6093_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(
    mut v_00_u03b2_6094_: *mut crate::leanh::LeanObject,
    mut v_m_6095_: *mut crate::leanh::LeanObject,
    mut v_a_6096_: *mut crate::leanh::LeanObject,
    mut v_b_6097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6098_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_6095_, v_a_6096_, v_b_6097_);
    return v___x_6098_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(
    mut v_00_u03b2_6099_: *mut crate::leanh::LeanObject,
    mut v_data_6100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_6100_);
    return v___x_6101_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6102_: *mut crate::leanh::LeanObject,
    mut v_i_6103_: *mut crate::leanh::LeanObject,
    mut v_source_6104_: *mut crate::leanh::LeanObject,
    mut v_target_6105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6106_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_6103_, v_source_6104_, v_target_6105_);
    return v___x_6106_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_6107_: *mut crate::leanh::LeanObject,
    mut v_x_6108_: *mut crate::leanh::LeanObject,
    mut v_x_6109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_6108_, v_x_6109_);
    return v___x_6110_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6120_ = l_Lean_addTrace___redArg___lam__0___closed__1;
    v___x_6121_ = l_String_toRawSubstring_x27(v___x_6120_);
    return v___x_6121_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6126_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12;
    v___x_6127_ = l_String_toRawSubstring_x27(v___x_6126_);
    return v___x_6127_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6133_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18;
    v___x_6134_ = l_String_toRawSubstring_x27(v___x_6133_);
    return v___x_6134_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6162_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_6162_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6188_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40;
    v___x_6189_ = l_String_toRawSubstring_x27(v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6224_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57;
    v___x_6225_ = l_String_toRawSubstring_x27(v___x_6224_);
    return v___x_6225_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
    mut v_id_6247_: *mut crate::leanh::LeanObject,
    mut v_s_6248_: *mut crate::leanh::LeanObject,
    mut v_a_6249_: *mut crate::leanh::LeanObject,
    mut v_a_6250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: u8 = 0;
    let mut v_quotContext_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: u8 = 0;
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_s_6248_);
                v___x_6397_ = l_Lean_Syntax_getKind(v_s_6248_);
                v___x_6398_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49;
                v___x_6399_ = lean_name_eq(v___x_6397_, v___x_6398_);
                crate::leanh::lean_dec(v___x_6397_);
                if v___x_6399_ == 0 {
                    v_quotContext_6400_ = crate::leanh::lean_ctor_get(v_a_6249_, 1);
                    v_currMacroScope_6401_ = crate::leanh::lean_ctor_get(v_a_6249_, 2);
                    v_ref_6402_ = crate::leanh::lean_ctor_get(v_a_6249_, 5);
                    v___x_6403_ = l_Lean_SourceInfo_fromRef(v_ref_6402_, v___x_6399_);
                    v___x_6404_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51;
                    v___x_6405_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52;
                    v___x_6406_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5;
                    crate::leanh::lean_inc_n(v___x_6403_, 8);
                    v___x_6407_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6407_, 0, v___x_6403_);
                    crate::leanh::lean_ctor_set(v___x_6407_, 1, v___x_6406_);
                    v___x_6408_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7;
                    v___x_6409_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once
                        ),
                        _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8,
                    );
                    v___x_6410_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_n(v_currMacroScope_6401_, 3);
                    crate::leanh::lean_inc_n(v_quotContext_6400_, 3);
                    v___x_6411_ = l_Lean_addMacroScope(
                        v_quotContext_6400_,
                        v___x_6410_,
                        v_currMacroScope_6401_,
                    );
                    v___x_6412_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55;
                    v___x_6413_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6413_, 0, v___x_6403_);
                    crate::leanh::lean_ctor_set(v___x_6413_, 1, v___x_6409_);
                    crate::leanh::lean_ctor_set(v___x_6413_, 2, v___x_6411_);
                    crate::leanh::lean_ctor_set(v___x_6413_, 3, v___x_6412_);
                    v___x_6414_ = l_Lean_Syntax_node1(v___x_6403_, v___x_6408_, v___x_6413_);
                    v___x_6415_ =
                        l_Lean_Syntax_node2(v___x_6403_, v___x_6405_, v___x_6407_, v___x_6414_);
                    v___x_6416_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56;
                    v___x_6417_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6417_, 0, v___x_6403_);
                    crate::leanh::lean_ctor_set(v___x_6417_, 1, v___x_6416_);
                    v___x_6418_ =
                        l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
                    v___x_6419_ = crate::leanh::lean_obj_once(
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
                    v___x_6423_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6423_, 0, v___x_6403_);
                    crate::leanh::lean_ctor_set(v___x_6423_, 1, v___x_6419_);
                    crate::leanh::lean_ctor_set(v___x_6423_, 2, v___x_6421_);
                    crate::leanh::lean_ctor_set(v___x_6423_, 3, v___x_6422_);
                    v___x_6424_ = l_Lean_Syntax_node1(v___x_6403_, v___x_6418_, v___x_6423_);
                    v___x_6425_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15;
                    v___x_6426_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6426_, 0, v___x_6403_);
                    crate::leanh::lean_ctor_set(v___x_6426_, 1, v___x_6425_);
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
                    v_quotContext_6428_ = crate::leanh::lean_ctor_get(v_a_6249_, 1);
                    v_currMacroScope_6429_ = crate::leanh::lean_ctor_get(v_a_6249_, 2);
                    v_ref_6430_ = crate::leanh::lean_ctor_get(v_a_6249_, 5);
                    v___x_6431_ = 0;
                    v___x_6432_ = l_Lean_SourceInfo_fromRef(v_ref_6430_, v___x_6431_);
                    v___x_6433_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66;
                    v___x_6434_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67;
                    crate::leanh::lean_inc(v___x_6432_);
                    v___x_6435_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6435_, 0, v___x_6432_);
                    crate::leanh::lean_ctor_set(v___x_6435_, 1, v___x_6434_);
                    v___x_6436_ =
                        l_Lean_Syntax_node2(v___x_6432_, v___x_6433_, v___x_6435_, v_s_6248_);
                    crate::leanh::lean_inc(v_currMacroScope_6429_);
                    crate::leanh::lean_inc(v_quotContext_6428_);
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
                crate::leanh::lean_inc_n(v___y_6262_, 8);
                crate::leanh::lean_inc(v___y_6264_);
                crate::leanh::lean_inc_n(v___y_6261_, 29);
                v___x_6276_ = l_Lean_Syntax_node5(
                    v___y_6261_,
                    v___y_6264_,
                    v___y_6270_,
                    v___y_6262_,
                    v___y_6262_,
                    v___y_6259_,
                    v___y_6275_,
                );
                crate::leanh::lean_inc(v___y_6265_);
                v___x_6277_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6265_, v___x_6276_);
                crate::leanh::lean_inc(v___y_6255_);
                v___x_6278_ = l_Lean_Syntax_node4(
                    v___y_6261_,
                    v___y_6255_,
                    v___y_6272_,
                    v___y_6262_,
                    v___y_6263_,
                    v___x_6277_,
                );
                crate::leanh::lean_inc_n(v___y_6258_, 3);
                v___x_6279_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6258_, v___x_6278_, v___y_6262_);
                v___x_6280_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_6268_, 7);
                crate::leanh::lean_inc_ref_n(v___y_6273_, 7);
                crate::leanh::lean_inc_ref_n(v___y_6269_, 10);
                v___x_6281_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6280_);
                v___x_6282_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1;
                v___x_6283_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6283_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6283_, 1, v___x_6282_);
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
                v___x_6291_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6291_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6291_, 1, v___x_6290_);
                v___x_6292_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7;
                v___x_6293_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8,
                );
                v___x_6294_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v___y_6254_, 2);
                crate::leanh::lean_inc_n(v___y_6271_, 2);
                v___x_6295_ = l_Lean_addMacroScope(v___y_6271_, v___x_6294_, v___y_6254_);
                v___x_6296_ = l_Lean_Name_mkStr1(v___y_6269_);
                v___x_6297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6297_, 0, v___x_6296_);
                crate::leanh::lean_inc_n(v___y_6253_, 2);
                v___x_6298_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6298_, 0, v___x_6297_);
                crate::leanh::lean_ctor_set(v___x_6298_, 1, v___y_6253_);
                v___x_6299_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6299_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6299_, 1, v___x_6293_);
                crate::leanh::lean_ctor_set(v___x_6299_, 2, v___x_6295_);
                crate::leanh::lean_ctor_set(v___x_6299_, 3, v___x_6298_);
                v___x_6300_ = l_Lean_Syntax_node1(v___y_6261_, v___x_6292_, v___x_6299_);
                v___x_6301_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6289_, v___x_6291_, v___x_6300_);
                v___x_6302_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9;
                v___x_6303_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6302_);
                v___x_6304_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10;
                v___x_6305_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6305_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6305_, 1, v___x_6304_);
                v___x_6306_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11;
                v___x_6307_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6306_);
                v___x_6308_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___x_6310_);
                v___x_6311_ = l_Lean_addMacroScope(v___y_6271_, v___x_6310_, v___y_6254_);
                v___x_6312_ = crate::leanh::lean_box(0);
                v___x_6313_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6313_, 0, v___x_6310_);
                crate::leanh::lean_ctor_set(v___x_6313_, 1, v___x_6312_);
                v___x_6314_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6314_, 0, v___x_6313_);
                crate::leanh::lean_ctor_set(v___x_6314_, 1, v___y_6253_);
                v___x_6315_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6315_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6315_, 1, v___x_6308_);
                crate::leanh::lean_ctor_set(v___x_6315_, 2, v___x_6311_);
                crate::leanh::lean_ctor_set(v___x_6315_, 3, v___x_6314_);
                crate::leanh::lean_inc(v___y_6257_);
                crate::leanh::lean_inc_n(v___y_6260_, 4);
                v___x_6316_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6260_, v___y_6257_);
                crate::leanh::lean_inc(v___x_6307_);
                v___x_6317_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6307_, v___x_6315_, v___x_6316_);
                v___x_6318_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6303_, v___x_6305_, v___x_6317_);
                v___x_6319_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15;
                v___x_6320_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6320_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6320_, 1, v___x_6319_);
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
                v___x_6324_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6324_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                v___x_6325_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17;
                v___x_6326_ =
                    l_Lean_Name_mkStr4(v___y_6269_, v___y_6273_, v___y_6268_, v___x_6325_);
                v___x_6327_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___x_6329_);
                v___x_6330_ = l_Lean_addMacroScope(v___y_6271_, v___x_6329_, v___y_6254_);
                v___x_6331_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6331_, 0, v___x_6329_);
                crate::leanh::lean_ctor_set(v___x_6331_, 1, v___x_6312_);
                v___x_6332_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6332_, 0, v___x_6331_);
                crate::leanh::lean_ctor_set(v___x_6332_, 1, v___y_6253_);
                v___x_6333_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6333_, 0, v___y_6261_);
                crate::leanh::lean_ctor_set(v___x_6333_, 1, v___x_6327_);
                crate::leanh::lean_ctor_set(v___x_6333_, 2, v___x_6330_);
                crate::leanh::lean_ctor_set(v___x_6333_, 3, v___x_6332_);
                v___x_6334_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6260_, v___y_6257_, v___y_6252_);
                v___x_6335_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___x_6307_, v___x_6333_, v___x_6334_);
                v___x_6336_ = l_Lean_Syntax_node1(v___y_6261_, v___x_6326_, v___x_6335_);
                v___x_6337_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6258_, v___x_6336_, v___y_6262_);
                v___x_6338_ = l_Lean_Syntax_node1(v___y_6261_, v___y_6260_, v___x_6337_);
                crate::leanh::lean_inc_n(v___y_6266_, 2);
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
                crate::leanh::lean_inc(v___y_6274_);
                v___x_6344_ =
                    l_Lean_Syntax_node2(v___y_6261_, v___y_6274_, v___y_6256_, v___x_6343_);
                v___x_6345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6345_, 0, v___x_6344_);
                crate::leanh::lean_ctor_set(v___x_6345_, 1, v___y_6267_);
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
                crate::leanh::lean_inc_n(v___x_6353_, 7);
                v___x_6359_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6359_, 0, v___x_6353_);
                crate::leanh::lean_ctor_set(v___x_6359_, 1, v___x_6358_);
                v___x_6360_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25;
                v___x_6361_ = l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9;
                v___x_6362_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27;
                v___x_6363_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29;
                v___x_6364_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30;
                v___x_6365_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6365_, 0, v___x_6353_);
                crate::leanh::lean_ctor_set(v___x_6365_, 1, v___x_6364_);
                v___x_6366_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31,
                );
                v___x_6367_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6367_, 0, v___x_6353_);
                crate::leanh::lean_ctor_set(v___x_6367_, 1, v___x_6361_);
                crate::leanh::lean_ctor_set(v___x_6367_, 2, v___x_6366_);
                v___x_6368_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33;
                crate::leanh::lean_inc_ref(v___x_6367_);
                v___x_6369_ = l_Lean_Syntax_node1(v___x_6353_, v___x_6368_, v___x_6367_);
                v___x_6370_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35;
                v___x_6371_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37;
                v___x_6372_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39;
                v___x_6373_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once
                    ),
                    _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41,
                );
                v___x_6374_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42;
                crate::leanh::lean_inc(v_currMacroScope_6349_);
                crate::leanh::lean_inc(v_quotContext_6348_);
                v___x_6375_ =
                    l_Lean_addMacroScope(v_quotContext_6348_, v___x_6374_, v_currMacroScope_6349_);
                v___x_6376_ = crate::leanh::lean_box(0);
                v___x_6377_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6377_, 0, v___x_6353_);
                crate::leanh::lean_ctor_set(v___x_6377_, 1, v___x_6373_);
                crate::leanh::lean_ctor_set(v___x_6377_, 2, v___x_6375_);
                crate::leanh::lean_ctor_set(v___x_6377_, 3, v___x_6376_);
                crate::leanh::lean_inc_ref(v___x_6377_);
                v___x_6378_ = l_Lean_Syntax_node1(v___x_6353_, v___x_6372_, v___x_6377_);
                v___x_6379_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43;
                v___x_6380_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6380_, 0, v___x_6353_);
                crate::leanh::lean_ctor_set(v___x_6380_, 1, v___x_6379_);
                v___x_6381_ = l_Lean_Syntax_getId(v_id_6247_);
                v___x_6382_ = lean_erase_macro_scopes(v___x_6381_);
                crate::leanh::lean_inc(v___x_6382_);
                v___x_6383_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_6376_,
                    v___x_6382_,
                );
                if crate::leanh::lean_obj_tag(v___x_6383_) == 0 {
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
                    crate::leanh::lean_dec(v___x_6382_);
                    v_val_6385_ = crate::leanh::lean_ctor_get(v___x_6383_, 0);
                    crate::leanh::lean_inc(v_val_6385_);
                    crate::leanh::lean_dec_ref_known(v___x_6383_, 1);
                    v___x_6386_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45;
                    v___x_6387_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46;
                    v___x_6388_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47;
                    v___x_6389_ = lean_string_intercalate(v___x_6388_, v_val_6385_);
                    v___x_6390_ = lean_string_append(v___x_6387_, v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    v___x_6391_ = crate::leanh::lean_box(2);
                    v___x_6392_ = l_Lean_Syntax_mkNameLit(v___x_6390_, v___x_6391_);
                    v___x_6393_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6394_ = lean_mk_empty_array_with_capacity(v___x_6393_);
                    v___x_6395_ = lean_array_push(v___x_6394_, v___x_6392_);
                    v___x_6396_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6396_, 0, v___x_6391_);
                    crate::leanh::lean_ctor_set(v___x_6396_, 1, v___x_6386_);
                    crate::leanh::lean_ctor_set(v___x_6396_, 2, v___x_6395_);
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
    mut v_id_6437_: *mut crate::leanh::LeanObject,
    mut v_s_6438_: *mut crate::leanh::LeanObject,
    mut v_a_6439_: *mut crate::leanh::LeanObject,
    mut v_a_6440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6441_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
        v_id_6437_, v_s_6438_, v_a_6439_, v_a_6440_,
    );
    crate::leanh::lean_dec_ref(v_a_6439_);
    crate::leanh::lean_dec(v_id_6437_);
    return v_res_6441_;
}
pub unsafe fn l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(
    mut v_x_6496_: *mut crate::leanh::LeanObject,
    mut v_a_6497_: *mut crate::leanh::LeanObject,
    mut v_a_6498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: u8 = 0;
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6512_: u8 = 0;
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6499_ = l_Lean_doElemTrace_x5b___x5d_____00__closed__1;
                crate::leanh::lean_inc(v_x_6496_);
                v___x_6500_ = l_Lean_Syntax_isOfKind(v_x_6496_, v___x_6499_);
                if v___x_6500_ == 0 {
                    crate::leanh::lean_dec(v_x_6496_);
                    v___x_6501_ = crate::leanh::lean_box(1);
                    v___x_6502_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6502_, 0, v___x_6501_);
                    crate::leanh::lean_ctor_set(v___x_6502_, 1, v_a_6498_);
                    return v___x_6502_;
                } else {
                    v___x_6503_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6504_ = l_Lean_Syntax_getArg(v_x_6496_, v___x_6503_);
                    v___x_6505_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6506_ = l_Lean_Syntax_getArg(v_x_6496_, v___x_6505_);
                    crate::leanh::lean_dec(v_x_6496_);
                    v___x_6507_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(
                        v___x_6504_,
                        v___x_6506_,
                        v_a_6497_,
                        v_a_6498_,
                    );
                    crate::leanh::lean_dec(v___x_6504_);
                    v_a_6508_ = crate::leanh::lean_ctor_get(v___x_6507_, 0);
                    v_a_6509_ = crate::leanh::lean_ctor_get(v___x_6507_, 1);
                    v_isSharedCheck_6516_ = (!crate::leanh::lean_is_exclusive(v___x_6507_)) as u8;
                    if v_isSharedCheck_6516_ == 0 {
                        v___x_6511_ = v___x_6507_;
                        v_isShared_6512_ = v_isSharedCheck_6516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6509_);
                        crate::leanh::lean_inc(v_a_6508_);
                        crate::leanh::lean_dec(v___x_6507_);
                        v___x_6511_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6515_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6515_, 0, v_a_6508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6515_, 1, v_a_6509_);
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
    mut v_x_6517_: *mut crate::leanh::LeanObject,
    mut v_a_6518_: *mut crate::leanh::LeanObject,
    mut v_a_6519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6520_ =
        l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(
            v_x_6517_, v_a_6518_, v_a_6519_,
        );
    crate::leanh::lean_dec_ref(v_a_6518_);
    return v_res_6520_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(
    mut v_inst_6521_: *mut crate::leanh::LeanObject,
    mut v_inst_6522_: *mut crate::leanh::LeanObject,
    mut v_inst_6523_: *mut crate::leanh::LeanObject,
    mut v_inst_6524_: *mut crate::leanh::LeanObject,
    mut v_always_6525_: *mut crate::leanh::LeanObject,
    mut v_inst_6526_: *mut crate::leanh::LeanObject,
    mut v_cls_6527_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6528_: u8,
    mut v_tag_6529_: *mut crate::leanh::LeanObject,
    mut v_opts_6530_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6531_: u8,
    mut v_oldTraces_6532_: *mut crate::leanh::LeanObject,
    mut v_ref_6533_: *mut crate::leanh::LeanObject,
    mut v_msg_6534_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6541_: u8 = 0;
    let mut v_fst_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v___f_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: u8 = 0;
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: f64 = 0.0;
    let mut v_data_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v_data_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: f64 = 0.0;
    let mut v___x_6573_: f64 = 0.0;
    let mut v_reuseFailAlloc_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: u8 = 0;
    let mut v_toBind_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyTraceState_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6583_: f64 = 0.0;
    let mut v___x_6584_: f64 = 0.0;
    let mut v___x_6585_: f64 = 0.0;
    let mut v___x_6586_: f64 = 0.0;
    let mut v___x_6587_: u8 = 0;
    let mut v___x_6588_: u8 = 0;
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: u8 = 0;
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: f64 = 0.0;
    let mut v___x_6597_: f64 = 0.0;
    let mut v___x_6598_: f64 = 0.0;
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: f64 = 0.0;
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6536_ = l_Lean_KVMap_instValueBool;
                v_snd_6537_ = crate::leanh::lean_ctor_get(v_resStartStop_6535_, 1);
                v_fst_6538_ = crate::leanh::lean_ctor_get(v_resStartStop_6535_, 0);
                v_isSharedCheck_6604_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_6535_)) as u8;
                if v_isSharedCheck_6604_ == 0 {
                    v___x_6540_ = v_resStartStop_6535_;
                    v_isShared_6541_ = v_isSharedCheck_6604_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6537_);
                    crate::leanh::lean_inc(v_fst_6538_);
                    crate::leanh::lean_dec(v_resStartStop_6535_);
                    v___x_6540_ = crate::leanh::lean_box(0);
                    v_isShared_6541_ = v_isSharedCheck_6604_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_6542_ = crate::leanh::lean_ctor_get(v_snd_6537_, 0);
                v_snd_6543_ = crate::leanh::lean_ctor_get(v_snd_6537_, 1);
                v_isSharedCheck_6603_ = (!crate::leanh::lean_is_exclusive(v_snd_6537_)) as u8;
                if v_isSharedCheck_6603_ == 0 {
                    v___x_6545_ = v_snd_6537_;
                    v_isShared_6546_ = v_isSharedCheck_6603_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6543_);
                    crate::leanh::lean_inc(v_fst_6542_);
                    crate::leanh::lean_dec(v_snd_6537_);
                    v___x_6545_ = crate::leanh::lean_box(0);
                    v_isShared_6546_ = v_isSharedCheck_6603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_oldTraces_6532_);
                v___f_6547_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6547_, 0, v_oldTraces_6532_);
                crate::leanh::lean_inc(v_fst_6538_);
                crate::leanh::lean_inc_ref(v_inst_6521_);
                v___f_6548_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_6548_, 0, v_always_6525_);
                crate::leanh::lean_closure_set(v___f_6548_, 1, v_inst_6521_);
                crate::leanh::lean_closure_set(v___f_6548_, 2, v_fst_6538_);
                v___x_6555_ = l_Lean_trace_profiler;
                v___x_6556_ = l_Lean_Option_get___redArg(v___x_6536_, v_opts_6530_, v___x_6555_);
                v___x_6588_ = (crate::leanh::lean_unbox(v___x_6556_) as u8);
                if v___x_6588_ == 0 {
                    v___x_6589_ = (crate::leanh::lean_unbox(v___x_6556_) as u8);
                    v___y_6577_ = v___x_6589_;
                    state = 7;
                    continue;
                } else {
                    v___x_6590_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_6591_ =
                        l_Lean_Option_get___redArg(v___x_6536_, v_opts_6530_, v___x_6590_);
                    v___x_6592_ = (crate::leanh::lean_unbox(v___x_6591_) as u8);
                    crate::leanh::lean_dec(v___x_6591_);
                    if v___x_6592_ == 0 {
                        v___x_6593_ = l_Lean_KVMap_instValueNat;
                        v___x_6594_ = l_Lean_trace_profiler_threshold;
                        v___x_6595_ =
                            l_Lean_Option_get___redArg(v___x_6593_, v_opts_6530_, v___x_6594_);
                        v___x_6596_ = lean_float_of_nat(v___x_6595_);
                        v___x_6597_ = crate::leanh::lean_float_once(
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
                v_toBind_6552_ = crate::leanh::lean_ctor_get(v_inst_6521_, 1);
                crate::leanh::lean_inc(v_toBind_6552_);
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
                v___x_6554_ = crate::leanh::lean_apply_4(
                    v_toBind_6552_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6553_,
                    v___f_6548_,
                );
                return v___x_6554_;
            }
            4 => {
                v_result_6558_ = crate::leanh::lean_apply_1(v_inst_6526_, v_fst_6538_);
                v___x_6559_ = (crate::leanh::lean_unbox(v_result_6558_) as u8);
                v___x_6560_ = l_Lean_TraceResult_toEmoji(v___x_6559_);
                v___x_6561_ = l_Lean_stringToMessageData(v___x_6560_);
                v___x_6562_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
                if v_isShared_6546_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6545_, 7);
                    crate::leanh::lean_ctor_set(v___x_6545_, 1, v___x_6562_);
                    crate::leanh::lean_ctor_set(v___x_6545_, 0, v___x_6561_);
                    v___x_6564_ = v___x_6545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 1, v___x_6562_);
                    v___x_6564_ = v_reuseFailAlloc_6575_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6541_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6540_, 7);
                    crate::leanh::lean_ctor_set(v___x_6540_, 1, v_msg_6534_);
                    crate::leanh::lean_ctor_set(v___x_6540_, 0, v___x_6564_);
                    v_msg_6566_ = v___x_6540_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6574_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6574_, 1, v_msg_6534_);
                    v_msg_6566_ = v_reuseFailAlloc_6574_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6567_, 0, v_result_6558_);
                v___x_6568_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_addTrace___redArg___lam__0___closed__0_once),
                    _init_l_Lean_addTrace___redArg___lam__0___closed__0,
                );
                crate::leanh::lean_inc_ref(v_tag_6529_);
                crate::leanh::lean_inc_ref(v___x_6567_);
                crate::leanh::lean_inc(v_cls_6527_);
                v_data_6569_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_6569_, 0, v_cls_6527_);
                crate::leanh::lean_ctor_set(v_data_6569_, 1, v___x_6567_);
                crate::leanh::lean_ctor_set(v_data_6569_, 2, v_tag_6529_);
                crate::leanh::lean_ctor_set_float(
                    v_data_6569_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6568_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_6569_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6568_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_6569_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_6528_,
                );
                v___x_6570_ = (crate::leanh::lean_unbox(v___x_6556_) as u8);
                crate::leanh::lean_dec(v___x_6556_);
                if v___x_6570_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6567_, 1);
                    crate::leanh::lean_dec(v_snd_6543_);
                    crate::leanh::lean_dec(v_fst_6542_);
                    crate::leanh::lean_dec_ref(v_tag_6529_);
                    crate::leanh::lean_dec(v_cls_6527_);
                    v___y_6550_ = v_msg_6566_;
                    v_data_6551_ = v_data_6569_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_6569_, 3);
                    v_data_6571_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_6571_, 0, v_cls_6527_);
                    crate::leanh::lean_ctor_set(v_data_6571_, 1, v___x_6567_);
                    crate::leanh::lean_ctor_set(v_data_6571_, 2, v_tag_6529_);
                    v___x_6572_ = crate::leanh::lean_unbox_float(v_fst_6542_);
                    crate::leanh::lean_dec(v_fst_6542_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6571_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6572_,
                    );
                    v___x_6573_ = crate::leanh::lean_unbox_float(v_snd_6543_);
                    crate::leanh::lean_dec(v_snd_6543_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6571_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6573_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_6571_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
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
                        crate::leanh::lean_dec(v___x_6556_);
                        crate::leanh::lean_del_object(v___x_6545_);
                        crate::leanh::lean_dec(v_snd_6543_);
                        crate::leanh::lean_dec(v_fst_6542_);
                        crate::leanh::lean_del_object(v___x_6540_);
                        crate::leanh::lean_dec(v_fst_6538_);
                        crate::leanh::lean_dec_ref(v_msg_6534_);
                        crate::leanh::lean_dec(v_ref_6533_);
                        crate::leanh::lean_dec_ref(v_oldTraces_6532_);
                        crate::leanh::lean_dec_ref(v_tag_6529_);
                        crate::leanh::lean_dec(v_cls_6527_);
                        crate::leanh::lean_dec_ref(v_inst_6526_);
                        crate::leanh::lean_dec(v_inst_6524_);
                        crate::leanh::lean_dec_ref(v_inst_6523_);
                        v_toBind_6578_ = crate::leanh::lean_ctor_get(v_inst_6521_, 1);
                        crate::leanh::lean_inc(v_toBind_6578_);
                        crate::leanh::lean_dec_ref(v_inst_6521_);
                        v_modifyTraceState_6579_ = crate::leanh::lean_ctor_get(v_inst_6522_, 0);
                        crate::leanh::lean_inc(v_modifyTraceState_6579_);
                        crate::leanh::lean_dec_ref(v_inst_6522_);
                        v___x_6580_ =
                            crate::leanh::lean_apply_1(v_modifyTraceState_6579_, v___f_6547_);
                        v___x_6581_ = crate::leanh::lean_apply_4(
                            v_toBind_6578_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_6580_,
                            v___f_6548_,
                        );
                        return v___x_6581_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_6547_);
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_6547_);
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_6584_ = crate::leanh::lean_unbox_float(v_snd_6543_);
                v___x_6585_ = crate::leanh::lean_unbox_float(v_fst_6542_);
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
    mut v_inst_6605_: *mut crate::leanh::LeanObject,
    mut v_inst_6606_: *mut crate::leanh::LeanObject,
    mut v_inst_6607_: *mut crate::leanh::LeanObject,
    mut v_inst_6608_: *mut crate::leanh::LeanObject,
    mut v_always_6609_: *mut crate::leanh::LeanObject,
    mut v_inst_6610_: *mut crate::leanh::LeanObject,
    mut v_cls_6611_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6612_: *mut crate::leanh::LeanObject,
    mut v_tag_6613_: *mut crate::leanh::LeanObject,
    mut v_opts_6614_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6615_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_6616_: *mut crate::leanh::LeanObject,
    mut v_ref_6617_: *mut crate::leanh::LeanObject,
    mut v_msg_6618_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_6620_: u8 = 0;
    let mut v_clsEnabled_boxed_6621_: u8 = 0;
    let mut v_res_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6620_ = (crate::leanh::lean_unbox(v_collapsed_6612_) as u8);
    v_clsEnabled_boxed_6621_ = (crate::leanh::lean_unbox(v_clsEnabled_6615_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_6614_);
    return v_res_6622_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(
    mut v_00_u03b1_6623_: *mut crate::leanh::LeanObject,
    mut v_m_6624_: *mut crate::leanh::LeanObject,
    mut v_inst_6625_: *mut crate::leanh::LeanObject,
    mut v_inst_6626_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_6627_: *mut crate::leanh::LeanObject,
    mut v_inst_6628_: *mut crate::leanh::LeanObject,
    mut v_inst_6629_: *mut crate::leanh::LeanObject,
    mut v_always_6630_: *mut crate::leanh::LeanObject,
    mut v_inst_6631_: *mut crate::leanh::LeanObject,
    mut v_cls_6632_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6633_: u8,
    mut v_tag_6634_: *mut crate::leanh::LeanObject,
    mut v_opts_6635_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6636_: u8,
    mut v_oldTraces_6637_: *mut crate::leanh::LeanObject,
    mut v_ref_6638_: *mut crate::leanh::LeanObject,
    mut v_msg_6639_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_6642_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_m_6643_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6644_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6645_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_00_u03b5_6646_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6647_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_6648_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_always_6649_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_6650_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_cls_6651_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_collapsed_6652_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_tag_6653_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_opts_6654_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_clsEnabled_6655_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_oldTraces_6656_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_ref_6657_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_msg_6658_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_resStartStop_6659_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6660_: u8 = 0;
    let mut v_clsEnabled_boxed_6661_: u8 = 0;
    let mut v_res_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6660_ = (crate::leanh::lean_unbox(v_collapsed_6652_) as u8);
    v_clsEnabled_boxed_6661_ = (crate::leanh::lean_unbox(v_clsEnabled_6655_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_6654_);
    return v_res_6662_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__0(
    mut v_inst_6663_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6665_ = crate::leanh::lean_apply_1(v_inst_6663_, v_____do__lift_6664_);
    return v___x_6665_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__1(
    mut v_inst_6666_: *mut crate::leanh::LeanObject,
    mut v_inst_6667_: *mut crate::leanh::LeanObject,
    mut v_inst_6668_: *mut crate::leanh::LeanObject,
    mut v_inst_6669_: *mut crate::leanh::LeanObject,
    mut v_always_6670_: *mut crate::leanh::LeanObject,
    mut v_inst_6671_: *mut crate::leanh::LeanObject,
    mut v_cls_6672_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6673_: u8,
    mut v_tag_6674_: *mut crate::leanh::LeanObject,
    mut v_opts_6675_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6676_: u8,
    mut v_oldTraces_6677_: *mut crate::leanh::LeanObject,
    mut v_ref_6678_: *mut crate::leanh::LeanObject,
    mut v_msg_6679_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_6682_: *mut crate::leanh::LeanObject,
    mut v_inst_6683_: *mut crate::leanh::LeanObject,
    mut v_inst_6684_: *mut crate::leanh::LeanObject,
    mut v_inst_6685_: *mut crate::leanh::LeanObject,
    mut v_always_6686_: *mut crate::leanh::LeanObject,
    mut v_inst_6687_: *mut crate::leanh::LeanObject,
    mut v_cls_6688_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6689_: *mut crate::leanh::LeanObject,
    mut v_tag_6690_: *mut crate::leanh::LeanObject,
    mut v_opts_6691_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6692_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_6693_: *mut crate::leanh::LeanObject,
    mut v_ref_6694_: *mut crate::leanh::LeanObject,
    mut v_msg_6695_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_6697_: u8 = 0;
    let mut v_clsEnabled_boxed_6698_: u8 = 0;
    let mut v_res_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6697_ = (crate::leanh::lean_unbox(v_collapsed_6689_) as u8);
    v_clsEnabled_boxed_6698_ = (crate::leanh::lean_unbox(v_clsEnabled_6692_) as u8);
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
    crate::leanh::lean_dec_ref(v_opts_6691_);
    return v_res_6699_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__10(
    mut v_always_6700_: *mut crate::leanh::LeanObject,
    mut v_inst_6701_: *mut crate::leanh::LeanObject,
    mut v_inst_6702_: *mut crate::leanh::LeanObject,
    mut v_inst_6703_: *mut crate::leanh::LeanObject,
    mut v_inst_6704_: *mut crate::leanh::LeanObject,
    mut v_inst_6705_: *mut crate::leanh::LeanObject,
    mut v_cls_6706_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6707_: u8,
    mut v_tag_6708_: *mut crate::leanh::LeanObject,
    mut v_opts_6709_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6710_: u8,
    mut v_oldTraces_6711_: *mut crate::leanh::LeanObject,
    mut v_ref_6712_: *mut crate::leanh::LeanObject,
    mut v_toPure_6713_: *mut crate::leanh::LeanObject,
    mut v_toBind_6714_: *mut crate::leanh::LeanObject,
    mut v_k_6715_: *mut crate::leanh::LeanObject,
    mut v_inst_6716_: *mut crate::leanh::LeanObject,
    mut v_msg_6717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: u8 = 0;
    v_tryCatch_6718_ = crate::leanh::lean_ctor_get(v_always_6700_, 1);
    crate::leanh::lean_inc(v_tryCatch_6718_);
    v___x_6719_ = crate::leanh::lean_box((v_collapsed_6707_) as usize);
    v___x_6720_ = crate::leanh::lean_box((v_clsEnabled_6710_) as usize);
    crate::leanh::lean_inc_ref(v_opts_6709_);
    v___f_6721_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__1___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_6721_, 0, v_inst_6701_);
    crate::leanh::lean_closure_set(v___f_6721_, 1, v_inst_6702_);
    crate::leanh::lean_closure_set(v___f_6721_, 2, v_inst_6703_);
    crate::leanh::lean_closure_set(v___f_6721_, 3, v_inst_6704_);
    crate::leanh::lean_closure_set(v___f_6721_, 4, v_always_6700_);
    crate::leanh::lean_closure_set(v___f_6721_, 5, v_inst_6705_);
    crate::leanh::lean_closure_set(v___f_6721_, 6, v_cls_6706_);
    crate::leanh::lean_closure_set(v___f_6721_, 7, v___x_6719_);
    crate::leanh::lean_closure_set(v___f_6721_, 8, v_tag_6708_);
    crate::leanh::lean_closure_set(v___f_6721_, 9, v_opts_6709_);
    crate::leanh::lean_closure_set(v___f_6721_, 10, v___x_6720_);
    crate::leanh::lean_closure_set(v___f_6721_, 11, v_oldTraces_6711_);
    crate::leanh::lean_closure_set(v___f_6721_, 12, v_ref_6712_);
    crate::leanh::lean_closure_set(v___f_6721_, 13, v_msg_6717_);
    crate::leanh::lean_inc_n(v_toPure_6713_, 2);
    v___f_6722_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6722_, 0, v_toPure_6713_);
    v___f_6723_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNode___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6723_, 0, v_toPure_6713_);
    crate::leanh::lean_inc(v_toBind_6714_);
    v___x_6724_ = crate::leanh::lean_apply_4(
        v_toBind_6714_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_k_6715_,
        v___f_6723_,
    );
    v___x_6725_ = crate::leanh::lean_apply_3(
        v_tryCatch_6718_,
        crate::leanh::lean_box(0),
        v___x_6724_,
        v___f_6722_,
    );
    v___x_6726_ = l_Lean_KVMap_instValueBool;
    v___x_6727_ = l_Lean_trace_profiler_useHeartbeats;
    v___x_6728_ = l_Lean_Option_get___redArg(v___x_6726_, v_opts_6709_, v___x_6727_);
    crate::leanh::lean_dec_ref(v_opts_6709_);
    v___x_6729_ = (crate::leanh::lean_unbox(v___x_6728_) as u8);
    crate::leanh::lean_dec(v___x_6728_);
    if v___x_6729_ == 0 {
        let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6730_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0;
        v___x_6731_ =
            crate::leanh::lean_apply_2(v_inst_6716_, crate::leanh::lean_box(0), v___x_6730_);
        crate::leanh::lean_inc(v___x_6731_);
        crate::leanh::lean_inc_n(v_toBind_6714_, 2);
        v___f_6732_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__5 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6732_, 0, v_toPure_6713_);
        crate::leanh::lean_closure_set(v___f_6732_, 1, v_toBind_6714_);
        crate::leanh::lean_closure_set(v___f_6732_, 2, v___x_6731_);
        crate::leanh::lean_closure_set(v___f_6732_, 3, v___x_6725_);
        v___x_6733_ = crate::leanh::lean_apply_4(
            v_toBind_6714_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6731_,
            v___f_6732_,
        );
        v___x_6734_ = crate::leanh::lean_apply_4(
            v_toBind_6714_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6733_,
            v___f_6721_,
        );
        return v___x_6734_;
    } else {
        let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6735_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1;
        v___x_6736_ =
            crate::leanh::lean_apply_2(v_inst_6716_, crate::leanh::lean_box(0), v___x_6735_);
        crate::leanh::lean_inc(v___x_6736_);
        crate::leanh::lean_inc_n(v_toBind_6714_, 2);
        v___f_6737_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNode___redArg___lam__8 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6737_, 0, v_toPure_6713_);
        crate::leanh::lean_closure_set(v___f_6737_, 1, v_toBind_6714_);
        crate::leanh::lean_closure_set(v___f_6737_, 2, v___x_6736_);
        crate::leanh::lean_closure_set(v___f_6737_, 3, v___x_6725_);
        v___x_6738_ = crate::leanh::lean_apply_4(
            v_toBind_6714_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6736_,
            v___f_6737_,
        );
        v___x_6739_ = crate::leanh::lean_apply_4(
            v_toBind_6714_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6738_,
            v___f_6721_,
        );
        return v___x_6739_;
    }
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_always_6740_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_6741_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6742_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6743_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_6744_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6745_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_6746_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_6747_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_6748_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_6749_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_clsEnabled_6750_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_oldTraces_6751_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_ref_6752_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toPure_6753_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_toBind_6754_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_k_6755_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_6756_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_msg_6757_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6758_: u8 = 0;
    let mut v_clsEnabled_boxed_6759_: u8 = 0;
    let mut v_res_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6758_ = (crate::leanh::lean_unbox(v_collapsed_6747_) as u8);
    v_clsEnabled_boxed_6759_ = (crate::leanh::lean_unbox(v_clsEnabled_6750_) as u8);
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
    mut v_always_6761_: *mut crate::leanh::LeanObject,
    mut v_inst_6762_: *mut crate::leanh::LeanObject,
    mut v_inst_6763_: *mut crate::leanh::LeanObject,
    mut v_inst_6764_: *mut crate::leanh::LeanObject,
    mut v_inst_6765_: *mut crate::leanh::LeanObject,
    mut v_inst_6766_: *mut crate::leanh::LeanObject,
    mut v_cls_6767_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6768_: u8,
    mut v_tag_6769_: *mut crate::leanh::LeanObject,
    mut v_opts_6770_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6771_: u8,
    mut v_oldTraces_6772_: *mut crate::leanh::LeanObject,
    mut v_toPure_6773_: *mut crate::leanh::LeanObject,
    mut v_toBind_6774_: *mut crate::leanh::LeanObject,
    mut v_k_6775_: *mut crate::leanh::LeanObject,
    mut v_inst_6776_: *mut crate::leanh::LeanObject,
    mut v_msg_6777_: *mut crate::leanh::LeanObject,
    mut v___f_6778_: *mut crate::leanh::LeanObject,
    mut v_withRef_6779_: *mut crate::leanh::LeanObject,
    mut v_getRef_6780_: *mut crate::leanh::LeanObject,
    mut v_ref_6781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6782_ = crate::leanh::lean_box((v_collapsed_6768_) as usize);
    v___x_6783_ = crate::leanh::lean_box((v_clsEnabled_6771_) as usize);
    crate::leanh::lean_inc_n(v_toBind_6774_, 3);
    crate::leanh::lean_inc(v_ref_6781_);
    v___f_6784_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__10___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_6784_, 0, v_always_6761_);
    crate::leanh::lean_closure_set(v___f_6784_, 1, v_inst_6762_);
    crate::leanh::lean_closure_set(v___f_6784_, 2, v_inst_6763_);
    crate::leanh::lean_closure_set(v___f_6784_, 3, v_inst_6764_);
    crate::leanh::lean_closure_set(v___f_6784_, 4, v_inst_6765_);
    crate::leanh::lean_closure_set(v___f_6784_, 5, v_inst_6766_);
    crate::leanh::lean_closure_set(v___f_6784_, 6, v_cls_6767_);
    crate::leanh::lean_closure_set(v___f_6784_, 7, v___x_6782_);
    crate::leanh::lean_closure_set(v___f_6784_, 8, v_tag_6769_);
    crate::leanh::lean_closure_set(v___f_6784_, 9, v_opts_6770_);
    crate::leanh::lean_closure_set(v___f_6784_, 10, v___x_6783_);
    crate::leanh::lean_closure_set(v___f_6784_, 11, v_oldTraces_6772_);
    crate::leanh::lean_closure_set(v___f_6784_, 12, v_ref_6781_);
    crate::leanh::lean_closure_set(v___f_6784_, 13, v_toPure_6773_);
    crate::leanh::lean_closure_set(v___f_6784_, 14, v_toBind_6774_);
    crate::leanh::lean_closure_set(v___f_6784_, 15, v_k_6775_);
    crate::leanh::lean_closure_set(v___f_6784_, 16, v_inst_6776_);
    v___x_6785_ = crate::leanh::lean_box(0);
    v___x_6786_ = crate::leanh::lean_apply_1(v_msg_6777_, v___x_6785_);
    v___x_6787_ = crate::leanh::lean_apply_4(
        v_toBind_6774_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6786_,
        v___f_6778_,
    );
    v___f_6788_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6788_, 0, v_ref_6781_);
    crate::leanh::lean_closure_set(v___f_6788_, 1, v_withRef_6779_);
    crate::leanh::lean_closure_set(v___f_6788_, 2, v___x_6787_);
    v___x_6789_ = crate::leanh::lean_apply_4(
        v_toBind_6774_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_6780_,
        v___f_6788_,
    );
    v___x_6790_ = crate::leanh::lean_apply_4(
        v_toBind_6774_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6789_,
        v___f_6784_,
    );
    return v___x_6790_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_always_6791_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_6792_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6793_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6794_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_6795_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6796_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_6797_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_6798_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_6799_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_6800_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_clsEnabled_6801_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_oldTraces_6802_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toPure_6803_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toBind_6804_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_k_6805_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_6806_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_msg_6807_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_6808_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_withRef_6809_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_getRef_6810_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_ref_6811_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_collapsed_boxed_6812_: u8 = 0;
    let mut v_clsEnabled_boxed_6813_: u8 = 0;
    let mut v_res_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6812_ = (crate::leanh::lean_unbox(v_collapsed_6798_) as u8);
    v_clsEnabled_boxed_6813_ = (crate::leanh::lean_unbox(v_clsEnabled_6801_) as u8);
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
    mut v_inst_6815_: *mut crate::leanh::LeanObject,
    mut v_always_6816_: *mut crate::leanh::LeanObject,
    mut v_inst_6817_: *mut crate::leanh::LeanObject,
    mut v_inst_6818_: *mut crate::leanh::LeanObject,
    mut v_inst_6819_: *mut crate::leanh::LeanObject,
    mut v_inst_6820_: *mut crate::leanh::LeanObject,
    mut v_cls_6821_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6822_: u8,
    mut v_tag_6823_: *mut crate::leanh::LeanObject,
    mut v_opts_6824_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6825_: u8,
    mut v_toPure_6826_: *mut crate::leanh::LeanObject,
    mut v_toBind_6827_: *mut crate::leanh::LeanObject,
    mut v_k_6828_: *mut crate::leanh::LeanObject,
    mut v_inst_6829_: *mut crate::leanh::LeanObject,
    mut v_msg_6830_: *mut crate::leanh::LeanObject,
    mut v___f_6831_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_6832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_6833_ = crate::leanh::lean_ctor_get(v_inst_6815_, 0);
    crate::leanh::lean_inc_n(v_getRef_6833_, 2);
    v_withRef_6834_ = crate::leanh::lean_ctor_get(v_inst_6815_, 1);
    crate::leanh::lean_inc(v_withRef_6834_);
    v___x_6835_ = crate::leanh::lean_box((v_collapsed_6822_) as usize);
    v___x_6836_ = crate::leanh::lean_box((v_clsEnabled_6825_) as usize);
    crate::leanh::lean_inc(v_toBind_6827_);
    v___f_6837_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__3___boxed as *mut core::ffi::c_void,
        21,
        20,
    );
    crate::leanh::lean_closure_set(v___f_6837_, 0, v_always_6816_);
    crate::leanh::lean_closure_set(v___f_6837_, 1, v_inst_6817_);
    crate::leanh::lean_closure_set(v___f_6837_, 2, v_inst_6818_);
    crate::leanh::lean_closure_set(v___f_6837_, 3, v_inst_6815_);
    crate::leanh::lean_closure_set(v___f_6837_, 4, v_inst_6819_);
    crate::leanh::lean_closure_set(v___f_6837_, 5, v_inst_6820_);
    crate::leanh::lean_closure_set(v___f_6837_, 6, v_cls_6821_);
    crate::leanh::lean_closure_set(v___f_6837_, 7, v___x_6835_);
    crate::leanh::lean_closure_set(v___f_6837_, 8, v_tag_6823_);
    crate::leanh::lean_closure_set(v___f_6837_, 9, v_opts_6824_);
    crate::leanh::lean_closure_set(v___f_6837_, 10, v___x_6836_);
    crate::leanh::lean_closure_set(v___f_6837_, 11, v_oldTraces_6832_);
    crate::leanh::lean_closure_set(v___f_6837_, 12, v_toPure_6826_);
    crate::leanh::lean_closure_set(v___f_6837_, 13, v_toBind_6827_);
    crate::leanh::lean_closure_set(v___f_6837_, 14, v_k_6828_);
    crate::leanh::lean_closure_set(v___f_6837_, 15, v_inst_6829_);
    crate::leanh::lean_closure_set(v___f_6837_, 16, v_msg_6830_);
    crate::leanh::lean_closure_set(v___f_6837_, 17, v___f_6831_);
    crate::leanh::lean_closure_set(v___f_6837_, 18, v_withRef_6834_);
    crate::leanh::lean_closure_set(v___f_6837_, 19, v_getRef_6833_);
    v___x_6838_ = crate::leanh::lean_apply_4(
        v_toBind_6827_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_6833_,
        v___f_6837_,
    );
    return v___x_6838_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_6839_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_always_6840_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6841_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6842_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_6843_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6844_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_6845_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_6846_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_6847_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_6848_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_clsEnabled_6849_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toPure_6850_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_6851_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_k_6852_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_6853_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_msg_6854_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_6855_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_oldTraces_6856_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_6857_: u8 = 0;
    let mut v_clsEnabled_boxed_6858_: u8 = 0;
    let mut v_res_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6857_ = (crate::leanh::lean_unbox(v_collapsed_6846_) as u8);
    v_clsEnabled_boxed_6858_ = (crate::leanh::lean_unbox(v_clsEnabled_6849_) as u8);
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
    mut v_inst_6860_: *mut crate::leanh::LeanObject,
    mut v_always_6861_: *mut crate::leanh::LeanObject,
    mut v_inst_6862_: *mut crate::leanh::LeanObject,
    mut v_inst_6863_: *mut crate::leanh::LeanObject,
    mut v_inst_6864_: *mut crate::leanh::LeanObject,
    mut v_inst_6865_: *mut crate::leanh::LeanObject,
    mut v_cls_6866_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6867_: u8,
    mut v_tag_6868_: *mut crate::leanh::LeanObject,
    mut v_opts_6869_: *mut crate::leanh::LeanObject,
    mut v_toPure_6870_: *mut crate::leanh::LeanObject,
    mut v_toBind_6871_: *mut crate::leanh::LeanObject,
    mut v_k_6872_: *mut crate::leanh::LeanObject,
    mut v_inst_6873_: *mut crate::leanh::LeanObject,
    mut v_msg_6874_: *mut crate::leanh::LeanObject,
    mut v___f_6875_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6876_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6877_ = crate::leanh::lean_box((v_collapsed_6867_) as usize);
                v___x_6878_ = crate::leanh::lean_box((v_clsEnabled_6876_) as usize);
                crate::leanh::lean_inc(v_k_6872_);
                crate::leanh::lean_inc(v_toBind_6871_);
                crate::leanh::lean_inc_ref(v_opts_6869_);
                crate::leanh::lean_inc_ref(v_inst_6863_);
                crate::leanh::lean_inc_ref(v_inst_6862_);
                v___f_6879_ = crate::leanh::lean_alloc_closure(
                    l_Lean_withTraceNodeBefore___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    18,
                    17,
                );
                crate::leanh::lean_closure_set(v___f_6879_, 0, v_inst_6860_);
                crate::leanh::lean_closure_set(v___f_6879_, 1, v_always_6861_);
                crate::leanh::lean_closure_set(v___f_6879_, 2, v_inst_6862_);
                crate::leanh::lean_closure_set(v___f_6879_, 3, v_inst_6863_);
                crate::leanh::lean_closure_set(v___f_6879_, 4, v_inst_6864_);
                crate::leanh::lean_closure_set(v___f_6879_, 5, v_inst_6865_);
                crate::leanh::lean_closure_set(v___f_6879_, 6, v_cls_6866_);
                crate::leanh::lean_closure_set(v___f_6879_, 7, v___x_6877_);
                crate::leanh::lean_closure_set(v___f_6879_, 8, v_tag_6868_);
                crate::leanh::lean_closure_set(v___f_6879_, 9, v_opts_6869_);
                crate::leanh::lean_closure_set(v___f_6879_, 10, v___x_6878_);
                crate::leanh::lean_closure_set(v___f_6879_, 11, v_toPure_6870_);
                crate::leanh::lean_closure_set(v___f_6879_, 12, v_toBind_6871_);
                crate::leanh::lean_closure_set(v___f_6879_, 13, v_k_6872_);
                crate::leanh::lean_closure_set(v___f_6879_, 14, v_inst_6873_);
                crate::leanh::lean_closure_set(v___f_6879_, 15, v_msg_6874_);
                crate::leanh::lean_closure_set(v___f_6879_, 16, v___f_6875_);
                if v_clsEnabled_6876_ == 0 {
                    v___x_6883_ = l_Lean_KVMap_instValueBool;
                    v___x_6884_ = l_Lean_trace_profiler;
                    v___x_6885_ =
                        l_Lean_Option_get___redArg(v___x_6883_, v_opts_6869_, v___x_6884_);
                    crate::leanh::lean_dec_ref(v_opts_6869_);
                    v___x_6886_ = (crate::leanh::lean_unbox(v___x_6885_) as u8);
                    crate::leanh::lean_dec(v___x_6885_);
                    if v___x_6886_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_6879_);
                        crate::leanh::lean_dec(v_toBind_6871_);
                        crate::leanh::lean_dec_ref(v_inst_6863_);
                        crate::leanh::lean_dec_ref(v_inst_6862_);
                        return v_k_6872_;
                    } else {
                        crate::leanh::lean_dec(v_k_6872_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6872_);
                    crate::leanh::lean_dec_ref(v_opts_6869_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6881_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                    v_inst_6862_,
                    v_inst_6863_,
                );
                v___x_6882_ = crate::leanh::lean_apply_4(
                    v_toBind_6871_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_6887_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_always_6888_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6889_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6890_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_6891_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6892_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_cls_6893_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_collapsed_6894_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tag_6895_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_opts_6896_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toPure_6897_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_6898_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_k_6899_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_6900_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_msg_6901_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___f_6902_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_clsEnabled_6903_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_6904_: u8 = 0;
    let mut v_clsEnabled_boxed_6905_: u8 = 0;
    let mut v_res_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6904_ = (crate::leanh::lean_unbox(v_collapsed_6894_) as u8);
    v_clsEnabled_boxed_6905_ = (crate::leanh::lean_unbox(v_clsEnabled_6903_) as u8);
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
    mut v_k_6907_: *mut crate::leanh::LeanObject,
    mut v_inst_6908_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_6909_: *mut crate::leanh::LeanObject,
    mut v_inst_6910_: *mut crate::leanh::LeanObject,
    mut v_always_6911_: *mut crate::leanh::LeanObject,
    mut v_inst_6912_: *mut crate::leanh::LeanObject,
    mut v_inst_6913_: *mut crate::leanh::LeanObject,
    mut v_inst_6914_: *mut crate::leanh::LeanObject,
    mut v_cls_6915_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6916_: u8,
    mut v_tag_6917_: *mut crate::leanh::LeanObject,
    mut v_toBind_6918_: *mut crate::leanh::LeanObject,
    mut v_inst_6919_: *mut crate::leanh::LeanObject,
    mut v_msg_6920_: *mut crate::leanh::LeanObject,
    mut v___f_6921_: *mut crate::leanh::LeanObject,
    mut v_inst_6922_: *mut crate::leanh::LeanObject,
    mut v_opts_6923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasTrace_6924_: u8 = 0;
    v_hasTrace_6924_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_6923_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_6924_ == 0 {
        crate::leanh::lean_dec_ref(v_opts_6923_);
        crate::leanh::lean_dec(v_inst_6922_);
        crate::leanh::lean_dec(v___f_6921_);
        crate::leanh::lean_dec(v_msg_6920_);
        crate::leanh::lean_dec(v_inst_6919_);
        crate::leanh::lean_dec(v_toBind_6918_);
        crate::leanh::lean_dec_ref(v_tag_6917_);
        crate::leanh::lean_dec(v_cls_6915_);
        crate::leanh::lean_dec_ref(v_inst_6914_);
        crate::leanh::lean_dec(v_inst_6913_);
        crate::leanh::lean_dec_ref(v_inst_6912_);
        crate::leanh::lean_dec_ref(v_always_6911_);
        crate::leanh::lean_dec_ref(v_inst_6910_);
        crate::leanh::lean_dec_ref(v_toApplicative_6909_);
        crate::leanh::lean_dec_ref(v_inst_6908_);
        return v_k_6907_;
    } else {
        let mut v_getInheritedTraceOptions_6925_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v_toPure_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_6925_ = crate::leanh::lean_ctor_get(v_inst_6908_, 2);
        crate::leanh::lean_inc(v_getInheritedTraceOptions_6925_);
        v_toPure_6926_ = crate::leanh::lean_ctor_get(v_toApplicative_6909_, 1);
        crate::leanh::lean_inc_n(v_toPure_6926_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_6909_);
        v___x_6927_ = crate::leanh::lean_box((v_collapsed_6916_) as usize);
        crate::leanh::lean_inc_n(v_toBind_6918_, 3);
        crate::leanh::lean_inc(v_cls_6915_);
        v___f_6928_ = crate::leanh::lean_alloc_closure(
            l_Lean_withTraceNodeBefore___redArg___lam__4___boxed as *mut core::ffi::c_void,
            17,
            16,
        );
        crate::leanh::lean_closure_set(v___f_6928_, 0, v_inst_6910_);
        crate::leanh::lean_closure_set(v___f_6928_, 1, v_always_6911_);
        crate::leanh::lean_closure_set(v___f_6928_, 2, v_inst_6912_);
        crate::leanh::lean_closure_set(v___f_6928_, 3, v_inst_6908_);
        crate::leanh::lean_closure_set(v___f_6928_, 4, v_inst_6913_);
        crate::leanh::lean_closure_set(v___f_6928_, 5, v_inst_6914_);
        crate::leanh::lean_closure_set(v___f_6928_, 6, v_cls_6915_);
        crate::leanh::lean_closure_set(v___f_6928_, 7, v___x_6927_);
        crate::leanh::lean_closure_set(v___f_6928_, 8, v_tag_6917_);
        crate::leanh::lean_closure_set(v___f_6928_, 9, v_opts_6923_);
        crate::leanh::lean_closure_set(v___f_6928_, 10, v_toPure_6926_);
        crate::leanh::lean_closure_set(v___f_6928_, 11, v_toBind_6918_);
        crate::leanh::lean_closure_set(v___f_6928_, 12, v_k_6907_);
        crate::leanh::lean_closure_set(v___f_6928_, 13, v_inst_6919_);
        crate::leanh::lean_closure_set(v___f_6928_, 14, v_msg_6920_);
        crate::leanh::lean_closure_set(v___f_6928_, 15, v___f_6921_);
        v___f_6929_ = crate::leanh::lean_alloc_closure(
            l_Lean_isTracingEnabledFor___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6929_, 0, v_toPure_6926_);
        crate::leanh::lean_closure_set(v___f_6929_, 1, v_cls_6915_);
        crate::leanh::lean_closure_set(v___f_6929_, 2, v_toBind_6918_);
        crate::leanh::lean_closure_set(v___f_6929_, 3, v_inst_6922_);
        v___x_6930_ = crate::leanh::lean_apply_4(
            v_toBind_6918_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getInheritedTraceOptions_6925_,
            v___f_6929_,
        );
        v___x_6931_ = crate::leanh::lean_apply_4(
            v_toBind_6918_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6930_,
            v___f_6928_,
        );
        return v___x_6931_;
    }
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6932_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_6933_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_toApplicative_6934_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_6935_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_always_6936_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_6937_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_6938_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_6939_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_cls_6940_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_collapsed_6941_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_tag_6942_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_6943_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_6944_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_msg_6945_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_6946_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_6947_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_opts_6948_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_collapsed_boxed_6949_: u8 = 0;
    let mut v_res_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6949_ = (crate::leanh::lean_unbox(v_collapsed_6941_) as u8);
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
    mut v_inst_6951_: *mut crate::leanh::LeanObject,
    mut v_inst_6952_: *mut crate::leanh::LeanObject,
    mut v_inst_6953_: *mut crate::leanh::LeanObject,
    mut v_inst_6954_: *mut crate::leanh::LeanObject,
    mut v_inst_6955_: *mut crate::leanh::LeanObject,
    mut v_always_6956_: *mut crate::leanh::LeanObject,
    mut v_inst_6957_: *mut crate::leanh::LeanObject,
    mut v_inst_6958_: *mut crate::leanh::LeanObject,
    mut v_cls_6959_: *mut crate::leanh::LeanObject,
    mut v_msg_6960_: *mut crate::leanh::LeanObject,
    mut v_k_6961_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6962_: u8,
    mut v_tag_6963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6964_ = crate::leanh::lean_ctor_get(v_inst_6951_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6964_);
    v_toBind_6965_ = crate::leanh::lean_ctor_get(v_inst_6951_, 1);
    crate::leanh::lean_inc_n(v_toBind_6965_, 2);
    crate::leanh::lean_inc(v_inst_6954_);
    v___f_6966_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6966_, 0, v_inst_6954_);
    v___x_6967_ = crate::leanh::lean_box((v_collapsed_6962_) as usize);
    crate::leanh::lean_inc(v_inst_6955_);
    v___f_6968_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_6968_, 0, v_k_6961_);
    crate::leanh::lean_closure_set(v___f_6968_, 1, v_inst_6952_);
    crate::leanh::lean_closure_set(v___f_6968_, 2, v_toApplicative_6964_);
    crate::leanh::lean_closure_set(v___f_6968_, 3, v_inst_6953_);
    crate::leanh::lean_closure_set(v___f_6968_, 4, v_always_6956_);
    crate::leanh::lean_closure_set(v___f_6968_, 5, v_inst_6951_);
    crate::leanh::lean_closure_set(v___f_6968_, 6, v_inst_6954_);
    crate::leanh::lean_closure_set(v___f_6968_, 7, v_inst_6958_);
    crate::leanh::lean_closure_set(v___f_6968_, 8, v_cls_6959_);
    crate::leanh::lean_closure_set(v___f_6968_, 9, v___x_6967_);
    crate::leanh::lean_closure_set(v___f_6968_, 10, v_tag_6963_);
    crate::leanh::lean_closure_set(v___f_6968_, 11, v_toBind_6965_);
    crate::leanh::lean_closure_set(v___f_6968_, 12, v_inst_6957_);
    crate::leanh::lean_closure_set(v___f_6968_, 13, v_msg_6960_);
    crate::leanh::lean_closure_set(v___f_6968_, 14, v___f_6966_);
    crate::leanh::lean_closure_set(v___f_6968_, 15, v_inst_6955_);
    v___x_6969_ = crate::leanh::lean_apply_4(
        v_toBind_6965_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6955_,
        v___f_6968_,
    );
    return v___x_6969_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___redArg___boxed(
    mut v_inst_6970_: *mut crate::leanh::LeanObject,
    mut v_inst_6971_: *mut crate::leanh::LeanObject,
    mut v_inst_6972_: *mut crate::leanh::LeanObject,
    mut v_inst_6973_: *mut crate::leanh::LeanObject,
    mut v_inst_6974_: *mut crate::leanh::LeanObject,
    mut v_always_6975_: *mut crate::leanh::LeanObject,
    mut v_inst_6976_: *mut crate::leanh::LeanObject,
    mut v_inst_6977_: *mut crate::leanh::LeanObject,
    mut v_cls_6978_: *mut crate::leanh::LeanObject,
    mut v_msg_6979_: *mut crate::leanh::LeanObject,
    mut v_k_6980_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6981_: *mut crate::leanh::LeanObject,
    mut v_tag_6982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_6983_: u8 = 0;
    let mut v_res_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6983_ = (crate::leanh::lean_unbox(v_collapsed_6981_) as u8);
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
    mut v_00_u03b1_6985_: *mut crate::leanh::LeanObject,
    mut v_m_6986_: *mut crate::leanh::LeanObject,
    mut v_inst_6987_: *mut crate::leanh::LeanObject,
    mut v_inst_6988_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_6989_: *mut crate::leanh::LeanObject,
    mut v_inst_6990_: *mut crate::leanh::LeanObject,
    mut v_inst_6991_: *mut crate::leanh::LeanObject,
    mut v_inst_6992_: *mut crate::leanh::LeanObject,
    mut v_always_6993_: *mut crate::leanh::LeanObject,
    mut v_inst_6994_: *mut crate::leanh::LeanObject,
    mut v_inst_6995_: *mut crate::leanh::LeanObject,
    mut v_cls_6996_: *mut crate::leanh::LeanObject,
    mut v_msg_6997_: *mut crate::leanh::LeanObject,
    mut v_k_6998_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6999_: u8,
    mut v_tag_7000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7001_ = crate::leanh::lean_ctor_get(v_inst_6987_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7001_);
    v_toBind_7002_ = crate::leanh::lean_ctor_get(v_inst_6987_, 1);
    crate::leanh::lean_inc_n(v_toBind_7002_, 2);
    crate::leanh::lean_inc(v_inst_6991_);
    v___f_7003_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7003_, 0, v_inst_6991_);
    v___x_7004_ = crate::leanh::lean_box((v_collapsed_6999_) as usize);
    crate::leanh::lean_inc(v_inst_6992_);
    v___f_7005_ = crate::leanh::lean_alloc_closure(
        l_Lean_withTraceNodeBefore___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_7005_, 0, v_k_6998_);
    crate::leanh::lean_closure_set(v___f_7005_, 1, v_inst_6988_);
    crate::leanh::lean_closure_set(v___f_7005_, 2, v_toApplicative_7001_);
    crate::leanh::lean_closure_set(v___f_7005_, 3, v_inst_6990_);
    crate::leanh::lean_closure_set(v___f_7005_, 4, v_always_6993_);
    crate::leanh::lean_closure_set(v___f_7005_, 5, v_inst_6987_);
    crate::leanh::lean_closure_set(v___f_7005_, 6, v_inst_6991_);
    crate::leanh::lean_closure_set(v___f_7005_, 7, v_inst_6995_);
    crate::leanh::lean_closure_set(v___f_7005_, 8, v_cls_6996_);
    crate::leanh::lean_closure_set(v___f_7005_, 9, v___x_7004_);
    crate::leanh::lean_closure_set(v___f_7005_, 10, v_tag_7000_);
    crate::leanh::lean_closure_set(v___f_7005_, 11, v_toBind_7002_);
    crate::leanh::lean_closure_set(v___f_7005_, 12, v_inst_6994_);
    crate::leanh::lean_closure_set(v___f_7005_, 13, v_msg_6997_);
    crate::leanh::lean_closure_set(v___f_7005_, 14, v___f_7003_);
    crate::leanh::lean_closure_set(v___f_7005_, 15, v_inst_6992_);
    v___x_7006_ = crate::leanh::lean_apply_4(
        v_toBind_7002_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6992_,
        v___f_7005_,
    );
    return v___x_7006_;
}
pub unsafe fn l_Lean_withTraceNodeBefore___boxed(
    mut v_00_u03b1_7007_: *mut crate::leanh::LeanObject,
    mut v_m_7008_: *mut crate::leanh::LeanObject,
    mut v_inst_7009_: *mut crate::leanh::LeanObject,
    mut v_inst_7010_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_7011_: *mut crate::leanh::LeanObject,
    mut v_inst_7012_: *mut crate::leanh::LeanObject,
    mut v_inst_7013_: *mut crate::leanh::LeanObject,
    mut v_inst_7014_: *mut crate::leanh::LeanObject,
    mut v_always_7015_: *mut crate::leanh::LeanObject,
    mut v_inst_7016_: *mut crate::leanh::LeanObject,
    mut v_inst_7017_: *mut crate::leanh::LeanObject,
    mut v_cls_7018_: *mut crate::leanh::LeanObject,
    mut v_msg_7019_: *mut crate::leanh::LeanObject,
    mut v_k_7020_: *mut crate::leanh::LeanObject,
    mut v_collapsed_7021_: *mut crate::leanh::LeanObject,
    mut v_tag_7022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_7023_: u8 = 0;
    let mut v_res_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_7023_ = (crate::leanh::lean_unbox(v_collapsed_7021_) as u8);
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
    mut v_toApplicative_7025_: *mut crate::leanh::LeanObject,
    mut v_____s_7026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_7027_ = crate::leanh::lean_ctor_get(v_toApplicative_7025_, 1);
    crate::leanh::lean_inc(v_toPure_7027_);
    crate::leanh::lean_dec_ref(v_toApplicative_7025_);
    v___x_7028_ = crate::leanh::lean_box(0);
    v___x_7029_ =
        crate::leanh::lean_apply_2(v_toPure_7027_, crate::leanh::lean_box(0), v___x_7028_);
    return v___x_7029_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__1(
    mut v_x_7030_: *mut crate::leanh::LeanObject,
    mut v_x_7031_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: u8 = 0;
    v_fst_7032_ = crate::leanh::lean_ctor_get(v_x_7030_, 0);
    v_fst_7033_ = crate::leanh::lean_ctor_get(v_x_7031_, 0);
    v_fst_7034_ = crate::leanh::lean_ctor_get(v_fst_7032_, 0);
    v_fst_7035_ = crate::leanh::lean_ctor_get(v_fst_7033_, 0);
    v___x_7036_ = lean_nat_dec_lt(v_fst_7034_, v_fst_7035_);
    return v___x_7036_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__1___boxed(
    mut v_x_7037_: *mut crate::leanh::LeanObject,
    mut v_x_7038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7039_: u8 = 0;
    let mut v_r_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7039_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_7037_, v_x_7038_);
    crate::leanh::lean_dec_ref(v_x_7038_);
    crate::leanh::lean_dec_ref(v_x_7037_);
    v_r_7040_ = crate::leanh::lean_box((v_res_7039_) as usize);
    return v_r_7040_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__2(
    mut v_x1_7041_: *mut crate::leanh::LeanObject,
    mut v_x2_7042_: *mut crate::leanh::LeanObject,
    mut v_x3_7043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7044_, 0, v_x2_7042_);
    crate::leanh::lean_ctor_set(v___x_7044_, 1, v_x3_7043_);
    v___x_7045_ = lean_array_push(v_x1_7041_, v___x_7044_);
    return v___x_7045_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__3(
    mut v_toApplicative_7046_: *mut crate::leanh::LeanObject,
    mut v___x_7047_: *mut crate::leanh::LeanObject,
    mut v_r_7048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_7049_ = crate::leanh::lean_ctor_get(v_toApplicative_7046_, 1);
    crate::leanh::lean_inc(v_toPure_7049_);
    crate::leanh::lean_dec_ref(v_toApplicative_7046_);
    v___x_7050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7050_, 0, v___x_7047_);
    v___x_7051_ =
        crate::leanh::lean_apply_2(v_toPure_7049_, crate::leanh::lean_box(0), v___x_7050_);
    return v___x_7051_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__4(
    mut v_____do__lift_7052_: *mut crate::leanh::LeanObject,
    mut v___x_7053_: *mut crate::leanh::LeanObject,
    mut v_fst_7054_: *mut crate::leanh::LeanObject,
    mut v_snd_7055_: *mut crate::leanh::LeanObject,
    mut v_logMessage_7056_: *mut crate::leanh::LeanObject,
    mut v_toBind_7057_: *mut crate::leanh::LeanObject,
    mut v___f_7058_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7060_ = 0;
    v___x_7061_ = l_Lean_Elab_mkMessageCore(
        v_____do__lift_7052_,
        v_____do__lift_7059_,
        v___x_7053_,
        v___x_7060_,
        v_fst_7054_,
        v_snd_7055_,
    );
    v___x_7062_ = crate::leanh::lean_apply_1(v_logMessage_7056_, v___x_7061_);
    v___x_7063_ = crate::leanh::lean_apply_4(
        v_toBind_7057_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7062_,
        v___f_7058_,
    );
    return v___x_7063_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__4___boxed(
    mut v_____do__lift_7064_: *mut crate::leanh::LeanObject,
    mut v___x_7065_: *mut crate::leanh::LeanObject,
    mut v_fst_7066_: *mut crate::leanh::LeanObject,
    mut v_snd_7067_: *mut crate::leanh::LeanObject,
    mut v_logMessage_7068_: *mut crate::leanh::LeanObject,
    mut v_toBind_7069_: *mut crate::leanh::LeanObject,
    mut v___f_7070_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_snd_7067_);
    crate::leanh::lean_dec(v_fst_7066_);
    return v_res_7072_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__5(
    mut v___x_7073_: *mut crate::leanh::LeanObject,
    mut v_fst_7074_: *mut crate::leanh::LeanObject,
    mut v_snd_7075_: *mut crate::leanh::LeanObject,
    mut v_logMessage_7076_: *mut crate::leanh::LeanObject,
    mut v_toBind_7077_: *mut crate::leanh::LeanObject,
    mut v___f_7078_: *mut crate::leanh::LeanObject,
    mut v_toMonadFileMap_7079_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_7077_);
    v___f_7081_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_7081_, 0, v_____do__lift_7080_);
    crate::leanh::lean_closure_set(v___f_7081_, 1, v___x_7073_);
    crate::leanh::lean_closure_set(v___f_7081_, 2, v_fst_7074_);
    crate::leanh::lean_closure_set(v___f_7081_, 3, v_snd_7075_);
    crate::leanh::lean_closure_set(v___f_7081_, 4, v_logMessage_7076_);
    crate::leanh::lean_closure_set(v___f_7081_, 5, v_toBind_7077_);
    crate::leanh::lean_closure_set(v___f_7081_, 6, v___f_7078_);
    v___x_7082_ = crate::leanh::lean_apply_4(
        v_toBind_7077_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_toMonadFileMap_7079_,
        v___f_7081_,
    );
    return v___x_7082_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__6(
    mut v___x_7083_: *mut crate::leanh::LeanObject,
    mut v___x_7084_: u8,
    mut v_inst_7085_: *mut crate::leanh::LeanObject,
    mut v_toBind_7086_: *mut crate::leanh::LeanObject,
    mut v___f_7087_: *mut crate::leanh::LeanObject,
    mut v_a_7088_: *mut crate::leanh::LeanObject,
    mut v_x_7089_: *mut crate::leanh::LeanObject,
    mut v___y_7090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7097_: u8 = 0;
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: f64 = 0.0;
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7091_ = crate::leanh::lean_ctor_get(v_a_7088_, 0);
                crate::leanh::lean_inc(v_fst_7091_);
                v_snd_7092_ = crate::leanh::lean_ctor_get(v_a_7088_, 1);
                crate::leanh::lean_inc(v_snd_7092_);
                crate::leanh::lean_dec_ref(v_a_7088_);
                v_fst_7093_ = crate::leanh::lean_ctor_get(v_fst_7091_, 0);
                v_snd_7094_ = crate::leanh::lean_ctor_get(v_fst_7091_, 1);
                v_isSharedCheck_7114_ = (!crate::leanh::lean_is_exclusive(v_fst_7091_)) as u8;
                if v_isSharedCheck_7114_ == 0 {
                    v___x_7096_ = v_fst_7091_;
                    v_isShared_7097_ = v_isSharedCheck_7114_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7094_);
                    crate::leanh::lean_inc(v_fst_7093_);
                    crate::leanh::lean_dec(v_fst_7091_);
                    v___x_7096_ = crate::leanh::lean_box(0);
                    v_isShared_7097_ = v_isSharedCheck_7114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7098_ = crate::leanh::lean_box(0);
                v___x_7099_ = crate::leanh::lean_box(0);
                v___x_7100_ = lean_float_of_nat(v___x_7083_);
                v___x_7101_ = l_Lean_addTrace___redArg___lam__0___closed__1;
                v___x_7102_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_7102_, 0, v___x_7098_);
                crate::leanh::lean_ctor_set(v___x_7102_, 1, v___x_7099_);
                crate::leanh::lean_ctor_set(v___x_7102_, 2, v___x_7101_);
                crate::leanh::lean_ctor_set_float(
                    v___x_7102_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_7100_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_7102_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_7100_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7102_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_7084_,
                );
                v_toMonadFileMap_7103_ = crate::leanh::lean_ctor_get(v_inst_7085_, 0);
                crate::leanh::lean_inc(v_toMonadFileMap_7103_);
                v_getFileName_7104_ = crate::leanh::lean_ctor_get(v_inst_7085_, 2);
                crate::leanh::lean_inc(v_getFileName_7104_);
                v_logMessage_7105_ = crate::leanh::lean_ctor_get(v_inst_7085_, 4);
                crate::leanh::lean_inc(v_logMessage_7105_);
                crate::leanh::lean_dec_ref(v_inst_7085_);
                v___x_7106_ = l_Lean_checkTraceOption___closed__1;
                v___x_7107_ = l_Lean_MessageData_nil;
                v___x_7108_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7108_, 0, v___x_7102_);
                crate::leanh::lean_ctor_set(v___x_7108_, 1, v___x_7107_);
                crate::leanh::lean_ctor_set(v___x_7108_, 2, v_snd_7092_);
                if v_isShared_7097_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7096_, 8);
                    crate::leanh::lean_ctor_set(v___x_7096_, 1, v___x_7108_);
                    crate::leanh::lean_ctor_set(v___x_7096_, 0, v___x_7106_);
                    v___x_7110_ = v___x_7096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7113_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7113_, 0, v___x_7106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7113_, 1, v___x_7108_);
                    v___x_7110_ = v_reuseFailAlloc_7113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_toBind_7086_);
                v___f_7111_ = crate::leanh::lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__5 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_7111_, 0, v___x_7110_);
                crate::leanh::lean_closure_set(v___f_7111_, 1, v_fst_7093_);
                crate::leanh::lean_closure_set(v___f_7111_, 2, v_snd_7094_);
                crate::leanh::lean_closure_set(v___f_7111_, 3, v_logMessage_7105_);
                crate::leanh::lean_closure_set(v___f_7111_, 4, v_toBind_7086_);
                crate::leanh::lean_closure_set(v___f_7111_, 5, v___f_7087_);
                crate::leanh::lean_closure_set(v___f_7111_, 6, v_toMonadFileMap_7103_);
                v___x_7112_ = crate::leanh::lean_apply_4(
                    v_toBind_7086_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___x_7115_: *mut crate::leanh::LeanObject,
    mut v___x_7116_: *mut crate::leanh::LeanObject,
    mut v_inst_7117_: *mut crate::leanh::LeanObject,
    mut v_toBind_7118_: *mut crate::leanh::LeanObject,
    mut v___f_7119_: *mut crate::leanh::LeanObject,
    mut v_a_7120_: *mut crate::leanh::LeanObject,
    mut v_x_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730__boxed_7123_: u8 = 0;
    let mut v_res_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730__boxed_7123_ = (crate::leanh::lean_unbox(v___x_7116_) as u8);
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
    mut v___x_7125_: *mut crate::leanh::LeanObject,
    mut v___f_7126_: *mut crate::leanh::LeanObject,
    mut v_acc_7127_: *mut crate::leanh::LeanObject,
    mut v_l_7128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7129_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_7125_,
        v___f_7126_,
        v_acc_7127_,
        v_l_7128_,
    );
    return v___x_7129_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__8(
    mut v_toApplicative_7130_: *mut crate::leanh::LeanObject,
    mut v___x_7131_: u8,
    mut v_inst_7132_: *mut crate::leanh::LeanObject,
    mut v_toBind_7133_: *mut crate::leanh::LeanObject,
    mut v_inst_7134_: *mut crate::leanh::LeanObject,
    mut v___f_7135_: *mut crate::leanh::LeanObject,
    mut v___f_7136_: *mut crate::leanh::LeanObject,
    mut v___f_7137_: *mut crate::leanh::LeanObject,
    mut v_____s_7138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7146_: usize = 0;
    let mut v___x_7147_: usize = 0;
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: u8 = 0;
    let mut v___y_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: u8 = 0;
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    let mut v_size_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: u8 = 0;
    let mut v___f_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: u8 = 0;
    let mut v___x_7181_: usize = 0;
    let mut v___x_7182_: usize = 0;
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: usize = 0;
    let mut v___x_7185_: usize = 0;
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7172_ = crate::leanh::lean_ctor_get(v_____s_7138_, 0);
                crate::leanh::lean_inc(v_size_7172_);
                v_buckets_7173_ = crate::leanh::lean_ctor_get(v_____s_7138_, 1);
                crate::leanh::lean_inc_ref(v_buckets_7173_);
                crate::leanh::lean_dec_ref(v_____s_7138_);
                v___x_7174_ = lean_mk_empty_array_with_capacity(v_size_7172_);
                crate::leanh::lean_dec(v_size_7172_);
                v___x_7175_ =
                    l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9;
                v___x_7176_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7177_ = lean_array_get_size(v_buckets_7173_);
                v___x_7178_ = lean_nat_dec_lt(v___x_7176_, v___x_7177_);
                if v___x_7178_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_7173_);
                    crate::leanh::lean_dec_ref(v___f_7137_);
                    v___y_7165_ = v___x_7174_;
                    state = 4;
                    continue;
                } else {
                    v___f_7179_ = crate::leanh::lean_alloc_closure(
                        l_Lean_addTraceAsMessages___redArg___lam__7 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_7179_, 0, v___x_7175_);
                    crate::leanh::lean_closure_set(v___f_7179_, 1, v___f_7137_);
                    v___x_7180_ = lean_nat_dec_le(v___x_7177_, v___x_7177_);
                    if v___x_7180_ == 0 {
                        if v___x_7178_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_7179_);
                            crate::leanh::lean_dec_ref(v_buckets_7173_);
                            v___y_7165_ = v___x_7174_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7181_ = 0usize;
                            v___x_7182_ = lean_usize_of_nat(v___x_7177_);
                            v___x_7183_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
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
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
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
                v___x_7142_ = crate::leanh::lean_box(0);
                v___f_7143_ = crate::leanh::lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__3 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7143_, 0, v_toApplicative_7130_);
                crate::leanh::lean_closure_set(v___f_7143_, 1, v___x_7142_);
                v___x_7144_ = crate::leanh::lean_box((v___x_7131_) as usize);
                crate::leanh::lean_inc(v_toBind_7133_);
                v___f_7145_ = crate::leanh::lean_alloc_closure(
                    l_Lean_addTraceAsMessages___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    8,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_7145_, 0, v___y_7140_);
                crate::leanh::lean_closure_set(v___f_7145_, 1, v___x_7144_);
                crate::leanh::lean_closure_set(v___f_7145_, 2, v_inst_7132_);
                crate::leanh::lean_closure_set(v___f_7145_, 3, v_toBind_7133_);
                crate::leanh::lean_closure_set(v___f_7145_, 4, v___f_7143_);
                v_sz_7146_ = lean_array_size(v___y_7141_);
                v___x_7147_ = 0usize;
                v___x_7148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_7134_,
                    v___y_7141_,
                    v___f_7145_,
                    v_sz_7146_,
                    v___x_7147_,
                    v___x_7142_,
                );
                v___x_7149_ = crate::leanh::lean_apply_4(
                    v_toBind_7133_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7148_,
                    v___f_7135_,
                );
                return v___x_7149_;
            }
            2 => {
                v___x_7156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_7136_,
                    v___y_7154_,
                    v___y_7152_,
                    v___y_7153_,
                    v___y_7155_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_7155_);
                crate::leanh::lean_dec(v___y_7154_);
                v___y_7140_ = v___y_7151_;
                v___y_7141_ = v___x_7156_;
                state = 1;
                continue;
            }
            3 => {
                v___x_7163_ = lean_nat_dec_le(v___y_7162_, v___y_7160_);
                if v___x_7163_ == 0 {
                    crate::leanh::lean_dec(v___y_7160_);
                    crate::leanh::lean_inc(v___y_7162_);
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
                v___x_7166_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7167_ = lean_array_get_size(v___y_7165_);
                v___x_7168_ = lean_nat_dec_eq(v___x_7167_, v___x_7166_);
                if v___x_7168_ == 0 {
                    v___x_7169_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7170_ = lean_nat_sub(v___x_7167_, v___x_7169_);
                    v___x_7171_ = lean_nat_dec_le(v___x_7166_, v___x_7170_);
                    if v___x_7171_ == 0 {
                        crate::leanh::lean_inc(v___x_7170_);
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
                    crate::leanh::lean_dec_ref(v___f_7136_);
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
    mut v_toApplicative_7187_: *mut crate::leanh::LeanObject,
    mut v___x_7188_: *mut crate::leanh::LeanObject,
    mut v_inst_7189_: *mut crate::leanh::LeanObject,
    mut v_toBind_7190_: *mut crate::leanh::LeanObject,
    mut v_inst_7191_: *mut crate::leanh::LeanObject,
    mut v___f_7192_: *mut crate::leanh::LeanObject,
    mut v___f_7193_: *mut crate::leanh::LeanObject,
    mut v___f_7194_: *mut crate::leanh::LeanObject,
    mut v_____s_7195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1818__boxed_7196_: u8 = 0;
    let mut v_res_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818__boxed_7196_ = (crate::leanh::lean_unbox(v___x_7188_) as u8);
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
    mut v_traceElem_7198_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7199_: *mut crate::leanh::LeanObject,
    mut v___f_7200_: *mut crate::leanh::LeanObject,
    mut v___f_7201_: *mut crate::leanh::LeanObject,
    mut v_____s_7202_: *mut crate::leanh::LeanObject,
    mut v___x_7203_: u8,
    mut v_____do__lift_7204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7209_: u8 = 0;
    let mut v___y_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7205_ = crate::leanh::lean_ctor_get(v_traceElem_7198_, 0);
                v_msg_7206_ = crate::leanh::lean_ctor_get(v_traceElem_7198_, 1);
                v_isSharedCheck_7231_ = (!crate::leanh::lean_is_exclusive(v_traceElem_7198_)) as u8;
                if v_isSharedCheck_7231_ == 0 {
                    v___x_7208_ = v_traceElem_7198_;
                    v_isShared_7209_ = v_isSharedCheck_7231_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_msg_7206_);
                    crate::leanh::lean_inc(v_ref_7205_);
                    crate::leanh::lean_dec(v_traceElem_7198_);
                    v___x_7208_ = crate::leanh::lean_box(0);
                    v_isShared_7209_ = v_isSharedCheck_7231_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_7223_ = l_Lean_replaceRef(v_ref_7205_, v_____do__lift_7204_);
                crate::leanh::lean_dec(v_ref_7205_);
                v___x_7228_ = l_Lean_Syntax_getPos_x3f(v_ref_7223_, v___x_7203_);
                if crate::leanh::lean_obj_tag(v___x_7228_) == 0 {
                    v___x_7229_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7225_ = v___x_7229_;
                    state = 4;
                    continue;
                } else {
                    v_val_7230_ = crate::leanh::lean_ctor_get(v___x_7228_, 0);
                    crate::leanh::lean_inc(v_val_7230_);
                    crate::leanh::lean_dec_ref_known(v___x_7228_, 1);
                    v___y_7225_ = v_val_7230_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v_toPure_7213_ = crate::leanh::lean_ctor_get(v_toApplicative_7199_, 1);
                crate::leanh::lean_inc(v_toPure_7213_);
                crate::leanh::lean_dec_ref(v_toApplicative_7199_);
                if v_isShared_7209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7208_, 1, v___y_7212_);
                    crate::leanh::lean_ctor_set(v___x_7208_, 0, v___y_7211_);
                    v___x_7215_ = v___x_7208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 0, v___y_7211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 1, v___y_7212_);
                    v___x_7215_ = v_reuseFailAlloc_7222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7216_ = l_Lean_addTrace___redArg___lam__0___closed__2;
                crate::leanh::lean_inc_ref(v___x_7215_);
                crate::leanh::lean_inc_ref(v___f_7201_);
                crate::leanh::lean_inc_ref(v___f_7200_);
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
                v___x_7220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7220_, 0, v_pos2traces_7219_);
                v___x_7221_ = crate::leanh::lean_apply_2(
                    v_toPure_7213_,
                    crate::leanh::lean_box(0),
                    v___x_7220_,
                );
                return v___x_7221_;
            }
            4 => {
                v___x_7226_ = l_Lean_Syntax_getTailPos_x3f(v_ref_7223_, v___x_7203_);
                crate::leanh::lean_dec(v_ref_7223_);
                if crate::leanh::lean_obj_tag(v___x_7226_) == 0 {
                    crate::leanh::lean_inc(v___y_7225_);
                    v___y_7211_ = v___y_7225_;
                    v___y_7212_ = v___y_7225_;
                    state = 2;
                    continue;
                } else {
                    v_val_7227_ = crate::leanh::lean_ctor_get(v___x_7226_, 0);
                    crate::leanh::lean_inc(v_val_7227_);
                    crate::leanh::lean_dec_ref_known(v___x_7226_, 1);
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
    mut v_traceElem_7232_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7233_: *mut crate::leanh::LeanObject,
    mut v___f_7234_: *mut crate::leanh::LeanObject,
    mut v___f_7235_: *mut crate::leanh::LeanObject,
    mut v_____s_7236_: *mut crate::leanh::LeanObject,
    mut v___x_7237_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1943__boxed_7239_: u8 = 0;
    let mut v_res_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943__boxed_7239_ = (crate::leanh::lean_unbox(v___x_7237_) as u8);
    v_res_7240_ = l_Lean_addTraceAsMessages___redArg___lam__9(
        v_traceElem_7232_,
        v_toApplicative_7233_,
        v___f_7234_,
        v___f_7235_,
        v_____s_7236_,
        v___x_1943__boxed_7239_,
        v_____do__lift_7238_,
    );
    crate::leanh::lean_dec(v_____do__lift_7238_);
    return v_res_7240_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__10(
    mut v_inst_7241_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7242_: *mut crate::leanh::LeanObject,
    mut v___f_7243_: *mut crate::leanh::LeanObject,
    mut v___f_7244_: *mut crate::leanh::LeanObject,
    mut v___x_7245_: u8,
    mut v_toBind_7246_: *mut crate::leanh::LeanObject,
    mut v_traceElem_7247_: *mut crate::leanh::LeanObject,
    mut v_____s_7248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_7249_ = crate::leanh::lean_ctor_get(v_inst_7241_, 0);
    crate::leanh::lean_inc(v_getRef_7249_);
    crate::leanh::lean_dec_ref(v_inst_7241_);
    v___x_7250_ = crate::leanh::lean_box((v___x_7245_) as usize);
    v___f_7251_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__9___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_7251_, 0, v_traceElem_7247_);
    crate::leanh::lean_closure_set(v___f_7251_, 1, v_toApplicative_7242_);
    crate::leanh::lean_closure_set(v___f_7251_, 2, v___f_7243_);
    crate::leanh::lean_closure_set(v___f_7251_, 3, v___f_7244_);
    crate::leanh::lean_closure_set(v___f_7251_, 4, v_____s_7248_);
    crate::leanh::lean_closure_set(v___f_7251_, 5, v___x_7250_);
    v___x_7252_ = crate::leanh::lean_apply_4(
        v_toBind_7246_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_7249_,
        v___f_7251_,
    );
    return v___x_7252_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__10___boxed(
    mut v_inst_7253_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7254_: *mut crate::leanh::LeanObject,
    mut v___f_7255_: *mut crate::leanh::LeanObject,
    mut v___f_7256_: *mut crate::leanh::LeanObject,
    mut v___x_7257_: *mut crate::leanh::LeanObject,
    mut v_toBind_7258_: *mut crate::leanh::LeanObject,
    mut v_traceElem_7259_: *mut crate::leanh::LeanObject,
    mut v_____s_7260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2003__boxed_7261_: u8 = 0;
    let mut v_res_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2003__boxed_7261_ = (crate::leanh::lean_unbox(v___x_7257_) as u8);
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
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7263_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqRaw___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_7264_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7264_, 0, v___x_7263_);
    return v___f_7264_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7265_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__0),
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once),
        _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0,
    );
    v___f_7266_ = crate::leanh::lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7266_, 0, v___f_7265_);
    crate::leanh::lean_closure_set(v___f_7266_, 1, v___f_7265_);
    return v___f_7266_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7270_ = crate::leanh::lean_box(0);
    v___x_7271_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_7272_ = lean_mk_array(v___x_7271_, v___x_7270_);
    return v___x_7272_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7273_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__4),
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once),
        _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4,
    );
    v___x_7274_ = crate::leanh::lean_unsigned_to_nat(0);
    v_pos2traces_7275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_pos2traces_7275_, 0, v___x_7274_);
    crate::leanh::lean_ctor_set(v_pos2traces_7275_, 1, v___x_7273_);
    return v_pos2traces_7275_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__11(
    mut v_inst_7276_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7277_: *mut crate::leanh::LeanObject,
    mut v_toBind_7278_: *mut crate::leanh::LeanObject,
    mut v_inst_7279_: *mut crate::leanh::LeanObject,
    mut v___f_7280_: *mut crate::leanh::LeanObject,
    mut v_traces_7281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7282_: u8 = 0;
    v___x_7282_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_7281_);
    if v___x_7282_ == 0 {
        let mut v___f_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos2traces_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_7283_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__1),
            core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once),
            _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1,
        );
        v___f_7284_ = l_Lean_addTraceAsMessages___redArg___lam__11___closed__3;
        v___x_7285_ = crate::leanh::lean_box((v___x_7282_) as usize);
        crate::leanh::lean_inc(v_toBind_7278_);
        v___f_7286_ = crate::leanh::lean_alloc_closure(
            l_Lean_addTraceAsMessages___redArg___lam__10___boxed as *mut core::ffi::c_void,
            8,
            6,
        );
        crate::leanh::lean_closure_set(v___f_7286_, 0, v_inst_7276_);
        crate::leanh::lean_closure_set(v___f_7286_, 1, v_toApplicative_7277_);
        crate::leanh::lean_closure_set(v___f_7286_, 2, v___f_7283_);
        crate::leanh::lean_closure_set(v___f_7286_, 3, v___f_7284_);
        crate::leanh::lean_closure_set(v___f_7286_, 4, v___x_7285_);
        crate::leanh::lean_closure_set(v___f_7286_, 5, v_toBind_7278_);
        v_pos2traces_7287_ = crate::leanh::lean_obj_once(
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
        v___x_7289_ = crate::leanh::lean_apply_4(
            v_toBind_7278_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_7288_,
            v___f_7280_,
        );
        return v___x_7289_;
    } else {
        let mut v_toPure_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_7280_);
        crate::leanh::lean_dec_ref(v_inst_7279_);
        crate::leanh::lean_dec(v_toBind_7278_);
        crate::leanh::lean_dec_ref(v_inst_7276_);
        v_toPure_7290_ = crate::leanh::lean_ctor_get(v_toApplicative_7277_, 1);
        crate::leanh::lean_inc(v_toPure_7290_);
        crate::leanh::lean_dec_ref(v_toApplicative_7277_);
        v___x_7291_ = crate::leanh::lean_box(0);
        v___x_7292_ =
            crate::leanh::lean_apply_2(v_toPure_7290_, crate::leanh::lean_box(0), v___x_7291_);
        return v___x_7292_;
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__11___boxed(
    mut v_inst_7293_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7294_: *mut crate::leanh::LeanObject,
    mut v_toBind_7295_: *mut crate::leanh::LeanObject,
    mut v_inst_7296_: *mut crate::leanh::LeanObject,
    mut v___f_7297_: *mut crate::leanh::LeanObject,
    mut v_traces_7298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7299_ = l_Lean_addTraceAsMessages___redArg___lam__11(
        v_inst_7293_,
        v_toApplicative_7294_,
        v_toBind_7295_,
        v_inst_7296_,
        v___f_7297_,
        v_traces_7298_,
    );
    crate::leanh::lean_dec_ref(v_traces_7298_);
    return v_res_7299_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__12(
    mut v_toApplicative_7300_: *mut crate::leanh::LeanObject,
    mut v_inst_7301_: *mut crate::leanh::LeanObject,
    mut v_toBind_7302_: *mut crate::leanh::LeanObject,
    mut v_inst_7303_: *mut crate::leanh::LeanObject,
    mut v___f_7304_: *mut crate::leanh::LeanObject,
    mut v___f_7305_: *mut crate::leanh::LeanObject,
    mut v___f_7306_: *mut crate::leanh::LeanObject,
    mut v_inst_7307_: *mut crate::leanh::LeanObject,
    mut v_inst_7308_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: u8 = 0;
    let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7314_ = l_Lean_KVMap_instValueBool;
                v___x_7315_ = l_Lean_KVMap_instValueString;
                v___x_7316_ = l_Lean_trace_profiler_output;
                v___x_7317_ =
                    l_Lean_Option_get_x3f___redArg(v___x_7315_, v_____do__lift_7309_, v___x_7316_);
                if crate::leanh::lean_obj_tag(v___x_7317_) == 0 {
                    v___x_7318_ = l_Lean_trace_profiler_serve;
                    v___x_7319_ =
                        l_Lean_Option_get___redArg(v___x_7314_, v_____do__lift_7309_, v___x_7318_);
                    v___x_7320_ = (crate::leanh::lean_unbox(v___x_7319_) as u8);
                    crate::leanh::lean_dec(v___x_7319_);
                    if v___x_7320_ == 0 {
                        v___x_7321_ = 1;
                        v___x_7322_ = crate::leanh::lean_box((v___x_7321_) as usize);
                        crate::leanh::lean_inc_ref_n(v_inst_7303_, 2);
                        crate::leanh::lean_inc_n(v_toBind_7302_, 2);
                        crate::leanh::lean_inc_ref(v_toApplicative_7300_);
                        v___f_7323_ = crate::leanh::lean_alloc_closure(
                            l_Lean_addTraceAsMessages___redArg___lam__8___boxed
                                as *mut core::ffi::c_void,
                            9,
                            8,
                        );
                        crate::leanh::lean_closure_set(v___f_7323_, 0, v_toApplicative_7300_);
                        crate::leanh::lean_closure_set(v___f_7323_, 1, v___x_7322_);
                        crate::leanh::lean_closure_set(v___f_7323_, 2, v_inst_7301_);
                        crate::leanh::lean_closure_set(v___f_7323_, 3, v_toBind_7302_);
                        crate::leanh::lean_closure_set(v___f_7323_, 4, v_inst_7303_);
                        crate::leanh::lean_closure_set(v___f_7323_, 5, v___f_7304_);
                        crate::leanh::lean_closure_set(v___f_7323_, 6, v___f_7305_);
                        crate::leanh::lean_closure_set(v___f_7323_, 7, v___f_7306_);
                        v___f_7324_ = crate::leanh::lean_alloc_closure(
                            l_Lean_addTraceAsMessages___redArg___lam__11___boxed
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_7324_, 0, v_inst_7307_);
                        crate::leanh::lean_closure_set(v___f_7324_, 1, v_toApplicative_7300_);
                        crate::leanh::lean_closure_set(v___f_7324_, 2, v_toBind_7302_);
                        crate::leanh::lean_closure_set(v___f_7324_, 3, v_inst_7303_);
                        crate::leanh::lean_closure_set(v___f_7324_, 4, v___f_7323_);
                        v___x_7325_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(
                            v_inst_7303_,
                            v_inst_7308_,
                        );
                        v___x_7326_ = crate::leanh::lean_apply_4(
                            v_toBind_7302_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_7325_,
                            v___f_7324_,
                        );
                        return v___x_7326_;
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_7308_);
                        crate::leanh::lean_dec_ref(v_inst_7307_);
                        crate::leanh::lean_dec_ref(v___f_7306_);
                        crate::leanh::lean_dec_ref(v___f_7305_);
                        crate::leanh::lean_dec(v___f_7304_);
                        crate::leanh::lean_dec_ref(v_inst_7303_);
                        crate::leanh::lean_dec(v_toBind_7302_);
                        crate::leanh::lean_dec_ref(v_inst_7301_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7317_, 1);
                    crate::leanh::lean_dec_ref(v_inst_7308_);
                    crate::leanh::lean_dec_ref(v_inst_7307_);
                    crate::leanh::lean_dec_ref(v___f_7306_);
                    crate::leanh::lean_dec_ref(v___f_7305_);
                    crate::leanh::lean_dec(v___f_7304_);
                    crate::leanh::lean_dec_ref(v_inst_7303_);
                    crate::leanh::lean_dec(v_toBind_7302_);
                    crate::leanh::lean_dec_ref(v_inst_7301_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_7311_ = crate::leanh::lean_ctor_get(v_toApplicative_7300_, 1);
                crate::leanh::lean_inc(v_toPure_7311_);
                crate::leanh::lean_dec_ref(v_toApplicative_7300_);
                v___x_7312_ = crate::leanh::lean_box(0);
                v___x_7313_ = crate::leanh::lean_apply_2(
                    v_toPure_7311_,
                    crate::leanh::lean_box(0),
                    v___x_7312_,
                );
                return v___x_7313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg___lam__12___boxed(
    mut v_toApplicative_7327_: *mut crate::leanh::LeanObject,
    mut v_inst_7328_: *mut crate::leanh::LeanObject,
    mut v_toBind_7329_: *mut crate::leanh::LeanObject,
    mut v_inst_7330_: *mut crate::leanh::LeanObject,
    mut v___f_7331_: *mut crate::leanh::LeanObject,
    mut v___f_7332_: *mut crate::leanh::LeanObject,
    mut v___f_7333_: *mut crate::leanh::LeanObject,
    mut v_inst_7334_: *mut crate::leanh::LeanObject,
    mut v_inst_7335_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_____do__lift_7336_);
    return v_res_7337_;
}
pub unsafe fn l_Lean_addTraceAsMessages___redArg(
    mut v_inst_7340_: *mut crate::leanh::LeanObject,
    mut v_inst_7341_: *mut crate::leanh::LeanObject,
    mut v_inst_7342_: *mut crate::leanh::LeanObject,
    mut v_inst_7343_: *mut crate::leanh::LeanObject,
    mut v_inst_7344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7345_ = crate::leanh::lean_ctor_get(v_inst_7341_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_7345_, 2);
    v_toBind_7346_ = crate::leanh::lean_ctor_get(v_inst_7341_, 1);
    crate::leanh::lean_inc_n(v_toBind_7346_, 2);
    v___f_7347_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7347_, 0, v_toApplicative_7345_);
    v___f_7348_ = l_Lean_addTraceAsMessages___redArg___closed__0;
    v___f_7349_ = l_Lean_addTraceAsMessages___redArg___closed__1;
    v___f_7350_ = crate::leanh::lean_alloc_closure(
        l_Lean_addTraceAsMessages___redArg___lam__12___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_7350_, 0, v_toApplicative_7345_);
    crate::leanh::lean_closure_set(v___f_7350_, 1, v_inst_7343_);
    crate::leanh::lean_closure_set(v___f_7350_, 2, v_toBind_7346_);
    crate::leanh::lean_closure_set(v___f_7350_, 3, v_inst_7341_);
    crate::leanh::lean_closure_set(v___f_7350_, 4, v___f_7347_);
    crate::leanh::lean_closure_set(v___f_7350_, 5, v___f_7348_);
    crate::leanh::lean_closure_set(v___f_7350_, 6, v___f_7349_);
    crate::leanh::lean_closure_set(v___f_7350_, 7, v_inst_7342_);
    crate::leanh::lean_closure_set(v___f_7350_, 8, v_inst_7344_);
    v___x_7351_ = crate::leanh::lean_apply_4(
        v_toBind_7346_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7340_,
        v___f_7350_,
    );
    return v___x_7351_;
}
pub unsafe fn l_Lean_addTraceAsMessages(
    mut v_m_7352_: *mut crate::leanh::LeanObject,
    mut v_inst_7353_: *mut crate::leanh::LeanObject,
    mut v_inst_7354_: *mut crate::leanh::LeanObject,
    mut v_inst_7355_: *mut crate::leanh::LeanObject,
    mut v_inst_7356_: *mut crate::leanh::LeanObject,
    mut v_inst_7357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_7400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7400_ = crate::leanh::lean_unsigned_to_nat(2826257906);
    v___x_7401_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7402_ = l_Lean_Name_num___override(v___x_7401_, v___x_7400_);
    return v___x_7402_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7404_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7406_ = l_Lean_Name_str___override(v___x_7405_, v___x_7404_);
    return v___x_7406_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7408_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7410_ = l_Lean_Name_str___override(v___x_7409_, v___x_7408_);
    return v___x_7410_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7411_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_7412_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7413_ = l_Lean_Name_num___override(v___x_7412_, v___x_7411_);
    return v___x_7413_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: u8 = 0;
    let mut v___x_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7415_ = l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
    v___x_7416_ = 0;
    v___x_7417_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once), _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
    v___x_7418_ = l_Lean_registerTraceClass(v___x_7415_, v___x_7416_, v___x_7417_);
    return v___x_7418_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(
    mut v_a_7419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7420_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
    return v_res_7420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Trace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedTraceElem_default = _init_l_Lean_instInhabitedTraceElem_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTraceElem_default);
    l_Lean_instInhabitedTraceElem = _init_l_Lean_instInhabitedTraceElem();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTraceElem);
    l_Lean_instInhabitedTraceState_default = _init_l_Lean_instInhabitedTraceState_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTraceState_default);
    l_Lean_instInhabitedTraceState = _init_l_Lean_instInhabitedTraceState();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTraceState);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_inheritedTraceOptions = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_inheritedTraceOptions);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_threshold = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler_threshold);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_useHeartbeats = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler_useHeartbeats);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_output = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler_output);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_serve = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler_serve);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_trace_profiler_output_pp = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_trace_profiler_output_pp);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Trace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_MonadTrace_getInheritedTraceOptions___autoParam =
        _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam);
    l_Lean_registerTraceClass___auto__1 = _init_l_Lean_registerTraceClass___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_registerTraceClass___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Trace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Trace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Trace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Trace(builtin);
}
