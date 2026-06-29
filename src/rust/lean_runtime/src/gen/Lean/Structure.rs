// Lean compiler output
// Module: Lean.Structure
// Imports: Lean.ProjFns Lean.Exception Init.While Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_contains___redArg,
    l_Array_erase___redArg, l_Array_eraseReps___redArg, l_Array_instInhabited,
};
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Init::While::{
    initialize_Init_While, l___private_Init_While_0__whileM_erased___redArg,
    runtime_initialize_Init_While,
};
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_isSuffixOf, l_Lean_Name_lt___boxed, l_Lean_Name_quickLt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_instInhabitedConstructorVal_default;
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_registerEnvExtension___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Exception::{
    initialize_Lean_Exception, l_Lean_throwError___redArg, runtime_initialize_Lean_Exception,
};
use crate::r#gen::Lean::Expr::{l_Lean_instReprBinderInfo_repr, l_Lean_instReprExpr_repr};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::ProjFns::{
    initialize_Lean_ProjFns, l_Lean_Environment_getProjectionFnInfo_x3f,
    runtime_initialize_Lean_ProjFns,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
pub static l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureFieldInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureFieldInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureFieldInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value:
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
    m_data: [102, 105, 101, 108, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value:
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
    m_data: [112, 114, 111, 106, 70, 110, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value:
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
    m_data: [115, 117, 98, 111, 98, 106, 101, 99, 116, 63, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value:
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
    m_data: [98, 105, 110, 100, 101, 114, 73, 110, 102, 111, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value:
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
    m_data: [97, 117, 116, 111, 80, 97, 114, 97, 109, 63, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprStructureFieldInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprStructureFieldInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprStructureFieldInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprStructureFieldInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprStructureFieldInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureParentInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureParentInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureParentInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureParentInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureParentInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureParentInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureParentInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureInfo_default___closed__0_value:
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
static mut l_Lean_instInhabitedStructureInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureInfo_default___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureInfo_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedStructureState_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedStructureState_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedStructureState_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedStructureState_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedStructureState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Structure_0__Lean_instInhabitedStructureState:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 116, 114, 117, 99, 116, 117, 114, 101, 0]};
static mut l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13825007971868435382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,917373819288895839 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15295730036977490450 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8958634111597956511 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Structure_0__Lean_structureExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instInhabitedStructureDescr_default___closed__0_value:
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
static mut l_Lean_instInhabitedStructureDescr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureDescr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureDescr_default___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedStructureDescr_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureDescr_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureDescr_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureDescr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedStructureDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerStructure___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_registerStructure___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerStructure___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_setStructureParents___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 115, 101, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114,
        101, 32, 112, 97, 114, 101, 110, 116, 115, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_setStructureParents___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_setStructureParents___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_setStructureParents___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setStructureParents___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_setStructureParents___redArg___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        96, 44, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 110, 111, 116, 32, 100, 101,
        102, 105, 110, 101, 100, 32, 105, 110, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111,
        100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_setStructureParents___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_setStructureParents___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_setStructureParents___redArg___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setStructureParents___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_setStructureParents___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_setStructureParents___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_setStructureParents___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_setStructureParents___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_setStructureParents___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_setStructureParents___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_setStructureParents___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_setStructureParents___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getStructureInfo___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_getStructureInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getStructureInfo___closed__1_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 103, 101, 116, 83, 116, 114, 117, 99, 116, 117, 114, 101, 73,
            110, 102, 111, 0,
        ],
    };
static mut l_Lean_getStructureInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureInfo___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getStructureInfo___closed__2_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100,
            0,
        ],
    };
static mut l_Lean_getStructureInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureInfo___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getStructureInfo___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getStructureInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getStructureCtor___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 103, 101, 116, 83, 116, 114, 117, 99, 116, 117, 114, 101, 67,
            116, 111, 114, 0,
        ],
    };
static mut l_Lean_getStructureCtor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureCtor___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getStructureCtor___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getStructureCtor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_getStructureCtor___closed__2_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 101, 110, 118, 105, 114, 111, 110,
            109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_getStructureCtor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureCtor___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getStructureCtor___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getStructureCtor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkFlatCtorOfStructCtorName___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [95, 102, 108, 97, 116, 95, 99, 116, 111, 114, 0],
    };
static mut l_Lean_mkFlatCtorOfStructCtorName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkFlatCtorOfStructCtorName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkFlatCtorOfStructCtorName___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkFlatCtorOfStructCtorName___closed__0_value)
                as *mut crate::leanh::LeanObject,
            123400120243909704 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkFlatCtorOfStructCtorName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkFlatCtorOfStructCtorName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkDefaultFnOfProjFn___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lean_mkDefaultFnOfProjFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkDefaultFnOfProjFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkDefaultFnOfProjFn___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkDefaultFnOfProjFn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8097510599517763222 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkDefaultFnOfProjFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkDefaultFnOfProjFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
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
        95, 105, 110, 104, 101, 114, 105, 116, 101, 100, 95, 100, 101, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l_Lean_mkInheritedDefaultFnOfProjFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            395188960735234389 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkInheritedDefaultFnOfProjFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getDefaultFnForField_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkDefaultFnOfProjFn as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getDefaultFnForField_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getDefaultFnForField_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value:
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
    m_fun: l_Lean_mkInheritedDefaultFnOfProjFn as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getEffectiveDefaultFnForField_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkAutoParamFnOfProjFn___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [95, 97, 117, 116, 111, 80, 97, 114, 97, 109, 0],
    };
static mut l_Lean_mkAutoParamFnOfProjFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkAutoParamFnOfProjFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkAutoParamFnOfProjFn___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkAutoParamFnOfProjFn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16042815966420905854 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkAutoParamFnOfProjFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkAutoParamFnOfProjFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getAutoParamFnForField_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkAutoParamFnOfProjFn as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getAutoParamFnForField_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getAutoParamFnForField_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getNonRecStructureCtor_x3f___closed__0_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 103, 101, 116, 78, 111, 110, 82, 101, 99, 83, 116, 114, 117, 99,
            116, 117, 114, 101, 67, 116, 111, 114, 63, 0,
        ],
    };
static mut l_Lean_getNonRecStructureCtor_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getNonRecStructureCtor_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getNonRecStructureCtor_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getNonRecStructureCtor_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedStructureResolutionState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedStructureResolutionState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedStructureResolutionState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedStructureResolutionState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedStructureResolutionState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedStructureResolutionState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_structureResolutionExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value:
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
static mut l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureResolutionOrderConflict_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureResolutionOrderConflict: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value
)
    as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value:
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
static mut l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value:
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
static mut l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value:
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
            l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureResolutionOrderResult_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedStructureResolutionOrderResult: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value
)
    as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value:
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
    m_fun: l_Lean_Name_lt___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1_value:
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
static mut l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_computeStructureResolutionOrder___redArg___closed__0_value:
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
    m_fun: l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_computeStructureResolutionOrder___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_computeStructureResolutionOrder___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value:
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
    m_fun: l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_mergeStructureResolutionOrders___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_mergeStructureResolutionOrders___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_mergeStructureResolutionOrders___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getStructureResolutionOrder___redArg___closed__0_value:
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
    m_fun: l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getStructureResolutionOrder___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getStructureResolutionOrder___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(
    mut v_x_2914_: *mut crate::leanh::LeanObject,
    mut v_x_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2914_) == 0 {
        let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2916_ =
            l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1;
        return v___x_2916_;
    } else {
        let mut v_val_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2917_ = crate::leanh::lean_ctor_get(v_x_2914_, 0);
        crate::leanh::lean_inc(v_val_2917_);
        crate::leanh::lean_dec_ref_known(v_x_2914_, 1);
        v___x_2918_ =
            l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3;
        v___x_2919_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_2920_ = l_Lean_Name_reprPrec(v_val_2917_, v___x_2919_);
        v___x_2921_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2921_, 0, v___x_2918_);
        crate::leanh::lean_ctor_set(v___x_2921_, 1, v___x_2920_);
        v___x_2922_ = l_Repr_addAppParen(v___x_2921_, v_x_2915_);
        return v___x_2922_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___boxed(
    mut v_x_2923_: *mut crate::leanh::LeanObject,
    mut v_x_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2925_ =
        l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(v_x_2923_, v_x_2924_);
    crate::leanh::lean_dec(v_x_2924_);
    return v_res_2925_;
}
pub unsafe fn l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(
    mut v_x_2926_: *mut crate::leanh::LeanObject,
    mut v_x_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2926_) == 0 {
        let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2928_ =
            l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1;
        return v___x_2928_;
    } else {
        let mut v_val_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2929_ = crate::leanh::lean_ctor_get(v_x_2926_, 0);
        crate::leanh::lean_inc(v_val_2929_);
        crate::leanh::lean_dec_ref_known(v_x_2926_, 1);
        v___x_2930_ =
            l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3;
        v___x_2931_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_2932_ = l_Lean_instReprExpr_repr(v_val_2929_, v___x_2931_);
        v___x_2933_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2930_);
        crate::leanh::lean_ctor_set(v___x_2933_, 1, v___x_2932_);
        v___x_2934_ = l_Repr_addAppParen(v___x_2933_, v_x_2927_);
        return v___x_2934_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1___boxed(
    mut v_x_2935_: *mut crate::leanh::LeanObject,
    mut v_x_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ =
        l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(v_x_2935_, v_x_2936_);
    crate::leanh::lean_dec(v_x_2936_);
    return v_res_2937_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprStructureFieldInfo_repr_spec__2(
    mut v_a_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2939_ = lean_nat_to_int(v_a_2938_);
    return v___x_2939_;
}
pub unsafe fn _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_2954_ = lean_nat_to_int(v___x_2953_);
    return v___x_2954_;
}
pub unsafe fn _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_2962_ = lean_nat_to_int(v___x_2961_);
    return v___x_2962_;
}
pub unsafe fn _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2967_ = lean_nat_to_int(v___x_2966_);
    return v___x_2967_;
}
pub unsafe fn _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0;
    v___x_2976_ = lean_string_length(v___x_2975_);
    return v___x_2976_;
}
pub unsafe fn _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once),
        _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21,
    );
    v___x_2978_ = lean_nat_to_int(v___x_2977_);
    return v___x_2978_;
}
pub unsafe fn l_Lean_instReprStructureFieldInfo_repr___redArg(
    mut v_x_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fieldName_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subobject_x3f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2987_: u8 = 0;
    let mut v_autoParam_x3f_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fieldName_2984_ = crate::leanh::lean_ctor_get(v_x_2983_, 0);
    crate::leanh::lean_inc(v_fieldName_2984_);
    v_projFn_2985_ = crate::leanh::lean_ctor_get(v_x_2983_, 1);
    crate::leanh::lean_inc(v_projFn_2985_);
    v_subobject_x3f_2986_ = crate::leanh::lean_ctor_get(v_x_2983_, 2);
    crate::leanh::lean_inc(v_subobject_x3f_2986_);
    v_binderInfo_2987_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2983_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
    );
    v_autoParam_x3f_2988_ = crate::leanh::lean_ctor_get(v_x_2983_, 3);
    crate::leanh::lean_inc(v_autoParam_x3f_2988_);
    crate::leanh::lean_dec_ref(v_x_2983_);
    v___x_2989_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5;
    v___x_2990_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6;
    v___x_2991_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once),
        _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7,
    );
    v___x_2992_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2993_ = l_Lean_Name_reprPrec(v_fieldName_2984_, v___x_2992_);
    v___x_2994_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2994_, 0, v___x_2991_);
    crate::leanh::lean_ctor_set(v___x_2994_, 1, v___x_2993_);
    v___x_2995_ = 0;
    v___x_2996_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2994_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2996_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    v___x_2997_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2997_, 0, v___x_2990_);
    crate::leanh::lean_ctor_set(v___x_2997_, 1, v___x_2996_);
    v___x_2998_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9;
    v___x_2999_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_2997_);
    crate::leanh::lean_ctor_set(v___x_2999_, 1, v___x_2998_);
    v___x_3000_ = crate::leanh::lean_box(1);
    v___x_3001_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_2999_);
    crate::leanh::lean_ctor_set(v___x_3001_, 1, v___x_3000_);
    v___x_3002_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11;
    v___x_3003_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3003_, 0, v___x_3001_);
    crate::leanh::lean_ctor_set(v___x_3003_, 1, v___x_3002_);
    v___x_3004_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3003_);
    crate::leanh::lean_ctor_set(v___x_3004_, 1, v___x_2989_);
    v___x_3005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once),
        _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12,
    );
    v___x_3006_ = l_Lean_Name_reprPrec(v_projFn_2985_, v___x_2992_);
    v___x_3007_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3007_, 0, v___x_3005_);
    crate::leanh::lean_ctor_set(v___x_3007_, 1, v___x_3006_);
    v___x_3008_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3007_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3008_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    v___x_3009_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3009_, 0, v___x_3004_);
    crate::leanh::lean_ctor_set(v___x_3009_, 1, v___x_3008_);
    v___x_3010_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3009_);
    crate::leanh::lean_ctor_set(v___x_3010_, 1, v___x_2998_);
    v___x_3011_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
    crate::leanh::lean_ctor_set(v___x_3011_, 1, v___x_3000_);
    v___x_3012_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14;
    v___x_3013_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3013_, 0, v___x_3011_);
    crate::leanh::lean_ctor_set(v___x_3013_, 1, v___x_3012_);
    v___x_3014_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3014_, 0, v___x_3013_);
    crate::leanh::lean_ctor_set(v___x_3014_, 1, v___x_2989_);
    v___x_3015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once),
        _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15,
    );
    v___x_3016_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(
        v_subobject_x3f_2986_,
        v___x_2992_,
    );
    v___x_3017_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3017_, 0, v___x_3015_);
    crate::leanh::lean_ctor_set(v___x_3017_, 1, v___x_3016_);
    v___x_3018_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3018_, 0, v___x_3017_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3018_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    v___x_3019_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3019_, 0, v___x_3014_);
    crate::leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
    v___x_3020_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3020_, 0, v___x_3019_);
    crate::leanh::lean_ctor_set(v___x_3020_, 1, v___x_2998_);
    v___x_3021_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3021_, 0, v___x_3020_);
    crate::leanh::lean_ctor_set(v___x_3021_, 1, v___x_3000_);
    v___x_3022_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17;
    v___x_3023_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3023_, 0, v___x_3021_);
    crate::leanh::lean_ctor_set(v___x_3023_, 1, v___x_3022_);
    v___x_3024_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3023_);
    crate::leanh::lean_ctor_set(v___x_3024_, 1, v___x_2989_);
    v___x_3025_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2987_, v___x_2992_);
    v___x_3026_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3026_, 0, v___x_3015_);
    crate::leanh::lean_ctor_set(v___x_3026_, 1, v___x_3025_);
    v___x_3027_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3027_, 0, v___x_3026_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3027_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    v___x_3028_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3028_, 0, v___x_3024_);
    crate::leanh::lean_ctor_set(v___x_3028_, 1, v___x_3027_);
    v___x_3029_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3028_);
    crate::leanh::lean_ctor_set(v___x_3029_, 1, v___x_2998_);
    v___x_3030_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3030_, 0, v___x_3029_);
    crate::leanh::lean_ctor_set(v___x_3030_, 1, v___x_3000_);
    v___x_3031_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19;
    v___x_3032_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3032_, 0, v___x_3030_);
    crate::leanh::lean_ctor_set(v___x_3032_, 1, v___x_3031_);
    v___x_3033_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3033_, 0, v___x_3032_);
    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_2989_);
    v___x_3034_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(
        v_autoParam_x3f_2988_,
        v___x_2992_,
    );
    v___x_3035_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3035_, 0, v___x_3015_);
    crate::leanh::lean_ctor_set(v___x_3035_, 1, v___x_3034_);
    v___x_3036_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3036_, 0, v___x_3035_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3036_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    v___x_3037_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3037_, 0, v___x_3033_);
    crate::leanh::lean_ctor_set(v___x_3037_, 1, v___x_3036_);
    v___x_3038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once),
        _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22,
    );
    v___x_3039_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23;
    v___x_3040_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3040_, 0, v___x_3039_);
    crate::leanh::lean_ctor_set(v___x_3040_, 1, v___x_3037_);
    v___x_3041_ = l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24;
    v___x_3042_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3040_);
    crate::leanh::lean_ctor_set(v___x_3042_, 1, v___x_3041_);
    v___x_3043_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3043_, 0, v___x_3038_);
    crate::leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
    v___x_3044_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3044_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2995_,
    );
    return v___x_3044_;
}
pub unsafe fn l_Lean_instReprStructureFieldInfo_repr(
    mut v_x_3045_: *mut crate::leanh::LeanObject,
    mut v_prec_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3047_ = l_Lean_instReprStructureFieldInfo_repr___redArg(v_x_3045_);
    return v___x_3047_;
}
pub unsafe fn l_Lean_instReprStructureFieldInfo_repr___boxed(
    mut v_x_3048_: *mut crate::leanh::LeanObject,
    mut v_prec_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3050_ = l_Lean_instReprStructureFieldInfo_repr(v_x_3048_, v_prec_3049_);
    crate::leanh::lean_dec(v_prec_3049_);
    return v_res_3050_;
}
pub unsafe fn l_Lean_StructureFieldInfo_lt(
    mut v_i_u2081_3053_: *mut crate::leanh::LeanObject,
    mut v_i_u2082_3054_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fieldName_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldName_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    v_fieldName_3055_ = crate::leanh::lean_ctor_get(v_i_u2081_3053_, 0);
    v_fieldName_3056_ = crate::leanh::lean_ctor_get(v_i_u2082_3054_, 0);
    v___x_3057_ = l_Lean_Name_quickLt(v_fieldName_3055_, v_fieldName_3056_);
    return v___x_3057_;
}
pub unsafe fn l_Lean_StructureFieldInfo_lt___boxed(
    mut v_i_u2081_3058_: *mut crate::leanh::LeanObject,
    mut v_i_u2082_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3060_: u8 = 0;
    let mut v_r_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Lean_StructureFieldInfo_lt(v_i_u2081_3058_, v_i_u2082_3059_);
    crate::leanh::lean_dec_ref(v_i_u2082_3059_);
    crate::leanh::lean_dec_ref(v_i_u2081_3058_);
    v_r_3061_ = crate::leanh::lean_box((v_res_3060_) as usize);
    return v_r_3061_;
}
pub unsafe fn l_Lean_StructureInfo_lt(
    mut v_i_u2081_3074_: *mut crate::leanh::LeanObject,
    mut v_i_u2082_3075_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_structName_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    v_structName_3076_ = crate::leanh::lean_ctor_get(v_i_u2081_3074_, 0);
    v_structName_3077_ = crate::leanh::lean_ctor_get(v_i_u2082_3075_, 0);
    v___x_3078_ = l_Lean_Name_quickLt(v_structName_3076_, v_structName_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Lean_StructureInfo_lt___boxed(
    mut v_i_u2081_3079_: *mut crate::leanh::LeanObject,
    mut v_i_u2082_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3081_: u8 = 0;
    let mut v_r_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3081_ = l_Lean_StructureInfo_lt(v_i_u2081_3079_, v_i_u2082_3080_);
    crate::leanh::lean_dec_ref(v_i_u2082_3080_);
    crate::leanh::lean_dec_ref(v_i_u2081_3079_);
    v_r_3082_ = crate::leanh::lean_box((v_res_3081_) as usize);
    return v_r_3082_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(
    mut v_as_3083_: *mut crate::leanh::LeanObject,
    mut v_k_3084_: *mut crate::leanh::LeanObject,
    mut v_x_3085_: *mut crate::leanh::LeanObject,
    mut v_x_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3087_ = lean_nat_add(v_x_3085_, v_x_3086_);
                v___x_3088_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_3089_ = lean_nat_shiftr(v___x_3087_, v___x_3088_);
                crate::leanh::lean_dec(v___x_3087_);
                v_a_3090_ = lean_array_fget_borrowed(v_as_3083_, v_m_3089_);
                v___x_3091_ = l_Lean_StructureFieldInfo_lt(v_a_3090_, v_k_3084_);
                if v___x_3091_ == 0 {
                    crate::leanh::lean_dec(v_x_3086_);
                    v___x_3092_ = l_Lean_StructureFieldInfo_lt(v_k_3084_, v_a_3090_);
                    if v___x_3092_ == 0 {
                        crate::leanh::lean_dec(v_m_3089_);
                        crate::leanh::lean_dec(v_x_3085_);
                        crate::leanh::lean_inc(v_a_3090_);
                        v___x_3093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3093_, 0, v_a_3090_);
                        return v___x_3093_;
                    } else {
                        v___x_3094_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3095_ = lean_nat_dec_eq(v_m_3089_, v___x_3094_);
                        if v___x_3095_ == 0 {
                            v___x_3096_ = lean_nat_sub(v_m_3089_, v___x_3088_);
                            crate::leanh::lean_dec(v_m_3089_);
                            v___x_3097_ = lean_nat_dec_lt(v___x_3096_, v_x_3085_);
                            if v___x_3097_ == 0 {
                                v_x_3086_ = v___x_3096_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3096_);
                                crate::leanh::lean_dec(v_x_3085_);
                                v___x_3099_ = crate::leanh::lean_box(0);
                                return v___x_3099_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_3089_);
                            crate::leanh::lean_dec(v_x_3085_);
                            v___x_3100_ = crate::leanh::lean_box(0);
                            return v___x_3100_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3085_);
                    v___x_3101_ = lean_nat_add(v_m_3089_, v___x_3088_);
                    crate::leanh::lean_dec(v_m_3089_);
                    v___x_3102_ = lean_nat_dec_le(v___x_3101_, v_x_3086_);
                    if v___x_3102_ == 0 {
                        crate::leanh::lean_dec(v___x_3101_);
                        crate::leanh::lean_dec(v_x_3086_);
                        v___x_3103_ = crate::leanh::lean_box(0);
                        return v___x_3103_;
                    } else {
                        v_x_3085_ = v___x_3101_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(
    mut v_as_3105_: *mut crate::leanh::LeanObject,
    mut v_k_3106_: *mut crate::leanh::LeanObject,
    mut v_x_3107_: *mut crate::leanh::LeanObject,
    mut v_x_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(
        v_as_3105_, v_k_3106_, v_x_3107_, v_x_3108_,
    );
    crate::leanh::lean_dec_ref(v_k_3106_);
    crate::leanh::lean_dec_ref(v_as_3105_);
    return v_res_3109_;
}
pub unsafe fn l_Lean_StructureInfo_getProjFn_x3f(
    mut v_info_3110_: *mut crate::leanh::LeanObject,
    mut v_i_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fieldNames_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v_fieldName_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v_projFn_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fieldNames_3112_ = crate::leanh::lean_ctor_get(v_info_3110_, 1);
                v_fieldInfo_3113_ = crate::leanh::lean_ctor_get(v_info_3110_, 2);
                v___x_3114_ = lean_array_get_size(v_fieldNames_3112_);
                v___x_3115_ = lean_nat_dec_lt(v_i_3111_, v___x_3114_);
                if v___x_3115_ == 0 {
                    v___x_3116_ = crate::leanh::lean_box(0);
                    return v___x_3116_;
                } else {
                    v___x_3117_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3118_ = lean_array_get_size(v_fieldInfo_3113_);
                    v___x_3119_ = lean_nat_dec_lt(v___x_3117_, v___x_3118_);
                    if v___x_3119_ == 0 {
                        v___x_3120_ = crate::leanh::lean_box(0);
                        return v___x_3120_;
                    } else {
                        v___x_3121_ = crate::leanh::lean_box(0);
                        v___x_3122_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3123_ = lean_nat_sub(v___x_3118_, v___x_3122_);
                        v___x_3124_ = lean_nat_dec_le(v___x_3117_, v___x_3123_);
                        if v___x_3124_ == 0 {
                            crate::leanh::lean_dec(v___x_3123_);
                            return v___x_3121_;
                        } else {
                            v_fieldName_3125_ =
                                lean_array_fget_borrowed(v_fieldNames_3112_, v_i_3111_);
                            v___x_3126_ = crate::leanh::lean_box(0);
                            v___x_3127_ = 0;
                            crate::leanh::lean_inc(v_fieldName_3125_);
                            v___x_3128_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3128_, 0, v_fieldName_3125_);
                            crate::leanh::lean_ctor_set(v___x_3128_, 1, v___x_3126_);
                            crate::leanh::lean_ctor_set(v___x_3128_, 2, v___x_3121_);
                            crate::leanh::lean_ctor_set(v___x_3128_, 3, v___x_3121_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3128_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v___x_3127_,
                            );
                            v___x_3129_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_3113_, v___x_3128_, v___x_3117_, v___x_3123_);
                            crate::leanh::lean_dec_ref_known(v___x_3128_, 4);
                            if crate::leanh::lean_obj_tag(v___x_3129_) == 0 {
                                return v___x_3121_;
                            } else {
                                v_val_3130_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                                v_isSharedCheck_3138_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                                if v_isSharedCheck_3138_ == 0 {
                                    v___x_3132_ = v___x_3129_;
                                    v_isShared_3133_ = v_isSharedCheck_3138_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3130_);
                                    crate::leanh::lean_dec(v___x_3129_);
                                    v___x_3132_ = crate::leanh::lean_box(0);
                                    v_isShared_3133_ = v_isSharedCheck_3138_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_projFn_3134_ = crate::leanh::lean_ctor_get(v_val_3130_, 1);
                crate::leanh::lean_inc(v_projFn_3134_);
                crate::leanh::lean_dec(v_val_3130_);
                if v_isShared_3133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3132_, 0, v_projFn_3134_);
                    v___x_3136_ = v___x_3132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_projFn_3134_);
                    v___x_3136_ = v_reuseFailAlloc_3137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_StructureInfo_getProjFn_x3f___boxed(
    mut v_info_3139_: *mut crate::leanh::LeanObject,
    mut v_i_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lean_StructureInfo_getProjFn_x3f(v_info_3139_, v_i_3140_);
    crate::leanh::lean_dec(v_i_3140_);
    crate::leanh::lean_dec_ref(v_info_3139_);
    return v_res_3141_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(
    mut v_as_3142_: *mut crate::leanh::LeanObject,
    mut v_k_3143_: *mut crate::leanh::LeanObject,
    mut v_x_3144_: *mut crate::leanh::LeanObject,
    mut v_x_3145_: *mut crate::leanh::LeanObject,
    mut v_x_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(
        v_as_3142_, v_k_3143_, v_x_3144_, v_x_3145_,
    );
    return v___x_3147_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(
    mut v_as_3148_: *mut crate::leanh::LeanObject,
    mut v_k_3149_: *mut crate::leanh::LeanObject,
    mut v_x_3150_: *mut crate::leanh::LeanObject,
    mut v_x_3151_: *mut crate::leanh::LeanObject,
    mut v_x_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3153_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(
        v_as_3148_, v_k_3149_, v_x_3150_, v_x_3151_, v_x_3152_,
    );
    crate::leanh::lean_dec_ref(v_k_3149_);
    crate::leanh::lean_dec_ref(v_as_3148_);
    return v_res_3153_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3154_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3154_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__0_once),
        _init_l_Lean_instInhabitedStructureState_default___closed__0,
    );
    v___x_3156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    return v___x_3156_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureState_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__1_once),
        _init_l_Lean_instInhabitedStructureState_default___closed__1,
    );
    return v___x_3157_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Lean_instInhabitedStructureState_default;
    return v___x_3158_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v_x_3159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3160_ = crate::leanh::lean_box(0);
    return v___x_3160_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v_x_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v_x_3161_);
    crate::leanh::lean_dec_ref(v_x_3161_);
    return v_res_3162_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(
    mut v_sz_3163_: usize,
    mut v_i_3164_: usize,
    mut v_bs_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3166_: u8 = 0;
    let mut v_v_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: usize = 0;
    let mut v___x_3172_: usize = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3166_ = lean_usize_dec_lt(v_i_3164_, v_sz_3163_);
                if v___x_3166_ == 0 {
                    return v_bs_3165_;
                } else {
                    v_v_3167_ = lean_array_uget_borrowed(v_bs_3165_, v_i_3164_);
                    v_snd_3168_ = crate::leanh::lean_ctor_get(v_v_3167_, 1);
                    crate::leanh::lean_inc(v_snd_3168_);
                    v___x_3169_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3170_ = lean_array_uset(v_bs_3165_, v_i_3164_, v___x_3169_);
                    v___x_3171_ = 1usize;
                    v___x_3172_ = lean_usize_add(v_i_3164_, v___x_3171_);
                    v___x_3173_ = lean_array_uset(v_bs_x27_3170_, v_i_3164_, v_snd_3168_);
                    v_i_3164_ = v___x_3172_;
                    v_bs_3165_ = v___x_3173_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(
    mut v_sz_3175_: *mut crate::leanh::LeanObject,
    mut v_i_3176_: *mut crate::leanh::LeanObject,
    mut v_bs_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3178_: usize = 0;
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3178_ = crate::leanh::lean_unbox_usize(v_sz_3175_);
    crate::leanh::lean_dec(v_sz_3175_);
    v_i_boxed_3179_ = crate::leanh::lean_unbox_usize(v_i_3176_);
    crate::leanh::lean_dec(v_i_3176_);
    v_res_3180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_boxed_3178_, v_i_boxed_3179_, v_bs_3177_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v_ps_3181_: *mut crate::leanh::LeanObject,
    mut v_k_3182_: *mut crate::leanh::LeanObject,
    mut v_v_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3184_, 0, v_k_3182_);
    crate::leanh::lean_ctor_set(v___x_3184_, 1, v_v_3183_);
    v___x_3185_ = lean_array_push(v_ps_3181_, v___x_3184_);
    return v___x_3185_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(
    mut v_f_3186_: *mut crate::leanh::LeanObject,
    mut v_keys_3187_: *mut crate::leanh::LeanObject,
    mut v_vals_3188_: *mut crate::leanh::LeanObject,
    mut v_i_3189_: *mut crate::leanh::LeanObject,
    mut v_acc_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v_k_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3191_ = lean_array_get_size(v_keys_3187_);
                v___x_3192_ = lean_nat_dec_lt(v_i_3189_, v___x_3191_);
                if v___x_3192_ == 0 {
                    crate::leanh::lean_dec(v_i_3189_);
                    crate::leanh::lean_dec(v_f_3186_);
                    return v_acc_3190_;
                } else {
                    v_k_3193_ = lean_array_fget_borrowed(v_keys_3187_, v_i_3189_);
                    v_v_3194_ = lean_array_fget_borrowed(v_vals_3188_, v_i_3189_);
                    crate::leanh::lean_inc(v_f_3186_);
                    crate::leanh::lean_inc(v_v_3194_);
                    crate::leanh::lean_inc(v_k_3193_);
                    v___x_3195_ =
                        crate::leanh::lean_apply_3(v_f_3186_, v_acc_3190_, v_k_3193_, v_v_3194_);
                    v___x_3196_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3197_ = lean_nat_add(v_i_3189_, v___x_3196_);
                    crate::leanh::lean_dec(v_i_3189_);
                    v_i_3189_ = v___x_3197_;
                    v_acc_3190_ = v___x_3195_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(
    mut v_f_3199_: *mut crate::leanh::LeanObject,
    mut v_keys_3200_: *mut crate::leanh::LeanObject,
    mut v_vals_3201_: *mut crate::leanh::LeanObject,
    mut v_i_3202_: *mut crate::leanh::LeanObject,
    mut v_acc_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_3199_, v_keys_3200_, v_vals_3201_, v_i_3202_, v_acc_3203_);
    crate::leanh::lean_dec_ref(v_vals_3201_);
    crate::leanh::lean_dec_ref(v_keys_3200_);
    return v_res_3204_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_f_3205_: *mut crate::leanh::LeanObject,
    mut v_x_3206_: *mut crate::leanh::LeanObject,
    mut v_x_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3206_) == 0 {
        let mut v_es_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3211_: u8 = 0;
        v_es_3208_ = crate::leanh::lean_ctor_get(v_x_3206_, 0);
        v___x_3209_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3210_ = lean_array_get_size(v_es_3208_);
        v___x_3211_ = lean_nat_dec_lt(v___x_3209_, v___x_3210_);
        if v___x_3211_ == 0 {
            crate::leanh::lean_dec(v_f_3205_);
            return v_x_3207_;
        } else {
            let mut v___x_3212_: u8 = 0;
            v___x_3212_ = lean_nat_dec_le(v___x_3210_, v___x_3210_);
            if v___x_3212_ == 0 {
                if v___x_3211_ == 0 {
                    crate::leanh::lean_dec(v_f_3205_);
                    return v_x_3207_;
                } else {
                    let mut v___x_3213_: usize = 0;
                    let mut v___x_3214_: usize = 0;
                    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3213_ = 0usize;
                    v___x_3214_ = lean_usize_of_nat(v___x_3210_);
                    v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_3205_, v_es_3208_, v___x_3213_, v___x_3214_, v_x_3207_);
                    return v___x_3215_;
                }
            } else {
                let mut v___x_3216_: usize = 0;
                let mut v___x_3217_: usize = 0;
                let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3216_ = 0usize;
                v___x_3217_ = lean_usize_of_nat(v___x_3210_);
                v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_3205_, v_es_3208_, v___x_3216_, v___x_3217_, v_x_3207_);
                return v___x_3218_;
            }
        }
    } else {
        let mut v_ks_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_3219_ = crate::leanh::lean_ctor_get(v_x_3206_, 0);
        v_vs_3220_ = crate::leanh::lean_ctor_get(v_x_3206_, 1);
        v___x_3221_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_3205_, v_ks_3219_, v_vs_3220_, v___x_3221_, v_x_3207_);
        return v___x_3222_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(
    mut v_f_3223_: *mut crate::leanh::LeanObject,
    mut v_as_3224_: *mut crate::leanh::LeanObject,
    mut v_i_3225_: usize,
    mut v_stop_3226_: usize,
    mut v_b_3227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3233_ = lean_usize_dec_eq(v_i_3225_, v_stop_3226_);
                if v___x_3233_ == 0 {
                    v___x_3234_ = lean_array_uget_borrowed(v_as_3224_, v_i_3225_);
                    match crate::leanh::lean_obj_tag(v___x_3234_) {
                        0 => {
                            v_key_3235_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                            v_val_3236_ = crate::leanh::lean_ctor_get(v___x_3234_, 1);
                            crate::leanh::lean_inc(v_f_3223_);
                            crate::leanh::lean_inc(v_val_3236_);
                            crate::leanh::lean_inc(v_key_3235_);
                            v___x_3237_ = crate::leanh::lean_apply_3(
                                v_f_3223_,
                                v_b_3227_,
                                v_key_3235_,
                                v_val_3236_,
                            );
                            v___y_3229_ = v___x_3237_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3238_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                            crate::leanh::lean_inc(v_f_3223_);
                            v___x_3239_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_3223_, v_node_3238_, v_b_3227_);
                            v___y_3229_ = v___x_3239_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3229_ = v_b_3227_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_3223_);
                    return v_b_3227_;
                }
            }
            1 => {
                v___x_3230_ = 1usize;
                v___x_3231_ = lean_usize_add(v_i_3225_, v___x_3230_);
                v_i_3225_ = v___x_3231_;
                v_b_3227_ = v___y_3229_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(
    mut v_f_3240_: *mut crate::leanh::LeanObject,
    mut v_as_3241_: *mut crate::leanh::LeanObject,
    mut v_i_3242_: *mut crate::leanh::LeanObject,
    mut v_stop_3243_: *mut crate::leanh::LeanObject,
    mut v_b_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3245_: usize = 0;
    let mut v_stop_boxed_3246_: usize = 0;
    let mut v_res_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3245_ = crate::leanh::lean_unbox_usize(v_i_3242_);
    crate::leanh::lean_dec(v_i_3242_);
    v_stop_boxed_3246_ = crate::leanh::lean_unbox_usize(v_stop_3243_);
    crate::leanh::lean_dec(v_stop_3243_);
    v_res_3247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_3240_, v_as_3241_, v_i_boxed_3245_, v_stop_boxed_3246_, v_b_3244_);
    crate::leanh::lean_dec_ref(v_as_3241_);
    return v_res_3247_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_f_3248_: *mut crate::leanh::LeanObject,
    mut v_x_3249_: *mut crate::leanh::LeanObject,
    mut v_x_3250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_3248_, v_x_3249_, v_x_3250_);
    crate::leanh::lean_dec_ref(v_x_3249_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(
    mut v_f_3252_: *mut crate::leanh::LeanObject,
    mut v_x1_3253_: *mut crate::leanh::LeanObject,
    mut v_x2_3254_: *mut crate::leanh::LeanObject,
    mut v_x3_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = crate::leanh::lean_apply_3(v_f_3252_, v_x1_3253_, v_x2_3254_, v_x3_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_map_3257_: *mut crate::leanh::LeanObject,
    mut v_f_3258_: *mut crate::leanh::LeanObject,
    mut v_init_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3260_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3260_, 0, v_f_3258_);
    v___x_3261_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_3260_, v_map_3257_, v_init_3259_);
    return v___x_3261_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_map_3262_: *mut crate::leanh::LeanObject,
    mut v_f_3263_: *mut crate::leanh::LeanObject,
    mut v_init_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3265_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_3262_, v_f_3263_, v_init_3264_);
    crate::leanh::lean_dec_ref(v_map_3262_);
    return v_res_3265_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3270_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0;
    v___x_3271_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1;
    v___x_3272_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_3269_, v___f_3270_, v___x_3271_);
    return v___x_3272_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_m_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_3273_);
    crate::leanh::lean_dec_ref(v_m_3273_);
    return v_res_3274_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_hi_3275_: *mut crate::leanh::LeanObject,
    mut v_pivot_3276_: *mut crate::leanh::LeanObject,
    mut v_as_3277_: *mut crate::leanh::LeanObject,
    mut v_i_3278_: *mut crate::leanh::LeanObject,
    mut v_k_3279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3280_ = lean_nat_dec_lt(v_k_3279_, v_hi_3275_);
                if v___x_3280_ == 0 {
                    crate::leanh::lean_dec(v_k_3279_);
                    v___x_3281_ = lean_array_fswap(v_as_3277_, v_i_3278_, v_hi_3275_);
                    v___x_3282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v_i_3278_);
                    crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3281_);
                    return v___x_3282_;
                } else {
                    v___x_3283_ = lean_array_fget_borrowed(v_as_3277_, v_k_3279_);
                    v___x_3284_ = l_Lean_StructureInfo_lt(v___x_3283_, v_pivot_3276_);
                    if v___x_3284_ == 0 {
                        v___x_3285_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3286_ = lean_nat_add(v_k_3279_, v___x_3285_);
                        crate::leanh::lean_dec(v_k_3279_);
                        v_k_3279_ = v___x_3286_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3288_ = lean_array_fswap(v_as_3277_, v_i_3278_, v_k_3279_);
                        v___x_3289_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3290_ = lean_nat_add(v_i_3278_, v___x_3289_);
                        crate::leanh::lean_dec(v_i_3278_);
                        v___x_3291_ = lean_nat_add(v_k_3279_, v___x_3289_);
                        crate::leanh::lean_dec(v_k_3279_);
                        v_as_3277_ = v___x_3288_;
                        v_i_3278_ = v___x_3290_;
                        v_k_3279_ = v___x_3291_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_hi_3293_: *mut crate::leanh::LeanObject,
    mut v_pivot_3294_: *mut crate::leanh::LeanObject,
    mut v_as_3295_: *mut crate::leanh::LeanObject,
    mut v_i_3296_: *mut crate::leanh::LeanObject,
    mut v_k_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_3293_, v_pivot_3294_, v_as_3295_, v_i_3296_, v_k_3297_);
    crate::leanh::lean_dec_ref(v_pivot_3294_);
    crate::leanh::lean_dec(v_hi_3293_);
    return v_res_3298_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_3299_: *mut crate::leanh::LeanObject,
    mut v_as_3300_: *mut crate::leanh::LeanObject,
    mut v_lo_3301_: *mut crate::leanh::LeanObject,
    mut v_hi_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3314_ = lean_nat_dec_lt(v_lo_3301_, v_hi_3302_);
                if v___x_3314_ == 0 {
                    crate::leanh::lean_dec(v_lo_3301_);
                    return v_as_3300_;
                } else {
                    v___x_3315_ = lean_nat_add(v_lo_3301_, v_hi_3302_);
                    v___x_3316_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3317_ = lean_nat_shiftr(v___x_3315_, v___x_3316_);
                    crate::leanh::lean_dec(v___x_3315_);
                    v___x_3330_ = lean_array_fget_borrowed(v_as_3300_, v_mid_3317_);
                    v___x_3331_ = lean_array_fget_borrowed(v_as_3300_, v_lo_3301_);
                    v___x_3332_ = l_Lean_StructureInfo_lt(v___x_3330_, v___x_3331_);
                    if v___x_3332_ == 0 {
                        v___y_3325_ = v_as_3300_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3333_ = lean_array_fswap(v_as_3300_, v_lo_3301_, v_mid_3317_);
                        v___y_3325_ = v___x_3333_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3305_ = lean_array_fget(v___y_3304_, v_hi_3302_);
                crate::leanh::lean_inc_n(v_lo_3301_, 2);
                v___x_3306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_3302_, v_pivot_3305_, v___y_3304_, v_lo_3301_, v_lo_3301_);
                crate::leanh::lean_dec(v_pivot_3305_);
                v_fst_3307_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                crate::leanh::lean_inc(v_fst_3307_);
                v_snd_3308_ = crate::leanh::lean_ctor_get(v___x_3306_, 1);
                crate::leanh::lean_inc(v_snd_3308_);
                crate::leanh::lean_dec_ref(v___x_3306_);
                v___x_3309_ = lean_nat_dec_le(v_hi_3302_, v_fst_3307_);
                if v___x_3309_ == 0 {
                    v___x_3310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_3299_, v_snd_3308_, v_lo_3301_, v_fst_3307_);
                    v___x_3311_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3312_ = lean_nat_add(v_fst_3307_, v___x_3311_);
                    crate::leanh::lean_dec(v_fst_3307_);
                    v_as_3300_ = v___x_3310_;
                    v_lo_3301_ = v___x_3312_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3307_);
                    crate::leanh::lean_dec(v_lo_3301_);
                    return v_snd_3308_;
                }
            }
            2 => {
                v___x_3320_ = lean_array_fget_borrowed(v___y_3319_, v_mid_3317_);
                v___x_3321_ = lean_array_fget_borrowed(v___y_3319_, v_hi_3302_);
                v___x_3322_ = l_Lean_StructureInfo_lt(v___x_3320_, v___x_3321_);
                if v___x_3322_ == 0 {
                    crate::leanh::lean_dec(v_mid_3317_);
                    v___y_3304_ = v___y_3319_;
                    state = 1;
                    continue;
                } else {
                    v___x_3323_ = lean_array_fswap(v___y_3319_, v_mid_3317_, v_hi_3302_);
                    crate::leanh::lean_dec(v_mid_3317_);
                    v___y_3304_ = v___x_3323_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3326_ = lean_array_fget_borrowed(v___y_3325_, v_hi_3302_);
                v___x_3327_ = lean_array_fget_borrowed(v___y_3325_, v_lo_3301_);
                v___x_3328_ = l_Lean_StructureInfo_lt(v___x_3326_, v___x_3327_);
                if v___x_3328_ == 0 {
                    v___y_3319_ = v___y_3325_;
                    state = 2;
                    continue;
                } else {
                    v___x_3329_ = lean_array_fswap(v___y_3325_, v_lo_3301_, v_hi_3302_);
                    v___y_3319_ = v___x_3329_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_n_3334_: *mut crate::leanh::LeanObject,
    mut v_as_3335_: *mut crate::leanh::LeanObject,
    mut v_lo_3336_: *mut crate::leanh::LeanObject,
    mut v_hi_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_3334_, v_as_3335_, v_lo_3336_, v_hi_3337_);
    crate::leanh::lean_dec(v_hi_3337_);
    crate::leanh::lean_dec(v_n_3334_);
    return v_res_3338_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v___x_3339_: *mut crate::leanh::LeanObject,
    mut v_x_3340_: *mut crate::leanh::LeanObject,
    mut v_s_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3342_ = crate::leanh::lean_ctor_get(v_s_3341_, 1);
                v___x_3343_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_3342_);
                v_sz_3344_ = lean_array_size(v___x_3343_);
                v___x_3345_ = 0usize;
                v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_3344_, v___x_3345_, v___x_3343_);
                v___x_3347_ = lean_array_get_size(v___x_3346_);
                v___x_3353_ = lean_nat_dec_eq(v___x_3347_, v___x_3339_);
                if v___x_3353_ == 0 {
                    v___x_3354_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3355_ = lean_nat_sub(v___x_3347_, v___x_3354_);
                    v___x_3359_ = lean_nat_dec_le(v___x_3339_, v___x_3355_);
                    if v___x_3359_ == 0 {
                        crate::leanh::lean_dec(v___x_3339_);
                        crate::leanh::lean_inc(v___x_3355_);
                        v___y_3357_ = v___x_3355_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3357_ = v___x_3339_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3339_);
                    crate::leanh::lean_inc_ref_n(v___x_3346_, 2);
                    v___x_3360_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3346_);
                    crate::leanh::lean_ctor_set(v___x_3360_, 1, v___x_3346_);
                    crate::leanh::lean_ctor_set(v___x_3360_, 2, v___x_3346_);
                    return v___x_3360_;
                }
            }
            1 => {
                v___x_3351_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_3347_, v___x_3346_, v___y_3349_, v___y_3350_);
                crate::leanh::lean_dec(v___y_3350_);
                crate::leanh::lean_inc_ref_n(v___x_3351_, 2);
                v___x_3352_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
                crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3351_);
                crate::leanh::lean_ctor_set(v___x_3352_, 2, v___x_3351_);
                return v___x_3352_;
            }
            2 => {
                v___x_3358_ = lean_nat_dec_le(v___y_3357_, v___x_3355_);
                if v___x_3358_ == 0 {
                    crate::leanh::lean_dec(v___x_3355_);
                    crate::leanh::lean_inc(v___y_3357_);
                    v___y_3349_ = v___y_3357_;
                    v___y_3350_ = v___y_3357_;
                    state = 1;
                    continue;
                } else {
                    v___y_3349_ = v___y_3357_;
                    v___y_3350_ = v___x_3355_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v___x_3361_: *mut crate::leanh::LeanObject,
    mut v_x_3362_: *mut crate::leanh::LeanObject,
    mut v_s_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_3361_, v_x_3362_, v_s_3363_);
    crate::leanh::lean_dec_ref(v_s_3363_);
    crate::leanh::lean_dec_ref(v_x_3362_);
    return v_res_3364_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v___x_3365_: *mut crate::leanh::LeanObject,
    mut v_x_3366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3369_: usize = 0;
    let mut v___x_3370_: usize = 0;
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u8 = 0;
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u8 = 0;
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3367_ = crate::leanh::lean_ctor_get(v_x_3366_, 1);
                v___x_3368_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_3367_);
                v_sz_3369_ = lean_array_size(v___x_3368_);
                v___x_3370_ = 0usize;
                v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_3369_, v___x_3370_, v___x_3368_);
                v___x_3372_ = lean_array_get_size(v___x_3371_);
                v___x_3373_ = lean_nat_dec_eq(v___x_3372_, v___x_3365_);
                if v___x_3373_ == 0 {
                    v___x_3374_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3375_ = lean_nat_sub(v___x_3372_, v___x_3374_);
                    v___x_3381_ = lean_nat_dec_le(v___x_3365_, v___x_3375_);
                    if v___x_3381_ == 0 {
                        crate::leanh::lean_dec(v___x_3365_);
                        crate::leanh::lean_inc(v___x_3375_);
                        v___y_3377_ = v___x_3375_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3377_ = v___x_3365_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3365_);
                    return v___x_3371_;
                }
            }
            1 => {
                v___x_3378_ = lean_nat_dec_le(v___y_3377_, v___x_3375_);
                if v___x_3378_ == 0 {
                    crate::leanh::lean_dec(v___x_3375_);
                    crate::leanh::lean_inc(v___y_3377_);
                    v___x_3379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_3372_, v___x_3371_, v___y_3377_, v___y_3377_);
                    crate::leanh::lean_dec(v___y_3377_);
                    return v___x_3379_;
                } else {
                    v___x_3380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_3372_, v___x_3371_, v___y_3377_, v___x_3375_);
                    crate::leanh::lean_dec(v___x_3375_);
                    return v___x_3380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v___x_3382_: *mut crate::leanh::LeanObject,
    mut v_x_3383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3384_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_3382_, v_x_3383_);
    crate::leanh::lean_dec_ref(v_x_3383_);
    return v_res_3384_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_x_3385_: *mut crate::leanh::LeanObject,
    mut v_x_3386_: *mut crate::leanh::LeanObject,
    mut v_x_3387_: *mut crate::leanh::LeanObject,
    mut v_x_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3389_ = crate::leanh::lean_ctor_get(v_x_3385_, 0);
                v_vs_3390_ = crate::leanh::lean_ctor_get(v_x_3385_, 1);
                v_isSharedCheck_3414_ = (!crate::leanh::lean_is_exclusive(v_x_3385_)) as u8;
                if v_isSharedCheck_3414_ == 0 {
                    v___x_3392_ = v_x_3385_;
                    v_isShared_3393_ = v_isSharedCheck_3414_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3390_);
                    crate::leanh::lean_inc(v_ks_3389_);
                    crate::leanh::lean_dec(v_x_3385_);
                    v___x_3392_ = crate::leanh::lean_box(0);
                    v_isShared_3393_ = v_isSharedCheck_3414_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3394_ = lean_array_get_size(v_ks_3389_);
                v___x_3395_ = lean_nat_dec_lt(v_x_3386_, v___x_3394_);
                if v___x_3395_ == 0 {
                    crate::leanh::lean_dec(v_x_3386_);
                    v___x_3396_ = lean_array_push(v_ks_3389_, v_x_3387_);
                    v___x_3397_ = lean_array_push(v_vs_3390_, v_x_3388_);
                    if v_isShared_3393_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3392_, 1, v___x_3397_);
                        crate::leanh::lean_ctor_set(v___x_3392_, 0, v___x_3396_);
                        v___x_3399_ = v___x_3392_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3400_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3396_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3397_);
                        v___x_3399_ = v_reuseFailAlloc_3400_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3401_ = lean_array_fget_borrowed(v_ks_3389_, v_x_3386_);
                    v___x_3402_ = lean_name_eq(v_x_3387_, v_k_x27_3401_);
                    if v___x_3402_ == 0 {
                        if v_isShared_3393_ == 0 {
                            v___x_3404_ = v___x_3392_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3408_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_ks_3389_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_vs_3390_);
                            v___x_3404_ = v_reuseFailAlloc_3408_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3409_ = lean_array_fset(v_ks_3389_, v_x_3386_, v_x_3387_);
                        v___x_3410_ = lean_array_fset(v_vs_3390_, v_x_3386_, v_x_3388_);
                        crate::leanh::lean_dec(v_x_3386_);
                        if v_isShared_3393_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3392_, 1, v___x_3410_);
                            crate::leanh::lean_ctor_set(v___x_3392_, 0, v___x_3409_);
                            v___x_3412_ = v___x_3392_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3413_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3409_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3410_);
                            v___x_3412_ = v_reuseFailAlloc_3413_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3399_;
            }
            3 => {
                v___x_3405_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3406_ = lean_nat_add(v_x_3386_, v___x_3405_);
                crate::leanh::lean_dec(v_x_3386_);
                v_x_3385_ = v___x_3404_;
                v_x_3386_ = v___x_3406_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(
    mut v_n_3415_: *mut crate::leanh::LeanObject,
    mut v_k_3416_: *mut crate::leanh::LeanObject,
    mut v_v_3417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3419_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_n_3415_, v___x_3418_, v_k_3416_, v_v_3417_);
    return v___x_3419_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0()
-> u64 {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: u64 = 0;
    v___x_3420_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3421_ = lean_uint64_of_nat(v___x_3420_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_3422_: usize = 0;
    let mut v___x_3423_: usize = 0;
    let mut v___x_3424_: usize = 0;
    v___x_3422_ = 5usize;
    v___x_3423_ = 1usize;
    v___x_3424_ = lean_usize_shift_left(v___x_3423_, v___x_3422_);
    return v___x_3424_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_3425_: usize = 0;
    let mut v___x_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    v___x_3425_ = 1usize;
    v___x_3426_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
    v___x_3427_ = lean_usize_sub(v___x_3426_, v___x_3425_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3428_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(
    mut v_x_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: usize,
    mut v_x_3431_: usize,
    mut v_x_3432_: *mut crate::leanh::LeanObject,
    mut v_x_3433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: usize = 0;
    let mut v___x_3438_: usize = 0;
    let mut v_j_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v_v_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_node_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: usize = 0;
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_unused_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: u8 = 0;
    let mut v_ks_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: usize = 0;
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: u8 = 0;
    let mut v_reuseFailAlloc_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3429_) == 0 {
                    v_es_3434_ = crate::leanh::lean_ctor_get(v_x_3429_, 0);
                    v___x_3435_ = 5usize;
                    v___x_3436_ = 1usize;
                    v___x_3437_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
                    v___x_3438_ = lean_usize_land(v_x_3430_, v___x_3437_);
                    v_j_3439_ = lean_usize_to_nat(v___x_3438_);
                    v___x_3440_ = lean_array_get_size(v_es_3434_);
                    v___x_3441_ = lean_nat_dec_lt(v_j_3439_, v___x_3440_);
                    if v___x_3441_ == 0 {
                        crate::leanh::lean_dec(v_j_3439_);
                        crate::leanh::lean_dec(v_x_3433_);
                        crate::leanh::lean_dec(v_x_3432_);
                        return v_x_3429_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3434_);
                        v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v_x_3429_)) as u8;
                        if v_isSharedCheck_3478_ == 0 {
                            v_unused_3479_ = crate::leanh::lean_ctor_get(v_x_3429_, 0);
                            crate::leanh::lean_dec(v_unused_3479_);
                            v___x_3443_ = v_x_3429_;
                            v_isShared_3444_ = v_isSharedCheck_3478_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3429_);
                            v___x_3443_ = crate::leanh::lean_box(0);
                            v_isShared_3444_ = v_isSharedCheck_3478_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3480_ = crate::leanh::lean_ctor_get(v_x_3429_, 0);
                    v_vs_3481_ = crate::leanh::lean_ctor_get(v_x_3429_, 1);
                    v_isSharedCheck_3501_ = (!crate::leanh::lean_is_exclusive(v_x_3429_)) as u8;
                    if v_isSharedCheck_3501_ == 0 {
                        v___x_3483_ = v_x_3429_;
                        v_isShared_3484_ = v_isSharedCheck_3501_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3481_);
                        crate::leanh::lean_inc(v_ks_3480_);
                        crate::leanh::lean_dec(v_x_3429_);
                        v___x_3483_ = crate::leanh::lean_box(0);
                        v_isShared_3484_ = v_isSharedCheck_3501_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3445_ = lean_array_fget(v_es_3434_, v_j_3439_);
                v___x_3446_ = crate::leanh::lean_box(0);
                v_xs_x27_3447_ = lean_array_fset(v_es_3434_, v_j_3439_, v___x_3446_);
                match crate::leanh::lean_obj_tag(v_v_3445_) {
                    0 => {
                        v_key_3454_ = crate::leanh::lean_ctor_get(v_v_3445_, 0);
                        v_val_3455_ = crate::leanh::lean_ctor_get(v_v_3445_, 1);
                        v_isSharedCheck_3465_ = (!crate::leanh::lean_is_exclusive(v_v_3445_)) as u8;
                        if v_isSharedCheck_3465_ == 0 {
                            v___x_3457_ = v_v_3445_;
                            v_isShared_3458_ = v_isSharedCheck_3465_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3455_);
                            crate::leanh::lean_inc(v_key_3454_);
                            crate::leanh::lean_dec(v_v_3445_);
                            v___x_3457_ = crate::leanh::lean_box(0);
                            v_isShared_3458_ = v_isSharedCheck_3465_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3466_ = crate::leanh::lean_ctor_get(v_v_3445_, 0);
                        v_isSharedCheck_3476_ = (!crate::leanh::lean_is_exclusive(v_v_3445_)) as u8;
                        if v_isSharedCheck_3476_ == 0 {
                            v___x_3468_ = v_v_3445_;
                            v_isShared_3469_ = v_isSharedCheck_3476_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3466_);
                            crate::leanh::lean_dec(v_v_3445_);
                            v___x_3468_ = crate::leanh::lean_box(0);
                            v_isShared_3469_ = v_isSharedCheck_3476_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3477_, 0, v_x_3432_);
                        crate::leanh::lean_ctor_set(v___x_3477_, 1, v_x_3433_);
                        v___y_3449_ = v___x_3477_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3450_ = lean_array_fset(v_xs_x27_3447_, v_j_3439_, v___y_3449_);
                crate::leanh::lean_dec(v_j_3439_);
                if v_isShared_3444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3443_, 0, v___x_3450_);
                    v___x_3452_ = v___x_3443_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3452_;
            }
            4 => {
                v___x_3459_ = lean_name_eq(v_x_3432_, v_key_3454_);
                if v___x_3459_ == 0 {
                    crate::leanh::lean_del_object(v___x_3457_);
                    v___x_3460_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3454_,
                        v_val_3455_,
                        v_x_3432_,
                        v_x_3433_,
                    );
                    v___x_3461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3460_);
                    v___y_3449_ = v___x_3461_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3455_);
                    crate::leanh::lean_dec(v_key_3454_);
                    if v_isShared_3458_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3457_, 1, v_x_3433_);
                        crate::leanh::lean_ctor_set(v___x_3457_, 0, v_x_3432_);
                        v___x_3463_ = v___x_3457_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_x_3432_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_x_3433_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3449_ = v___x_3463_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3470_ = lean_usize_shift_right(v_x_3430_, v___x_3435_);
                v___x_3471_ = lean_usize_add(v_x_3431_, v___x_3436_);
                v___x_3472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_3466_, v___x_3470_, v___x_3471_, v_x_3432_, v_x_3433_);
                if v_isShared_3469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3468_, 0, v___x_3472_);
                    v___x_3474_ = v___x_3468_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
                    v___x_3474_ = v_reuseFailAlloc_3475_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3449_ = v___x_3474_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3484_ == 0 {
                    v___x_3486_ = v___x_3483_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_ks_3480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_vs_3481_);
                    v___x_3486_ = v_reuseFailAlloc_3500_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3487_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_3486_, v_x_3432_, v_x_3433_);
                v___x_3495_ = 7usize;
                v___x_3496_ = lean_usize_dec_le(v___x_3495_, v_x_3431_);
                if v___x_3496_ == 0 {
                    v___x_3497_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3487_);
                    v___x_3498_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3499_ = lean_nat_dec_lt(v___x_3497_, v___x_3498_);
                    crate::leanh::lean_dec(v___x_3497_);
                    v___y_3489_ = v___x_3499_;
                    state = 10;
                    continue;
                } else {
                    v___y_3489_ = v___x_3496_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3489_ == 0 {
                    v_ks_3490_ = crate::leanh::lean_ctor_get(v_newNode_3487_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3490_);
                    v_vs_3491_ = crate::leanh::lean_ctor_get(v_newNode_3487_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3491_);
                    crate::leanh::lean_dec_ref(v_newNode_3487_);
                    v___x_3492_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3493_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2);
                    v___x_3494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_3431_, v_ks_3490_, v_vs_3491_, v___x_3492_, v___x_3493_);
                    crate::leanh::lean_dec_ref(v_vs_3491_);
                    crate::leanh::lean_dec_ref(v_ks_3490_);
                    return v___x_3494_;
                } else {
                    return v_newNode_3487_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(
    mut v_depth_3502_: usize,
    mut v_keys_3503_: *mut crate::leanh::LeanObject,
    mut v_vals_3504_: *mut crate::leanh::LeanObject,
    mut v_i_3505_: *mut crate::leanh::LeanObject,
    mut v_entries_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v_k_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: u64 = 0;
    let mut v_h_3513_: usize = 0;
    let mut v___x_3514_: usize = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: usize = 0;
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: usize = 0;
    let mut v_h_3519_: usize = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u64 = 0;
    let mut v_hash_3524_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3507_ = lean_array_get_size(v_keys_3503_);
                v___x_3508_ = lean_nat_dec_lt(v_i_3505_, v___x_3507_);
                if v___x_3508_ == 0 {
                    crate::leanh::lean_dec(v_i_3505_);
                    return v_entries_3506_;
                } else {
                    v_k_3509_ = lean_array_fget_borrowed(v_keys_3503_, v_i_3505_);
                    v_v_3510_ = lean_array_fget_borrowed(v_vals_3504_, v_i_3505_);
                    if crate::leanh::lean_obj_tag(v_k_3509_) == 0 {
                        v___x_3523_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
                        v___y_3512_ = v___x_3523_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3524_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_3509_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3512_ = v_hash_3524_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3513_ = lean_uint64_to_usize(v___y_3512_);
                v___x_3514_ = 5usize;
                v___x_3515_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3516_ = 1usize;
                v___x_3517_ = lean_usize_sub(v_depth_3502_, v___x_3516_);
                v___x_3518_ = lean_usize_mul(v___x_3514_, v___x_3517_);
                v_h_3519_ = lean_usize_shift_right(v_h_3513_, v___x_3518_);
                v___x_3520_ = lean_nat_add(v_i_3505_, v___x_3515_);
                crate::leanh::lean_dec(v_i_3505_);
                crate::leanh::lean_inc(v_v_3510_);
                crate::leanh::lean_inc(v_k_3509_);
                v___x_3521_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_3506_, v_h_3519_, v_depth_3502_, v_k_3509_, v_v_3510_);
                v_i_3505_ = v___x_3520_;
                v_entries_3506_ = v___x_3521_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(
    mut v_depth_3525_: *mut crate::leanh::LeanObject,
    mut v_keys_3526_: *mut crate::leanh::LeanObject,
    mut v_vals_3527_: *mut crate::leanh::LeanObject,
    mut v_i_3528_: *mut crate::leanh::LeanObject,
    mut v_entries_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3530_: usize = 0;
    let mut v_res_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3530_ = crate::leanh::lean_unbox_usize(v_depth_3525_);
    crate::leanh::lean_dec(v_depth_3525_);
    v_res_3531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_3530_, v_keys_3526_, v_vals_3527_, v_i_3528_, v_entries_3529_);
    crate::leanh::lean_dec_ref(v_vals_3527_);
    crate::leanh::lean_dec_ref(v_keys_3526_);
    return v_res_3531_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(
    mut v_x_3532_: *mut crate::leanh::LeanObject,
    mut v_x_3533_: *mut crate::leanh::LeanObject,
    mut v_x_3534_: *mut crate::leanh::LeanObject,
    mut v_x_3535_: *mut crate::leanh::LeanObject,
    mut v_x_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1842__boxed_3537_: usize = 0;
    let mut v_x_1843__boxed_3538_: usize = 0;
    let mut v_res_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1842__boxed_3537_ = crate::leanh::lean_unbox_usize(v_x_3533_);
    crate::leanh::lean_dec(v_x_3533_);
    v_x_1843__boxed_3538_ = crate::leanh::lean_unbox_usize(v_x_3534_);
    crate::leanh::lean_dec(v_x_3534_);
    v_res_3539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_3532_, v_x_1842__boxed_3537_, v_x_1843__boxed_3538_, v_x_3535_, v_x_3536_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(
    mut v_x_3540_: *mut crate::leanh::LeanObject,
    mut v_x_3541_: *mut crate::leanh::LeanObject,
    mut v_x_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3544_: u64 = 0;
    let mut v___x_3545_: usize = 0;
    let mut v___x_3546_: usize = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: u64 = 0;
    let mut v_hash_3549_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3541_) == 0 {
                    v___x_3548_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
                    v___y_3544_ = v___x_3548_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3549_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3541_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3544_ = v_hash_3549_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3545_ = lean_uint64_to_usize(v___y_3544_);
                v___x_3546_ = 1usize;
                v___x_3547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_3540_, v___x_3545_, v___x_3546_, v_x_3541_, v_x_3542_);
                return v___x_3547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v___x_3550_: *mut crate::leanh::LeanObject,
    mut v_x_3551_: *mut crate::leanh::LeanObject,
    mut v_e_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v_structName_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_unused_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3553_ = crate::leanh::lean_ctor_get(v_x_3551_, 1);
                v_isSharedCheck_3562_ = (!crate::leanh::lean_is_exclusive(v_x_3551_)) as u8;
                if v_isSharedCheck_3562_ == 0 {
                    v_unused_3563_ = crate::leanh::lean_ctor_get(v_x_3551_, 0);
                    crate::leanh::lean_dec(v_unused_3563_);
                    v___x_3555_ = v_x_3551_;
                    v_isShared_3556_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3553_);
                    crate::leanh::lean_dec(v_x_3551_);
                    v___x_3555_ = crate::leanh::lean_box(0);
                    v_isShared_3556_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_structName_3557_ = crate::leanh::lean_ctor_get(v_e_3552_, 0);
                crate::leanh::lean_inc(v_structName_3557_);
                v___x_3558_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_3553_, v_structName_3557_, v_e_3552_);
                if v_isShared_3556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3555_, 1, v___x_3558_);
                    crate::leanh::lean_ctor_set(v___x_3555_, 0, v___x_3550_);
                    v___x_3560_ = v___x_3555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3558_);
                    v___x_3560_ = v_reuseFailAlloc_3561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v___x_3564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3566_, 0, v___x_3564_);
    return v___x_3566_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v___x_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3569_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_3567_);
    return v_res_3569_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(
    mut v___x_3570_: *mut crate::leanh::LeanObject,
    mut v_x_3571_: *mut crate::leanh::LeanObject,
    mut v___y_3572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3570_);
    return v___x_3574_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v___x_3575_: *mut crate::leanh::LeanObject,
    mut v_x_3576_: *mut crate::leanh::LeanObject,
    mut v___y_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3579_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_3575_, v_x_3576_, v___y_3577_);
    crate::leanh::lean_dec_ref(v___y_3577_);
    crate::leanh::lean_dec_ref(v_x_3576_);
    return v_res_3579_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureState_default___closed__1_once),
        _init_l_Lean_instInhabitedStructureState_default___closed__1,
    );
    v___x_3610_ = crate::leanh::lean_box(0);
    v___x_3611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3610_);
    crate::leanh::lean_ctor_set(v___x_3611_, 1, v___x_3609_);
    return v___x_3611_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___f_3613_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_3613_, 0, v___x_3612_);
    return v___f_3613_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___f_3615_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3615_, 0, v___x_3614_);
    return v___f_3615_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = crate::leanh::lean_box(0);
    v___x_3617_ = crate::leanh::lean_box(2);
    v___f_3618_ = l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
    v___f_3619_ = l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
    v___f_3620_ = l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
    v___f_3621_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___f_3622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___x_3623_ = l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
    v___x_3624_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
    crate::leanh::lean_ctor_set(v___x_3624_, 1, v___f_3622_);
    crate::leanh::lean_ctor_set(v___x_3624_, 2, v___f_3621_);
    crate::leanh::lean_ctor_set(v___x_3624_, 3, v___f_3620_);
    crate::leanh::lean_ctor_set(v___x_3624_, 4, v___f_3619_);
    crate::leanh::lean_ctor_set(v___x_3624_, 5, v___f_3618_);
    crate::leanh::lean_ctor_set(v___x_3624_, 6, v___x_3617_);
    crate::leanh::lean_ctor_set(v___x_3624_, 7, v___x_3616_);
    return v___x_3624_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3625_ = l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
    v___x_3626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___x_3627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3627_, 0, v___x_3626_);
    crate::leanh::lean_ctor_set(v___x_3627_, 1, v___f_3625_);
    return v___x_3627_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3629_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
    v___x_3630_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(
    mut v_a_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
    return v_res_3632_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_3633_: *mut crate::leanh::LeanObject,
    mut v_m_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_3634_);
    return v___x_3635_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b2_3636_: *mut crate::leanh::LeanObject,
    mut v_m_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_3636_, v_m_3637_);
    crate::leanh::lean_dec_ref(v_m_3637_);
    return v_res_3638_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(
    mut v_n_3639_: *mut crate::leanh::LeanObject,
    mut v_as_3640_: *mut crate::leanh::LeanObject,
    mut v_lo_3641_: *mut crate::leanh::LeanObject,
    mut v_hi_3642_: *mut crate::leanh::LeanObject,
    mut v_w_3643_: *mut crate::leanh::LeanObject,
    mut v_hlo_3644_: *mut crate::leanh::LeanObject,
    mut v_hhi_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_3639_, v_as_3640_, v_lo_3641_, v_hi_3642_);
    return v___x_3646_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_3647_: *mut crate::leanh::LeanObject,
    mut v_as_3648_: *mut crate::leanh::LeanObject,
    mut v_lo_3649_: *mut crate::leanh::LeanObject,
    mut v_hi_3650_: *mut crate::leanh::LeanObject,
    mut v_w_3651_: *mut crate::leanh::LeanObject,
    mut v_hlo_3652_: *mut crate::leanh::LeanObject,
    mut v_hhi_3653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_3647_, v_as_3648_, v_lo_3649_, v_hi_3650_, v_w_3651_, v_hlo_3652_, v_hhi_3653_);
    crate::leanh::lean_dec(v_hi_3650_);
    crate::leanh::lean_dec(v_n_3647_);
    return v_res_3654_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(
    mut v_00_u03b2_3655_: *mut crate::leanh::LeanObject,
    mut v_x_3656_: *mut crate::leanh::LeanObject,
    mut v_x_3657_: *mut crate::leanh::LeanObject,
    mut v_x_3658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_3656_, v_x_3657_, v_x_3658_);
    return v___x_3659_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03c3_3660_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3661_: *mut crate::leanh::LeanObject,
    mut v_map_3662_: *mut crate::leanh::LeanObject,
    mut v_f_3663_: *mut crate::leanh::LeanObject,
    mut v_init_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_3662_, v_f_3663_, v_init_3664_);
    return v___x_3665_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03c3_3666_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3667_: *mut crate::leanh::LeanObject,
    mut v_map_3668_: *mut crate::leanh::LeanObject,
    mut v_f_3669_: *mut crate::leanh::LeanObject,
    mut v_init_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_3666_, v_00_u03b2_3667_, v_map_3668_, v_f_3669_, v_init_3670_);
    crate::leanh::lean_dec_ref(v_map_3668_);
    return v_res_3671_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(
    mut v_n_3672_: *mut crate::leanh::LeanObject,
    mut v_lo_3673_: *mut crate::leanh::LeanObject,
    mut v_hi_3674_: *mut crate::leanh::LeanObject,
    mut v_hhi_3675_: *mut crate::leanh::LeanObject,
    mut v_pivot_3676_: *mut crate::leanh::LeanObject,
    mut v_as_3677_: *mut crate::leanh::LeanObject,
    mut v_i_3678_: *mut crate::leanh::LeanObject,
    mut v_k_3679_: *mut crate::leanh::LeanObject,
    mut v_ilo_3680_: *mut crate::leanh::LeanObject,
    mut v_ik_3681_: *mut crate::leanh::LeanObject,
    mut v_w_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_3674_, v_pivot_3676_, v_as_3677_, v_i_3678_, v_k_3679_);
    return v___x_3683_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_n_3684_: *mut crate::leanh::LeanObject,
    mut v_lo_3685_: *mut crate::leanh::LeanObject,
    mut v_hi_3686_: *mut crate::leanh::LeanObject,
    mut v_hhi_3687_: *mut crate::leanh::LeanObject,
    mut v_pivot_3688_: *mut crate::leanh::LeanObject,
    mut v_as_3689_: *mut crate::leanh::LeanObject,
    mut v_i_3690_: *mut crate::leanh::LeanObject,
    mut v_k_3691_: *mut crate::leanh::LeanObject,
    mut v_ilo_3692_: *mut crate::leanh::LeanObject,
    mut v_ik_3693_: *mut crate::leanh::LeanObject,
    mut v_w_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_3684_, v_lo_3685_, v_hi_3686_, v_hhi_3687_, v_pivot_3688_, v_as_3689_, v_i_3690_, v_k_3691_, v_ilo_3692_, v_ik_3693_, v_w_3694_);
    crate::leanh::lean_dec_ref(v_pivot_3688_);
    crate::leanh::lean_dec(v_hi_3686_);
    crate::leanh::lean_dec(v_lo_3685_);
    crate::leanh::lean_dec(v_n_3684_);
    return v_res_3695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(
    mut v_00_u03b2_3696_: *mut crate::leanh::LeanObject,
    mut v_x_3697_: *mut crate::leanh::LeanObject,
    mut v_x_3698_: usize,
    mut v_x_3699_: usize,
    mut v_x_3700_: *mut crate::leanh::LeanObject,
    mut v_x_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_3697_, v_x_3698_, v_x_3699_, v_x_3700_, v_x_3701_);
    return v___x_3702_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_00_u03b2_3703_: *mut crate::leanh::LeanObject,
    mut v_x_3704_: *mut crate::leanh::LeanObject,
    mut v_x_3705_: *mut crate::leanh::LeanObject,
    mut v_x_3706_: *mut crate::leanh::LeanObject,
    mut v_x_3707_: *mut crate::leanh::LeanObject,
    mut v_x_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2245__boxed_3709_: usize = 0;
    let mut v_x_2246__boxed_3710_: usize = 0;
    let mut v_res_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2245__boxed_3709_ = crate::leanh::lean_unbox_usize(v_x_3705_);
    crate::leanh::lean_dec(v_x_3705_);
    v_x_2246__boxed_3710_ = crate::leanh::lean_unbox_usize(v_x_3706_);
    crate::leanh::lean_dec(v_x_3706_);
    v_res_3711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_3703_, v_x_3704_, v_x_2245__boxed_3709_, v_x_2246__boxed_3710_, v_x_3707_, v_x_3708_);
    return v_res_3711_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_map_3712_: *mut crate::leanh::LeanObject,
    mut v_f_3713_: *mut crate::leanh::LeanObject,
    mut v_init_3714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_3713_, v_map_3712_, v_init_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_map_3716_: *mut crate::leanh::LeanObject,
    mut v_f_3717_: *mut crate::leanh::LeanObject,
    mut v_init_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_3716_, v_f_3717_, v_init_3718_);
    crate::leanh::lean_dec_ref(v_map_3716_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03c3_3720_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3721_: *mut crate::leanh::LeanObject,
    mut v_map_3722_: *mut crate::leanh::LeanObject,
    mut v_f_3723_: *mut crate::leanh::LeanObject,
    mut v_init_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_3723_, v_map_3722_, v_init_3724_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_3726_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3727_: *mut crate::leanh::LeanObject,
    mut v_map_3728_: *mut crate::leanh::LeanObject,
    mut v_f_3729_: *mut crate::leanh::LeanObject,
    mut v_init_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3731_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_3726_, v_00_u03b2_3727_, v_map_3728_, v_f_3729_, v_init_3730_);
    crate::leanh::lean_dec_ref(v_map_3728_);
    return v_res_3731_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(
    mut v_00_u03b2_3732_: *mut crate::leanh::LeanObject,
    mut v_n_3733_: *mut crate::leanh::LeanObject,
    mut v_k_3734_: *mut crate::leanh::LeanObject,
    mut v_v_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_3733_, v_k_3734_, v_v_3735_);
    return v___x_3736_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(
    mut v_00_u03b2_3737_: *mut crate::leanh::LeanObject,
    mut v_depth_3738_: usize,
    mut v_keys_3739_: *mut crate::leanh::LeanObject,
    mut v_vals_3740_: *mut crate::leanh::LeanObject,
    mut v_heq_3741_: *mut crate::leanh::LeanObject,
    mut v_i_3742_: *mut crate::leanh::LeanObject,
    mut v_entries_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_3738_, v_keys_3739_, v_vals_3740_, v_i_3742_, v_entries_3743_);
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_3745_: *mut crate::leanh::LeanObject,
    mut v_depth_3746_: *mut crate::leanh::LeanObject,
    mut v_keys_3747_: *mut crate::leanh::LeanObject,
    mut v_vals_3748_: *mut crate::leanh::LeanObject,
    mut v_heq_3749_: *mut crate::leanh::LeanObject,
    mut v_i_3750_: *mut crate::leanh::LeanObject,
    mut v_entries_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3752_: usize = 0;
    let mut v_res_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3752_ = crate::leanh::lean_unbox_usize(v_depth_3746_);
    crate::leanh::lean_dec(v_depth_3746_);
    v_res_3753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_3745_, v_depth_boxed_3752_, v_keys_3747_, v_vals_3748_, v_heq_3749_, v_i_3750_, v_entries_3751_);
    crate::leanh::lean_dec_ref(v_vals_3748_);
    crate::leanh::lean_dec_ref(v_keys_3747_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03c3_3754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3756_: *mut crate::leanh::LeanObject,
    mut v_f_3757_: *mut crate::leanh::LeanObject,
    mut v_x_3758_: *mut crate::leanh::LeanObject,
    mut v_x_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3760_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_3757_, v_x_3758_, v_x_3759_);
    return v___x_3760_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03c3_3761_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3762_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3763_: *mut crate::leanh::LeanObject,
    mut v_f_3764_: *mut crate::leanh::LeanObject,
    mut v_x_3765_: *mut crate::leanh::LeanObject,
    mut v_x_3766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3767_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_3761_, v_00_u03b1_3762_, v_00_u03b2_3763_, v_f_3764_, v_x_3765_, v_x_3766_);
    crate::leanh::lean_dec_ref(v_x_3765_);
    return v_res_3767_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b2_3768_: *mut crate::leanh::LeanObject,
    mut v_x_3769_: *mut crate::leanh::LeanObject,
    mut v_x_3770_: *mut crate::leanh::LeanObject,
    mut v_x_3771_: *mut crate::leanh::LeanObject,
    mut v_x_3772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_3769_, v_x_3770_, v_x_3771_, v_x_3772_);
    return v___x_3773_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(
    mut v_00_u03b1_3774_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3775_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3776_: *mut crate::leanh::LeanObject,
    mut v_f_3777_: *mut crate::leanh::LeanObject,
    mut v_as_3778_: *mut crate::leanh::LeanObject,
    mut v_i_3779_: usize,
    mut v_stop_3780_: usize,
    mut v_b_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_3777_, v_as_3778_, v_i_3779_, v_stop_3780_, v_b_3781_);
    return v___x_3782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(
    mut v_00_u03b1_3783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3784_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3785_: *mut crate::leanh::LeanObject,
    mut v_f_3786_: *mut crate::leanh::LeanObject,
    mut v_as_3787_: *mut crate::leanh::LeanObject,
    mut v_i_3788_: *mut crate::leanh::LeanObject,
    mut v_stop_3789_: *mut crate::leanh::LeanObject,
    mut v_b_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3791_: usize = 0;
    let mut v_stop_boxed_3792_: usize = 0;
    let mut v_res_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3791_ = crate::leanh::lean_unbox_usize(v_i_3788_);
    crate::leanh::lean_dec(v_i_3788_);
    v_stop_boxed_3792_ = crate::leanh::lean_unbox_usize(v_stop_3789_);
    crate::leanh::lean_dec(v_stop_3789_);
    v_res_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_3783_, v_00_u03b2_3784_, v_00_u03c3_3785_, v_f_3786_, v_as_3787_, v_i_boxed_3791_, v_stop_boxed_3792_, v_b_3790_);
    crate::leanh::lean_dec_ref(v_as_3787_);
    return v_res_3793_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(
    mut v_00_u03c3_3794_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3796_: *mut crate::leanh::LeanObject,
    mut v_f_3797_: *mut crate::leanh::LeanObject,
    mut v_keys_3798_: *mut crate::leanh::LeanObject,
    mut v_vals_3799_: *mut crate::leanh::LeanObject,
    mut v_heq_3800_: *mut crate::leanh::LeanObject,
    mut v_i_3801_: *mut crate::leanh::LeanObject,
    mut v_acc_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_3797_, v_keys_3798_, v_vals_3799_, v_i_3801_, v_acc_3802_);
    return v___x_3803_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(
    mut v_00_u03c3_3804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3806_: *mut crate::leanh::LeanObject,
    mut v_f_3807_: *mut crate::leanh::LeanObject,
    mut v_keys_3808_: *mut crate::leanh::LeanObject,
    mut v_vals_3809_: *mut crate::leanh::LeanObject,
    mut v_heq_3810_: *mut crate::leanh::LeanObject,
    mut v_i_3811_: *mut crate::leanh::LeanObject,
    mut v_acc_3812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_3804_, v_00_u03b1_3805_, v_00_u03b2_3806_, v_f_3807_, v_keys_3808_, v_vals_3809_, v_heq_3810_, v_i_3811_, v_acc_3812_);
    crate::leanh::lean_dec_ref(v_vals_3809_);
    crate::leanh::lean_dec_ref(v_keys_3808_);
    return v_res_3813_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(
    mut v_sz_3821_: usize,
    mut v_i_3822_: usize,
    mut v_bs_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: u8 = 0;
    let mut v_v_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldName_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: usize = 0;
    let mut v___x_3830_: usize = 0;
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3824_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
                if v___x_3824_ == 0 {
                    return v_bs_3823_;
                } else {
                    v_v_3825_ = lean_array_uget_borrowed(v_bs_3823_, v_i_3822_);
                    v_fieldName_3826_ = crate::leanh::lean_ctor_get(v_v_3825_, 0);
                    crate::leanh::lean_inc(v_fieldName_3826_);
                    v___x_3827_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3828_ = lean_array_uset(v_bs_3823_, v_i_3822_, v___x_3827_);
                    v___x_3829_ = 1usize;
                    v___x_3830_ = lean_usize_add(v_i_3822_, v___x_3829_);
                    v___x_3831_ = lean_array_uset(v_bs_x27_3828_, v_i_3822_, v_fieldName_3826_);
                    v_i_3822_ = v___x_3830_;
                    v_bs_3823_ = v___x_3831_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(
    mut v_sz_3833_: *mut crate::leanh::LeanObject,
    mut v_i_3834_: *mut crate::leanh::LeanObject,
    mut v_bs_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3836_: usize = 0;
    let mut v_i_boxed_3837_: usize = 0;
    let mut v_res_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3836_ = crate::leanh::lean_unbox_usize(v_sz_3833_);
    crate::leanh::lean_dec(v_sz_3833_);
    v_i_boxed_3837_ = crate::leanh::lean_unbox_usize(v_i_3834_);
    crate::leanh::lean_dec(v_i_3834_);
    v_res_3838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_3836_, v_i_boxed_3837_, v_bs_3835_);
    return v_res_3838_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(
    mut v_hi_3839_: *mut crate::leanh::LeanObject,
    mut v_pivot_3840_: *mut crate::leanh::LeanObject,
    mut v_as_3841_: *mut crate::leanh::LeanObject,
    mut v_i_3842_: *mut crate::leanh::LeanObject,
    mut v_k_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3844_ = lean_nat_dec_lt(v_k_3843_, v_hi_3839_);
                if v___x_3844_ == 0 {
                    crate::leanh::lean_dec(v_k_3843_);
                    v___x_3845_ = lean_array_fswap(v_as_3841_, v_i_3842_, v_hi_3839_);
                    v___x_3846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3846_, 0, v_i_3842_);
                    crate::leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
                    return v___x_3846_;
                } else {
                    v___x_3847_ = lean_array_fget_borrowed(v_as_3841_, v_k_3843_);
                    v___x_3848_ = l_Lean_StructureFieldInfo_lt(v___x_3847_, v_pivot_3840_);
                    if v___x_3848_ == 0 {
                        v___x_3849_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3850_ = lean_nat_add(v_k_3843_, v___x_3849_);
                        crate::leanh::lean_dec(v_k_3843_);
                        v_k_3843_ = v___x_3850_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3852_ = lean_array_fswap(v_as_3841_, v_i_3842_, v_k_3843_);
                        v___x_3853_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3854_ = lean_nat_add(v_i_3842_, v___x_3853_);
                        crate::leanh::lean_dec(v_i_3842_);
                        v___x_3855_ = lean_nat_add(v_k_3843_, v___x_3853_);
                        crate::leanh::lean_dec(v_k_3843_);
                        v_as_3841_ = v___x_3852_;
                        v_i_3842_ = v___x_3854_;
                        v_k_3843_ = v___x_3855_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(
    mut v_hi_3857_: *mut crate::leanh::LeanObject,
    mut v_pivot_3858_: *mut crate::leanh::LeanObject,
    mut v_as_3859_: *mut crate::leanh::LeanObject,
    mut v_i_3860_: *mut crate::leanh::LeanObject,
    mut v_k_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_3857_, v_pivot_3858_, v_as_3859_, v_i_3860_, v_k_3861_);
    crate::leanh::lean_dec_ref(v_pivot_3858_);
    crate::leanh::lean_dec(v_hi_3857_);
    return v_res_3862_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(
    mut v_n_3863_: *mut crate::leanh::LeanObject,
    mut v_as_3864_: *mut crate::leanh::LeanObject,
    mut v_lo_3865_: *mut crate::leanh::LeanObject,
    mut v_hi_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: u8 = 0;
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3878_ = lean_nat_dec_lt(v_lo_3865_, v_hi_3866_);
                if v___x_3878_ == 0 {
                    crate::leanh::lean_dec(v_lo_3865_);
                    return v_as_3864_;
                } else {
                    v___x_3879_ = lean_nat_add(v_lo_3865_, v_hi_3866_);
                    v___x_3880_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3881_ = lean_nat_shiftr(v___x_3879_, v___x_3880_);
                    crate::leanh::lean_dec(v___x_3879_);
                    v___x_3894_ = lean_array_fget_borrowed(v_as_3864_, v_mid_3881_);
                    v___x_3895_ = lean_array_fget_borrowed(v_as_3864_, v_lo_3865_);
                    v___x_3896_ = l_Lean_StructureFieldInfo_lt(v___x_3894_, v___x_3895_);
                    if v___x_3896_ == 0 {
                        v___y_3889_ = v_as_3864_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3897_ = lean_array_fswap(v_as_3864_, v_lo_3865_, v_mid_3881_);
                        v___y_3889_ = v___x_3897_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3869_ = lean_array_fget(v___y_3868_, v_hi_3866_);
                crate::leanh::lean_inc_n(v_lo_3865_, 2);
                v___x_3870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_3866_, v_pivot_3869_, v___y_3868_, v_lo_3865_, v_lo_3865_);
                crate::leanh::lean_dec(v_pivot_3869_);
                v_fst_3871_ = crate::leanh::lean_ctor_get(v___x_3870_, 0);
                crate::leanh::lean_inc(v_fst_3871_);
                v_snd_3872_ = crate::leanh::lean_ctor_get(v___x_3870_, 1);
                crate::leanh::lean_inc(v_snd_3872_);
                crate::leanh::lean_dec_ref(v___x_3870_);
                v___x_3873_ = lean_nat_dec_le(v_hi_3866_, v_fst_3871_);
                if v___x_3873_ == 0 {
                    v___x_3874_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_3863_, v_snd_3872_, v_lo_3865_, v_fst_3871_);
                    v___x_3875_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3876_ = lean_nat_add(v_fst_3871_, v___x_3875_);
                    crate::leanh::lean_dec(v_fst_3871_);
                    v_as_3864_ = v___x_3874_;
                    v_lo_3865_ = v___x_3876_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3871_);
                    crate::leanh::lean_dec(v_lo_3865_);
                    return v_snd_3872_;
                }
            }
            2 => {
                v___x_3884_ = lean_array_fget_borrowed(v___y_3883_, v_mid_3881_);
                v___x_3885_ = lean_array_fget_borrowed(v___y_3883_, v_hi_3866_);
                v___x_3886_ = l_Lean_StructureFieldInfo_lt(v___x_3884_, v___x_3885_);
                if v___x_3886_ == 0 {
                    crate::leanh::lean_dec(v_mid_3881_);
                    v___y_3868_ = v___y_3883_;
                    state = 1;
                    continue;
                } else {
                    v___x_3887_ = lean_array_fswap(v___y_3883_, v_mid_3881_, v_hi_3866_);
                    crate::leanh::lean_dec(v_mid_3881_);
                    v___y_3868_ = v___x_3887_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3890_ = lean_array_fget_borrowed(v___y_3889_, v_hi_3866_);
                v___x_3891_ = lean_array_fget_borrowed(v___y_3889_, v_lo_3865_);
                v___x_3892_ = l_Lean_StructureFieldInfo_lt(v___x_3890_, v___x_3891_);
                if v___x_3892_ == 0 {
                    v___y_3883_ = v___y_3889_;
                    state = 2;
                    continue;
                } else {
                    v___x_3893_ = lean_array_fswap(v___y_3889_, v_lo_3865_, v_hi_3866_);
                    v___y_3883_ = v___x_3893_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(
    mut v_n_3898_: *mut crate::leanh::LeanObject,
    mut v_as_3899_: *mut crate::leanh::LeanObject,
    mut v_lo_3900_: *mut crate::leanh::LeanObject,
    mut v_hi_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_3898_, v_as_3899_, v_lo_3900_, v_hi_3901_);
    crate::leanh::lean_dec(v_hi_3901_);
    crate::leanh::lean_dec(v_n_3898_);
    return v_res_3902_;
}
pub unsafe fn l_Lean_registerStructure(
    mut v_env_3905_: *mut crate::leanh::LeanObject,
    mut v_e_3906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structName_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3910_: usize = 0;
    let mut v___x_3911_: usize = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structName_3907_ = crate::leanh::lean_ctor_get(v_e_3906_, 0);
                crate::leanh::lean_inc(v_structName_3907_);
                v_fields_3908_ = crate::leanh::lean_ctor_get(v_e_3906_, 1);
                crate::leanh::lean_inc_ref_n(v_fields_3908_, 2);
                crate::leanh::lean_dec_ref(v_e_3906_);
                v___x_3909_ = l___private_Lean_Structure_0__Lean_structureExt;
                v_sz_3910_ = lean_array_size(v_fields_3908_);
                v___x_3911_ = 0usize;
                v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_3910_, v___x_3911_, v_fields_3908_);
                v___x_3921_ = lean_array_get_size(v_fields_3908_);
                v___x_3926_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3927_ = lean_nat_dec_eq(v___x_3921_, v___x_3926_);
                if v___x_3927_ == 0 {
                    v___x_3928_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3929_ = lean_nat_sub(v___x_3921_, v___x_3928_);
                    v___x_3933_ = lean_nat_dec_le(v___x_3926_, v___x_3929_);
                    if v___x_3933_ == 0 {
                        crate::leanh::lean_inc(v___x_3929_);
                        v___y_3931_ = v___x_3929_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3931_ = v___x_3926_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_3914_ = v_fields_3908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEnvExtension_3915_ = crate::leanh::lean_ctor_get(v___x_3909_, 0);
                v_asyncMode_3916_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3915_, 2);
                v___x_3917_ = l_Lean_registerStructure___closed__0;
                v___x_3918_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3918_, 0, v_structName_3907_);
                crate::leanh::lean_ctor_set(v___x_3918_, 1, v___x_3912_);
                crate::leanh::lean_ctor_set(v___x_3918_, 2, v___y_3914_);
                crate::leanh::lean_ctor_set(v___x_3918_, 3, v___x_3917_);
                v___x_3919_ = crate::leanh::lean_box(0);
                v___x_3920_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3909_,
                    v_env_3905_,
                    v___x_3918_,
                    v_asyncMode_3916_,
                    v___x_3919_,
                );
                return v___x_3920_;
            }
            2 => {
                v___x_3925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_3921_, v_fields_3908_, v___y_3923_, v___y_3924_);
                crate::leanh::lean_dec(v___y_3924_);
                v___y_3914_ = v___x_3925_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3932_ = lean_nat_dec_le(v___y_3931_, v___x_3929_);
                if v___x_3932_ == 0 {
                    crate::leanh::lean_dec(v___x_3929_);
                    crate::leanh::lean_inc(v___y_3931_);
                    v___y_3923_ = v___y_3931_;
                    v___y_3924_ = v___y_3931_;
                    state = 2;
                    continue;
                } else {
                    v___y_3923_ = v___y_3931_;
                    v___y_3924_ = v___x_3929_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(
    mut v_n_3934_: *mut crate::leanh::LeanObject,
    mut v_as_3935_: *mut crate::leanh::LeanObject,
    mut v_lo_3936_: *mut crate::leanh::LeanObject,
    mut v_hi_3937_: *mut crate::leanh::LeanObject,
    mut v_w_3938_: *mut crate::leanh::LeanObject,
    mut v_hlo_3939_: *mut crate::leanh::LeanObject,
    mut v_hhi_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_3934_, v_as_3935_, v_lo_3936_, v_hi_3937_);
    return v___x_3941_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(
    mut v_n_3942_: *mut crate::leanh::LeanObject,
    mut v_as_3943_: *mut crate::leanh::LeanObject,
    mut v_lo_3944_: *mut crate::leanh::LeanObject,
    mut v_hi_3945_: *mut crate::leanh::LeanObject,
    mut v_w_3946_: *mut crate::leanh::LeanObject,
    mut v_hlo_3947_: *mut crate::leanh::LeanObject,
    mut v_hhi_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3949_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_3942_, v_as_3943_, v_lo_3944_, v_hi_3945_, v_w_3946_, v_hlo_3947_, v_hhi_3948_);
    crate::leanh::lean_dec(v_hi_3945_);
    crate::leanh::lean_dec(v_n_3942_);
    return v_res_3949_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(
    mut v_n_3950_: *mut crate::leanh::LeanObject,
    mut v_lo_3951_: *mut crate::leanh::LeanObject,
    mut v_hi_3952_: *mut crate::leanh::LeanObject,
    mut v_hhi_3953_: *mut crate::leanh::LeanObject,
    mut v_pivot_3954_: *mut crate::leanh::LeanObject,
    mut v_as_3955_: *mut crate::leanh::LeanObject,
    mut v_i_3956_: *mut crate::leanh::LeanObject,
    mut v_k_3957_: *mut crate::leanh::LeanObject,
    mut v_ilo_3958_: *mut crate::leanh::LeanObject,
    mut v_ik_3959_: *mut crate::leanh::LeanObject,
    mut v_w_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_3952_, v_pivot_3954_, v_as_3955_, v_i_3956_, v_k_3957_);
    return v___x_3961_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(
    mut v_n_3962_: *mut crate::leanh::LeanObject,
    mut v_lo_3963_: *mut crate::leanh::LeanObject,
    mut v_hi_3964_: *mut crate::leanh::LeanObject,
    mut v_hhi_3965_: *mut crate::leanh::LeanObject,
    mut v_pivot_3966_: *mut crate::leanh::LeanObject,
    mut v_as_3967_: *mut crate::leanh::LeanObject,
    mut v_i_3968_: *mut crate::leanh::LeanObject,
    mut v_k_3969_: *mut crate::leanh::LeanObject,
    mut v_ilo_3970_: *mut crate::leanh::LeanObject,
    mut v_ik_3971_: *mut crate::leanh::LeanObject,
    mut v_w_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_3962_, v_lo_3963_, v_hi_3964_, v_hhi_3965_, v_pivot_3966_, v_as_3967_, v_i_3968_, v_k_3969_, v_ilo_3970_, v_ik_3971_, v_w_3972_);
    crate::leanh::lean_dec_ref(v_pivot_3966_);
    crate::leanh::lean_dec(v_hi_3964_);
    crate::leanh::lean_dec(v_lo_3963_);
    crate::leanh::lean_dec(v_n_3962_);
    return v_res_3973_;
}
pub unsafe fn l_Lean_setStructureParents___redArg___lam__0(
    mut v_val_3974_: *mut crate::leanh::LeanObject,
    mut v_parentInfo_3975_: *mut crate::leanh::LeanObject,
    mut v___x_3976_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_3977_: *mut crate::leanh::LeanObject,
    mut v___x_3978_: *mut crate::leanh::LeanObject,
    mut v_env_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structName_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_unused_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structName_3980_ = crate::leanh::lean_ctor_get(v_val_3974_, 0);
                v_fieldNames_3981_ = crate::leanh::lean_ctor_get(v_val_3974_, 1);
                v_fieldInfo_3982_ = crate::leanh::lean_ctor_get(v_val_3974_, 2);
                v_isSharedCheck_3990_ = (!crate::leanh::lean_is_exclusive(v_val_3974_)) as u8;
                if v_isSharedCheck_3990_ == 0 {
                    v_unused_3991_ = crate::leanh::lean_ctor_get(v_val_3974_, 3);
                    crate::leanh::lean_dec(v_unused_3991_);
                    v___x_3984_ = v_val_3974_;
                    v_isShared_3985_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fieldInfo_3982_);
                    crate::leanh::lean_inc(v_fieldNames_3981_);
                    crate::leanh::lean_inc(v_structName_3980_);
                    crate::leanh::lean_dec(v_val_3974_);
                    v___x_3984_ = crate::leanh::lean_box(0);
                    v_isShared_3985_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_parentInfo_3975_);
                    v___x_3987_ = v___x_3984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_structName_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_fieldNames_3981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_fieldInfo_3982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_parentInfo_3975_);
                    v___x_3987_ = v_reuseFailAlloc_3989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3988_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3976_,
                    v_env_3979_,
                    v___x_3987_,
                    v_asyncMode_3977_,
                    v___x_3978_,
                );
                return v___x_3988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setStructureParents___redArg___lam__0___boxed(
    mut v_val_3992_: *mut crate::leanh::LeanObject,
    mut v_parentInfo_3993_: *mut crate::leanh::LeanObject,
    mut v___x_3994_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_3995_: *mut crate::leanh::LeanObject,
    mut v___x_3996_: *mut crate::leanh::LeanObject,
    mut v_env_3997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_setStructureParents___redArg___lam__0(
        v_val_3992_,
        v_parentInfo_3993_,
        v___x_3994_,
        v_asyncMode_3995_,
        v___x_3996_,
        v_env_3997_,
    );
    crate::leanh::lean_dec(v_asyncMode_3995_);
    return v_res_3998_;
}
pub unsafe fn _init_l_Lean_setStructureParents___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = l_Lean_setStructureParents___redArg___lam__1___closed__0;
    v___x_4001_ = l_Lean_stringToMessageData(v___x_4000_);
    return v___x_4001_;
}
pub unsafe fn _init_l_Lean_setStructureParents___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ = l_Lean_setStructureParents___redArg___lam__1___closed__2;
    v___x_4004_ = l_Lean_stringToMessageData(v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l_Lean_setStructureParents___redArg___lam__1(
    mut v___x_4005_: *mut crate::leanh::LeanObject,
    mut v___x_4006_: *mut crate::leanh::LeanObject,
    mut v___x_4007_: *mut crate::leanh::LeanObject,
    mut v_structName_4008_: *mut crate::leanh::LeanObject,
    mut v_parentInfo_4009_: *mut crate::leanh::LeanObject,
    mut v_modifyEnv_4010_: *mut crate::leanh::LeanObject,
    mut v_inst_4011_: *mut crate::leanh::LeanObject,
    mut v_inst_4012_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut v_unused_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4014_ = l___private_Lean_Structure_0__Lean_structureExt;
                v_toEnvExtension_4015_ = crate::leanh::lean_ctor_get(v___x_4014_, 0);
                v_asyncMode_4016_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4015_, 2);
                v___x_4017_ = crate::leanh::lean_box(0);
                v___x_4018_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_4005_,
                    v___x_4014_,
                    v_____do__lift_4013_,
                    v_asyncMode_4016_,
                    v___x_4017_,
                );
                v_snd_4019_ = crate::leanh::lean_ctor_get(v___x_4018_, 1);
                v_isSharedCheck_4035_ = (!crate::leanh::lean_is_exclusive(v___x_4018_)) as u8;
                if v_isSharedCheck_4035_ == 0 {
                    v_unused_4036_ = crate::leanh::lean_ctor_get(v___x_4018_, 0);
                    crate::leanh::lean_dec(v_unused_4036_);
                    v___x_4021_ = v___x_4018_;
                    v_isShared_4022_ = v_isSharedCheck_4035_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4019_);
                    crate::leanh::lean_dec(v___x_4018_);
                    v___x_4021_ = crate::leanh::lean_box(0);
                    v_isShared_4022_ = v_isSharedCheck_4035_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_structName_4008_);
                v___x_4023_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_4006_,
                    v___x_4007_,
                    v_snd_4019_,
                    v_structName_4008_,
                );
                crate::leanh::lean_dec(v_snd_4019_);
                if crate::leanh::lean_obj_tag(v___x_4023_) == 1 {
                    crate::leanh::lean_del_object(v___x_4021_);
                    crate::leanh::lean_dec_ref(v_inst_4012_);
                    crate::leanh::lean_dec_ref(v_inst_4011_);
                    crate::leanh::lean_dec(v_structName_4008_);
                    v_val_4024_ = crate::leanh::lean_ctor_get(v___x_4023_, 0);
                    crate::leanh::lean_inc(v_val_4024_);
                    crate::leanh::lean_dec_ref_known(v___x_4023_, 1);
                    crate::leanh::lean_inc(v_asyncMode_4016_);
                    v___f_4025_ = crate::leanh::lean_alloc_closure(
                        l_Lean_setStructureParents___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_4025_, 0, v_val_4024_);
                    crate::leanh::lean_closure_set(v___f_4025_, 1, v_parentInfo_4009_);
                    crate::leanh::lean_closure_set(v___f_4025_, 2, v___x_4014_);
                    crate::leanh::lean_closure_set(v___f_4025_, 3, v_asyncMode_4016_);
                    crate::leanh::lean_closure_set(v___f_4025_, 4, v___x_4017_);
                    v___x_4026_ = crate::leanh::lean_apply_1(v_modifyEnv_4010_, v___f_4025_);
                    return v___x_4026_;
                } else {
                    crate::leanh::lean_dec(v___x_4023_);
                    crate::leanh::lean_dec(v_modifyEnv_4010_);
                    crate::leanh::lean_dec_ref(v_parentInfo_4009_);
                    v___x_4027_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_setStructureParents___redArg___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_setStructureParents___redArg___lam__1___closed__1_once
                        ),
                        _init_l_Lean_setStructureParents___redArg___lam__1___closed__1,
                    );
                    v___x_4028_ = l_Lean_MessageData_ofName(v_structName_4008_);
                    if v_isShared_4022_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4021_, 7);
                        crate::leanh::lean_ctor_set(v___x_4021_, 1, v___x_4028_);
                        crate::leanh::lean_ctor_set(v___x_4021_, 0, v___x_4027_);
                        v___x_4030_ = v___x_4021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4034_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4028_);
                        v___x_4030_ = v_reuseFailAlloc_4034_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4031_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_setStructureParents___redArg___lam__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_setStructureParents___redArg___lam__1___closed__3_once
                    ),
                    _init_l_Lean_setStructureParents___redArg___lam__1___closed__3,
                );
                v___x_4032_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4030_);
                crate::leanh::lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                v___x_4033_ = l_Lean_throwError___redArg(v_inst_4011_, v_inst_4012_, v___x_4032_);
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_setStructureParents___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l_Lean_instInhabitedStructureState_default;
    v___x_4040_ = crate::leanh::lean_box(0);
    v___x_4041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4041_, 0, v___x_4040_);
    crate::leanh::lean_ctor_set(v___x_4041_, 1, v___x_4039_);
    return v___x_4041_;
}
pub unsafe fn l_Lean_setStructureParents___redArg(
    mut v_inst_4042_: *mut crate::leanh::LeanObject,
    mut v_inst_4043_: *mut crate::leanh::LeanObject,
    mut v_inst_4044_: *mut crate::leanh::LeanObject,
    mut v_structName_4045_: *mut crate::leanh::LeanObject,
    mut v_parentInfo_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4047_ = crate::leanh::lean_ctor_get(v_inst_4042_, 1);
    crate::leanh::lean_inc(v_toBind_4047_);
    v_getEnv_4048_ = crate::leanh::lean_ctor_get(v_inst_4043_, 0);
    crate::leanh::lean_inc(v_getEnv_4048_);
    v_modifyEnv_4049_ = crate::leanh::lean_ctor_get(v_inst_4043_, 1);
    crate::leanh::lean_inc(v_modifyEnv_4049_);
    crate::leanh::lean_dec_ref(v_inst_4043_);
    v___x_4050_ = l_Lean_setStructureParents___redArg___closed__0;
    v___x_4051_ = l_Lean_setStructureParents___redArg___closed__1;
    v___x_4052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_setStructureParents___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_setStructureParents___redArg___closed__2_once),
        _init_l_Lean_setStructureParents___redArg___closed__2,
    );
    v___f_4053_ = crate::leanh::lean_alloc_closure(
        l_Lean_setStructureParents___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_4053_, 0, v___x_4052_);
    crate::leanh::lean_closure_set(v___f_4053_, 1, v___x_4050_);
    crate::leanh::lean_closure_set(v___f_4053_, 2, v___x_4051_);
    crate::leanh::lean_closure_set(v___f_4053_, 3, v_structName_4045_);
    crate::leanh::lean_closure_set(v___f_4053_, 4, v_parentInfo_4046_);
    crate::leanh::lean_closure_set(v___f_4053_, 5, v_modifyEnv_4049_);
    crate::leanh::lean_closure_set(v___f_4053_, 6, v_inst_4042_);
    crate::leanh::lean_closure_set(v___f_4053_, 7, v_inst_4044_);
    v___x_4054_ = crate::leanh::lean_apply_4(
        v_toBind_4047_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_4048_,
        v___f_4053_,
    );
    return v___x_4054_;
}
pub unsafe fn l_Lean_setStructureParents(
    mut v_m_4055_: *mut crate::leanh::LeanObject,
    mut v_inst_4056_: *mut crate::leanh::LeanObject,
    mut v_inst_4057_: *mut crate::leanh::LeanObject,
    mut v_inst_4058_: *mut crate::leanh::LeanObject,
    mut v_structName_4059_: *mut crate::leanh::LeanObject,
    mut v_parentInfo_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = l_Lean_setStructureParents___redArg(
        v_inst_4056_,
        v_inst_4057_,
        v_inst_4058_,
        v_structName_4059_,
        v_parentInfo_4060_,
    );
    return v___x_4061_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(
    mut v_as_4062_: *mut crate::leanh::LeanObject,
    mut v_k_4063_: *mut crate::leanh::LeanObject,
    mut v_x_4064_: *mut crate::leanh::LeanObject,
    mut v_x_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4066_ = lean_nat_add(v_x_4064_, v_x_4065_);
                v___x_4067_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_4068_ = lean_nat_shiftr(v___x_4066_, v___x_4067_);
                crate::leanh::lean_dec(v___x_4066_);
                v_a_4069_ = lean_array_fget_borrowed(v_as_4062_, v_m_4068_);
                v___x_4070_ = l_Lean_StructureInfo_lt(v_a_4069_, v_k_4063_);
                if v___x_4070_ == 0 {
                    crate::leanh::lean_dec(v_x_4065_);
                    v___x_4071_ = l_Lean_StructureInfo_lt(v_k_4063_, v_a_4069_);
                    if v___x_4071_ == 0 {
                        crate::leanh::lean_dec(v_m_4068_);
                        crate::leanh::lean_dec(v_x_4064_);
                        crate::leanh::lean_inc(v_a_4069_);
                        v___x_4072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4072_, 0, v_a_4069_);
                        return v___x_4072_;
                    } else {
                        v___x_4073_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4074_ = lean_nat_dec_eq(v_m_4068_, v___x_4073_);
                        if v___x_4074_ == 0 {
                            v___x_4075_ = lean_nat_sub(v_m_4068_, v___x_4067_);
                            crate::leanh::lean_dec(v_m_4068_);
                            v___x_4076_ = lean_nat_dec_lt(v___x_4075_, v_x_4064_);
                            if v___x_4076_ == 0 {
                                v_x_4065_ = v___x_4075_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4075_);
                                crate::leanh::lean_dec(v_x_4064_);
                                v___x_4078_ = crate::leanh::lean_box(0);
                                return v___x_4078_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_4068_);
                            crate::leanh::lean_dec(v_x_4064_);
                            v___x_4079_ = crate::leanh::lean_box(0);
                            return v___x_4079_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4064_);
                    v___x_4080_ = lean_nat_add(v_m_4068_, v___x_4067_);
                    crate::leanh::lean_dec(v_m_4068_);
                    v___x_4081_ = lean_nat_dec_le(v___x_4080_, v_x_4065_);
                    if v___x_4081_ == 0 {
                        crate::leanh::lean_dec(v___x_4080_);
                        crate::leanh::lean_dec(v_x_4065_);
                        v___x_4082_ = crate::leanh::lean_box(0);
                        return v___x_4082_;
                    } else {
                        v_x_4064_ = v___x_4080_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(
    mut v_as_4084_: *mut crate::leanh::LeanObject,
    mut v_k_4085_: *mut crate::leanh::LeanObject,
    mut v_x_4086_: *mut crate::leanh::LeanObject,
    mut v_x_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(
        v_as_4084_, v_k_4085_, v_x_4086_, v_x_4087_,
    );
    crate::leanh::lean_dec_ref(v_k_4085_);
    crate::leanh::lean_dec_ref(v_as_4084_);
    return v_res_4088_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4089_: *mut crate::leanh::LeanObject,
    mut v_vals_4090_: *mut crate::leanh::LeanObject,
    mut v_i_4091_: *mut crate::leanh::LeanObject,
    mut v_k_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4093_ = lean_array_get_size(v_keys_4089_);
                v___x_4094_ = lean_nat_dec_lt(v_i_4091_, v___x_4093_);
                if v___x_4094_ == 0 {
                    crate::leanh::lean_dec(v_i_4091_);
                    v___x_4095_ = crate::leanh::lean_box(0);
                    return v___x_4095_;
                } else {
                    v_k_x27_4096_ = lean_array_fget_borrowed(v_keys_4089_, v_i_4091_);
                    v___x_4097_ = lean_name_eq(v_k_4092_, v_k_x27_4096_);
                    if v___x_4097_ == 0 {
                        v___x_4098_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4099_ = lean_nat_add(v_i_4091_, v___x_4098_);
                        crate::leanh::lean_dec(v_i_4091_);
                        v_i_4091_ = v___x_4099_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4101_ = lean_array_fget_borrowed(v_vals_4090_, v_i_4091_);
                        crate::leanh::lean_dec(v_i_4091_);
                        crate::leanh::lean_inc(v___x_4101_);
                        v___x_4102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4102_, 0, v___x_4101_);
                        return v___x_4102_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4103_: *mut crate::leanh::LeanObject,
    mut v_vals_4104_: *mut crate::leanh::LeanObject,
    mut v_i_4105_: *mut crate::leanh::LeanObject,
    mut v_k_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4103_, v_vals_4104_, v_i_4105_, v_k_4106_);
    crate::leanh::lean_dec(v_k_4106_);
    crate::leanh::lean_dec_ref(v_vals_4104_);
    crate::leanh::lean_dec_ref(v_keys_4103_);
    return v_res_4107_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(
    mut v_x_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: usize,
    mut v_x_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: usize = 0;
    let mut v___x_4114_: usize = 0;
    let mut v___x_4115_: usize = 0;
    let mut v_j_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: usize = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4108_) == 0 {
                    v_es_4111_ = crate::leanh::lean_ctor_get(v_x_4108_, 0);
                    v___x_4112_ = crate::leanh::lean_box(2);
                    v___x_4113_ = 5usize;
                    v___x_4114_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
                    v___x_4115_ = lean_usize_land(v_x_4109_, v___x_4114_);
                    v_j_4116_ = lean_usize_to_nat(v___x_4115_);
                    v___x_4117_ = lean_array_get_borrowed(v___x_4112_, v_es_4111_, v_j_4116_);
                    crate::leanh::lean_dec(v_j_4116_);
                    match crate::leanh::lean_obj_tag(v___x_4117_) {
                        0 => {
                            v_key_4118_ = crate::leanh::lean_ctor_get(v___x_4117_, 0);
                            v_val_4119_ = crate::leanh::lean_ctor_get(v___x_4117_, 1);
                            v___x_4120_ = lean_name_eq(v_x_4110_, v_key_4118_);
                            if v___x_4120_ == 0 {
                                v___x_4121_ = crate::leanh::lean_box(0);
                                return v___x_4121_;
                            } else {
                                crate::leanh::lean_inc(v_val_4119_);
                                v___x_4122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4122_, 0, v_val_4119_);
                                return v___x_4122_;
                            }
                        }
                        1 => {
                            v_node_4123_ = crate::leanh::lean_ctor_get(v___x_4117_, 0);
                            v___x_4124_ = lean_usize_shift_right(v_x_4109_, v___x_4113_);
                            v_x_4108_ = v_node_4123_;
                            v_x_4109_ = v___x_4124_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4126_ = crate::leanh::lean_box(0);
                            return v___x_4126_;
                        }
                    }
                } else {
                    v_ks_4127_ = crate::leanh::lean_ctor_get(v_x_4108_, 0);
                    v_vs_4128_ = crate::leanh::lean_ctor_get(v_x_4108_, 1);
                    v___x_4129_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4127_, v_vs_4128_, v___x_4129_, v_x_4110_);
                    return v___x_4130_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4131_: *mut crate::leanh::LeanObject,
    mut v_x_4132_: *mut crate::leanh::LeanObject,
    mut v_x_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_395__boxed_4134_: usize = 0;
    let mut v_res_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_395__boxed_4134_ = crate::leanh::lean_unbox_usize(v_x_4132_);
    crate::leanh::lean_dec(v_x_4132_);
    v_res_4135_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_4131_, v_x_395__boxed_4134_, v_x_4133_);
    crate::leanh::lean_dec(v_x_4133_);
    crate::leanh::lean_dec_ref(v_x_4131_);
    return v_res_4135_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(
    mut v_x_4136_: *mut crate::leanh::LeanObject,
    mut v_x_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4139_: u64 = 0;
    let mut v___x_4140_: usize = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: u64 = 0;
    let mut v_hash_4143_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4137_) == 0 {
                    v___x_4142_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
                    v___y_4139_ = v___x_4142_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4143_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4137_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4139_ = v_hash_4143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4140_ = lean_uint64_to_usize(v___y_4139_);
                v___x_4141_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_4136_, v___x_4140_, v_x_4137_);
                return v___x_4141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(
    mut v_x_4144_: *mut crate::leanh::LeanObject,
    mut v_x_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(
            v_x_4144_, v_x_4145_,
        );
    crate::leanh::lean_dec(v_x_4145_);
    crate::leanh::lean_dec_ref(v_x_4144_);
    return v_res_4146_;
}
pub unsafe fn l_Lean_getStructureInfo_x3f(
    mut v_env_4147_: *mut crate::leanh::LeanObject,
    mut v_structName_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_setStructureParents___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_setStructureParents___redArg___closed__2_once),
        _init_l_Lean_setStructureParents___redArg___closed__2,
    );
    v___x_4150_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4147_, v_structName_4148_);
    if crate::leanh::lean_obj_tag(v___x_4150_) == 0 {
        let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4151_ = l___private_Lean_Structure_0__Lean_structureExt;
        v_toEnvExtension_4152_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
        v_asyncMode_4153_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4152_, 2);
        v___x_4154_ = crate::leanh::lean_box(0);
        v___x_4155_ = l_Lean_PersistentEnvExtension_getState___redArg(
            v___x_4149_,
            v___x_4151_,
            v_env_4147_,
            v_asyncMode_4153_,
            v___x_4154_,
        );
        v_snd_4156_ = crate::leanh::lean_ctor_get(v___x_4155_, 1);
        crate::leanh::lean_inc(v_snd_4156_);
        crate::leanh::lean_dec(v___x_4155_);
        v___x_4157_ =
            l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(
                v_snd_4156_,
                v_structName_4148_,
            );
        crate::leanh::lean_dec(v_structName_4148_);
        crate::leanh::lean_dec(v_snd_4156_);
        return v___x_4157_;
    } else {
        let mut v_val_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4160_: u8 = 0;
        let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4164_: u8 = 0;
        v_val_4158_ = crate::leanh::lean_ctor_get(v___x_4150_, 0);
        crate::leanh::lean_inc(v_val_4158_);
        crate::leanh::lean_dec_ref_known(v___x_4150_, 1);
        v___x_4159_ = l___private_Lean_Structure_0__Lean_structureExt;
        v___x_4160_ = 0;
        v___x_4161_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
            v___x_4149_,
            v___x_4159_,
            v_env_4147_,
            v_val_4158_,
            v___x_4160_,
        );
        crate::leanh::lean_dec(v_val_4158_);
        crate::leanh::lean_dec_ref(v_env_4147_);
        v___x_4162_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4163_ = lean_array_get_size(v___x_4161_);
        v___x_4164_ = lean_nat_dec_lt(v___x_4162_, v___x_4163_);
        if v___x_4164_ == 0 {
            let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_4161_);
            crate::leanh::lean_dec(v_structName_4148_);
            v___x_4165_ = crate::leanh::lean_box(0);
            return v___x_4165_;
        } else {
            let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4168_: u8 = 0;
            v___x_4166_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4167_ = lean_nat_sub(v___x_4163_, v___x_4166_);
            v___x_4168_ = lean_nat_dec_le(v___x_4162_, v___x_4167_);
            if v___x_4168_ == 0 {
                let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4167_);
                crate::leanh::lean_dec_ref(v___x_4161_);
                crate::leanh::lean_dec(v_structName_4148_);
                v___x_4169_ = crate::leanh::lean_box(0);
                return v___x_4169_;
            } else {
                let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4170_ = l_Lean_instInhabitedStructureInfo_default___closed__0;
                v___x_4171_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4171_, 0, v_structName_4148_);
                crate::leanh::lean_ctor_set(v___x_4171_, 1, v___x_4170_);
                crate::leanh::lean_ctor_set(v___x_4171_, 2, v___x_4170_);
                crate::leanh::lean_ctor_set(v___x_4171_, 3, v___x_4170_);
                v___x_4172_ =
                    l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(
                        v___x_4161_,
                        v___x_4171_,
                        v___x_4162_,
                        v___x_4167_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_4171_, 4);
                crate::leanh::lean_dec_ref(v___x_4161_);
                return v___x_4172_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(
    mut v_00_u03b2_4173_: *mut crate::leanh::LeanObject,
    mut v_x_4174_: *mut crate::leanh::LeanObject,
    mut v_x_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(
            v_x_4174_, v_x_4175_,
        );
    return v___x_4176_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(
    mut v_00_u03b2_4177_: *mut crate::leanh::LeanObject,
    mut v_x_4178_: *mut crate::leanh::LeanObject,
    mut v_x_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(
        v_00_u03b2_4177_,
        v_x_4178_,
        v_x_4179_,
    );
    crate::leanh::lean_dec(v_x_4179_);
    crate::leanh::lean_dec_ref(v_x_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(
    mut v_as_4181_: *mut crate::leanh::LeanObject,
    mut v_k_4182_: *mut crate::leanh::LeanObject,
    mut v_x_4183_: *mut crate::leanh::LeanObject,
    mut v_x_4184_: *mut crate::leanh::LeanObject,
    mut v_x_4185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(
        v_as_4181_, v_k_4182_, v_x_4183_, v_x_4184_,
    );
    return v___x_4186_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(
    mut v_as_4187_: *mut crate::leanh::LeanObject,
    mut v_k_4188_: *mut crate::leanh::LeanObject,
    mut v_x_4189_: *mut crate::leanh::LeanObject,
    mut v_x_4190_: *mut crate::leanh::LeanObject,
    mut v_x_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(
        v_as_4187_, v_k_4188_, v_x_4189_, v_x_4190_, v_x_4191_,
    );
    crate::leanh::lean_dec_ref(v_k_4188_);
    crate::leanh::lean_dec_ref(v_as_4187_);
    return v_res_4192_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(
    mut v_00_u03b2_4193_: *mut crate::leanh::LeanObject,
    mut v_x_4194_: *mut crate::leanh::LeanObject,
    mut v_x_4195_: usize,
    mut v_x_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_4194_, v_x_4195_, v_x_4196_);
    return v___x_4197_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4198_: *mut crate::leanh::LeanObject,
    mut v_x_4199_: *mut crate::leanh::LeanObject,
    mut v_x_4200_: *mut crate::leanh::LeanObject,
    mut v_x_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_531__boxed_4202_: usize = 0;
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_531__boxed_4202_ = crate::leanh::lean_unbox_usize(v_x_4200_);
    crate::leanh::lean_dec(v_x_4200_);
    v_res_4203_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_4198_, v_x_4199_, v_x_531__boxed_4202_, v_x_4201_);
    crate::leanh::lean_dec(v_x_4201_);
    crate::leanh::lean_dec_ref(v_x_4199_);
    return v_res_4203_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4204_: *mut crate::leanh::LeanObject,
    mut v_keys_4205_: *mut crate::leanh::LeanObject,
    mut v_vals_4206_: *mut crate::leanh::LeanObject,
    mut v_heq_4207_: *mut crate::leanh::LeanObject,
    mut v_i_4208_: *mut crate::leanh::LeanObject,
    mut v_k_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4205_, v_vals_4206_, v_i_4208_, v_k_4209_);
    return v___x_4210_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4211_: *mut crate::leanh::LeanObject,
    mut v_keys_4212_: *mut crate::leanh::LeanObject,
    mut v_vals_4213_: *mut crate::leanh::LeanObject,
    mut v_heq_4214_: *mut crate::leanh::LeanObject,
    mut v_i_4215_: *mut crate::leanh::LeanObject,
    mut v_k_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4217_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4211_, v_keys_4212_, v_vals_4213_, v_heq_4214_, v_i_4215_, v_k_4216_);
    crate::leanh::lean_dec(v_k_4216_);
    crate::leanh::lean_dec_ref(v_vals_4213_);
    crate::leanh::lean_dec_ref(v_keys_4212_);
    return v_res_4217_;
}
pub unsafe fn l_panic___at___00Lean_getStructureInfo_spec__0(
    mut v_msg_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4219_ = l_Lean_instInhabitedStructureInfo_default;
    v___x_4220_ = lean_panic_fn_borrowed(v___x_4219_, v_msg_4218_);
    return v___x_4220_;
}
pub unsafe fn _init_l_Lean_getStructureInfo___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4224_ = l_Lean_getStructureInfo___closed__2;
    v___x_4225_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_4226_ = crate::leanh::lean_unsigned_to_nat(139);
    v___x_4227_ = l_Lean_getStructureInfo___closed__1;
    v___x_4228_ = l_Lean_getStructureInfo___closed__0;
    v___x_4229_ = l_mkPanicMessageWithDecl(
        v___x_4228_,
        v___x_4227_,
        v___x_4226_,
        v___x_4225_,
        v___x_4224_,
    );
    return v___x_4229_;
}
pub unsafe fn l_Lean_getStructureInfo(
    mut v_env_4230_: *mut crate::leanh::LeanObject,
    mut v_structName_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4232_ = l_Lean_getStructureInfo_x3f(v_env_4230_, v_structName_4231_);
    if crate::leanh::lean_obj_tag(v___x_4232_) == 1 {
        let mut v_val_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4233_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
        crate::leanh::lean_inc(v_val_4233_);
        crate::leanh::lean_dec_ref_known(v___x_4232_, 1);
        return v_val_4233_;
    } else {
        let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4232_);
        v___x_4234_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getStructureInfo___closed__3),
            core::ptr::addr_of_mut!(l_Lean_getStructureInfo___closed__3_once),
            _init_l_Lean_getStructureInfo___closed__3,
        );
        v___x_4235_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_4234_);
        return v___x_4235_;
    }
}
pub unsafe fn l_panic___at___00Lean_getStructureCtor_spec__0(
    mut v_msg_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4237_ = l_Lean_instInhabitedConstructorVal_default;
    v___x_4238_ = lean_panic_fn_borrowed(v___x_4237_, v_msg_4236_);
    return v___x_4238_;
}
pub unsafe fn _init_l_Lean_getStructureCtor___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4240_ = l_Lean_getStructureInfo___closed__2;
    v___x_4241_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_4242_ = crate::leanh::lean_unsigned_to_nat(154);
    v___x_4243_ = l_Lean_getStructureCtor___closed__0;
    v___x_4244_ = l_Lean_getStructureInfo___closed__0;
    v___x_4245_ = l_mkPanicMessageWithDecl(
        v___x_4244_,
        v___x_4243_,
        v___x_4242_,
        v___x_4241_,
        v___x_4240_,
    );
    return v___x_4245_;
}
pub unsafe fn _init_l_Lean_getStructureCtor___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_getStructureCtor___closed__2;
    v___x_4248_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_4249_ = crate::leanh::lean_unsigned_to_nat(153);
    v___x_4250_ = l_Lean_getStructureCtor___closed__0;
    v___x_4251_ = l_Lean_getStructureInfo___closed__0;
    v___x_4252_ = l_mkPanicMessageWithDecl(
        v___x_4251_,
        v___x_4250_,
        v___x_4249_,
        v___x_4248_,
        v___x_4247_,
    );
    return v___x_4252_;
}
pub unsafe fn l_Lean_getStructureCtor(
    mut v_env_4253_: *mut crate::leanh::LeanObject,
    mut v_constName_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: u8 = 0;
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4261_ = 0;
                crate::leanh::lean_inc_ref(v_env_4253_);
                v___x_4262_ =
                    l_Lean_Environment_find_x3f(v_env_4253_, v_constName_4254_, v___x_4261_);
                if crate::leanh::lean_obj_tag(v___x_4262_) == 1 {
                    v_val_4263_ = crate::leanh::lean_ctor_get(v___x_4262_, 0);
                    crate::leanh::lean_inc(v_val_4263_);
                    crate::leanh::lean_dec_ref_known(v___x_4262_, 1);
                    if crate::leanh::lean_obj_tag(v_val_4263_) == 5 {
                        v_val_4264_ = crate::leanh::lean_ctor_get(v_val_4263_, 0);
                        crate::leanh::lean_inc_ref(v_val_4264_);
                        crate::leanh::lean_dec_ref_known(v_val_4263_, 1);
                        v_ctors_4265_ = crate::leanh::lean_ctor_get(v_val_4264_, 4);
                        crate::leanh::lean_inc(v_ctors_4265_);
                        crate::leanh::lean_dec_ref(v_val_4264_);
                        if crate::leanh::lean_obj_tag(v_ctors_4265_) == 1 {
                            v_tail_4266_ = crate::leanh::lean_ctor_get(v_ctors_4265_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_4266_) == 0 {
                                v_head_4267_ = crate::leanh::lean_ctor_get(v_ctors_4265_, 0);
                                crate::leanh::lean_inc(v_head_4267_);
                                crate::leanh::lean_dec_ref_known(v_ctors_4265_, 2);
                                v___x_4268_ = l_Lean_Environment_find_x3f(
                                    v_env_4253_,
                                    v_head_4267_,
                                    v___x_4261_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4268_) == 1 {
                                    v_val_4269_ = crate::leanh::lean_ctor_get(v___x_4268_, 0);
                                    crate::leanh::lean_inc(v_val_4269_);
                                    crate::leanh::lean_dec_ref_known(v___x_4268_, 1);
                                    if crate::leanh::lean_obj_tag(v_val_4269_) == 6 {
                                        v_val_4270_ = crate::leanh::lean_ctor_get(v_val_4269_, 0);
                                        crate::leanh::lean_inc_ref(v_val_4270_);
                                        crate::leanh::lean_dec_ref_known(v_val_4269_, 1);
                                        return v_val_4270_;
                                    } else {
                                        crate::leanh::lean_dec(v_val_4269_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_4268_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_ctors_4265_, 2);
                                crate::leanh::lean_dec_ref(v_env_4253_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_ctors_4265_);
                            crate::leanh::lean_dec_ref(v_env_4253_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4263_);
                        crate::leanh::lean_dec_ref(v_env_4253_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4262_);
                    crate::leanh::lean_dec_ref(v_env_4253_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4256_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_getStructureCtor___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_getStructureCtor___closed__1_once),
                    _init_l_Lean_getStructureCtor___closed__1,
                );
                v___x_4257_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_4256_);
                return v___x_4257_;
            }
            2 => {
                v___x_4259_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_getStructureCtor___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_getStructureCtor___closed__3_once),
                    _init_l_Lean_getStructureCtor___closed__3,
                );
                v___x_4260_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_4259_);
                return v___x_4260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getStructureFields(
    mut v_env_4271_: *mut crate::leanh::LeanObject,
    mut v_structName_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4273_ = l_Lean_getStructureInfo(v_env_4271_, v_structName_4272_);
    v_fieldNames_4274_ = crate::leanh::lean_ctor_get(v___x_4273_, 1);
    crate::leanh::lean_inc_ref(v_fieldNames_4274_);
    crate::leanh::lean_dec_ref(v___x_4273_);
    return v_fieldNames_4274_;
}
pub unsafe fn l_Lean_getFieldInfo_x3f(
    mut v_env_4275_: *mut crate::leanh::LeanObject,
    mut v_structName_4276_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_getStructureInfo_x3f(v_env_4275_, v_structName_4276_);
    if crate::leanh::lean_obj_tag(v___x_4278_) == 1 {
        let mut v_val_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fieldInfo_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4283_: u8 = 0;
        v_val_4279_ = crate::leanh::lean_ctor_get(v___x_4278_, 0);
        crate::leanh::lean_inc(v_val_4279_);
        crate::leanh::lean_dec_ref_known(v___x_4278_, 1);
        v_fieldInfo_4280_ = crate::leanh::lean_ctor_get(v_val_4279_, 2);
        crate::leanh::lean_inc_ref(v_fieldInfo_4280_);
        crate::leanh::lean_dec(v_val_4279_);
        v___x_4281_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4282_ = lean_array_get_size(v_fieldInfo_4280_);
        v___x_4283_ = lean_nat_dec_lt(v___x_4281_, v___x_4282_);
        if v___x_4283_ == 0 {
            let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_fieldInfo_4280_);
            crate::leanh::lean_dec(v_fieldName_4277_);
            v___x_4284_ = crate::leanh::lean_box(0);
            return v___x_4284_;
        } else {
            let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4287_: u8 = 0;
            v___x_4285_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4286_ = lean_nat_sub(v___x_4282_, v___x_4285_);
            v___x_4287_ = lean_nat_dec_le(v___x_4281_, v___x_4286_);
            if v___x_4287_ == 0 {
                let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4286_);
                crate::leanh::lean_dec_ref(v_fieldInfo_4280_);
                crate::leanh::lean_dec(v_fieldName_4277_);
                v___x_4288_ = crate::leanh::lean_box(0);
                return v___x_4288_;
            } else {
                let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4291_: u8 = 0;
                let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4289_ = crate::leanh::lean_box(0);
                v___x_4290_ = crate::leanh::lean_box(0);
                v___x_4291_ = 0;
                v___x_4292_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4292_, 0, v_fieldName_4277_);
                crate::leanh::lean_ctor_set(v___x_4292_, 1, v___x_4289_);
                crate::leanh::lean_ctor_set(v___x_4292_, 2, v___x_4290_);
                crate::leanh::lean_ctor_set(v___x_4292_, 3, v___x_4290_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4292_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_4291_,
                );
                v___x_4293_ =
                    l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(
                        v_fieldInfo_4280_,
                        v___x_4292_,
                        v___x_4281_,
                        v___x_4286_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_4292_, 4);
                crate::leanh::lean_dec_ref(v_fieldInfo_4280_);
                return v___x_4293_;
            }
        }
    } else {
        let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4278_);
        crate::leanh::lean_dec(v_fieldName_4277_);
        v___x_4294_ = crate::leanh::lean_box(0);
        return v___x_4294_;
    }
}
pub unsafe fn l_Lean_isSubobjectField_x3f(
    mut v_env_4295_: *mut crate::leanh::LeanObject,
    mut v_structName_4296_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4298_ = l_Lean_getFieldInfo_x3f(v_env_4295_, v_structName_4296_, v_fieldName_4297_);
    if crate::leanh::lean_obj_tag(v___x_4298_) == 1 {
        let mut v_val_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subobject_x3f_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4299_ = crate::leanh::lean_ctor_get(v___x_4298_, 0);
        crate::leanh::lean_inc(v_val_4299_);
        crate::leanh::lean_dec_ref_known(v___x_4298_, 1);
        v_subobject_x3f_4300_ = crate::leanh::lean_ctor_get(v_val_4299_, 2);
        crate::leanh::lean_inc(v_subobject_x3f_4300_);
        crate::leanh::lean_dec(v_val_4299_);
        return v_subobject_x3f_4300_;
    } else {
        let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4298_);
        v___x_4301_ = crate::leanh::lean_box(0);
        return v___x_4301_;
    }
}
pub unsafe fn l_Lean_getStructureParentInfo(
    mut v_env_4302_: *mut crate::leanh::LeanObject,
    mut v_structName_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parentInfo_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4304_ = l_Lean_getStructureInfo(v_env_4302_, v_structName_4303_);
    v_parentInfo_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 3);
    crate::leanh::lean_inc_ref(v_parentInfo_4305_);
    crate::leanh::lean_dec_ref(v___x_4304_);
    return v_parentInfo_4305_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(
    mut v_env_4306_: *mut crate::leanh::LeanObject,
    mut v_structName_4307_: *mut crate::leanh::LeanObject,
    mut v_as_4308_: *mut crate::leanh::LeanObject,
    mut v_i_4309_: usize,
    mut v_stop_4310_: usize,
    mut v_b_4311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: usize = 0;
    let mut v___x_4315_: usize = 0;
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4317_ = lean_usize_dec_eq(v_i_4309_, v_stop_4310_);
                if v___x_4317_ == 0 {
                    v___x_4318_ = lean_array_uget_borrowed(v_as_4308_, v_i_4309_);
                    crate::leanh::lean_inc(v___x_4318_);
                    crate::leanh::lean_inc(v_structName_4307_);
                    crate::leanh::lean_inc_ref(v_env_4306_);
                    v___x_4319_ =
                        l_Lean_isSubobjectField_x3f(v_env_4306_, v_structName_4307_, v___x_4318_);
                    if crate::leanh::lean_obj_tag(v___x_4319_) == 0 {
                        v___y_4313_ = v_b_4311_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4320_ = crate::leanh::lean_ctor_get(v___x_4319_, 0);
                        crate::leanh::lean_inc(v_val_4320_);
                        crate::leanh::lean_dec_ref_known(v___x_4319_, 1);
                        v___x_4321_ = lean_array_push(v_b_4311_, v_val_4320_);
                        v___y_4313_ = v___x_4321_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_structName_4307_);
                    crate::leanh::lean_dec_ref(v_env_4306_);
                    return v_b_4311_;
                }
            }
            1 => {
                v___x_4314_ = 1usize;
                v___x_4315_ = lean_usize_add(v_i_4309_, v___x_4314_);
                v_i_4309_ = v___x_4315_;
                v_b_4311_ = v___y_4313_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(
    mut v_env_4322_: *mut crate::leanh::LeanObject,
    mut v_structName_4323_: *mut crate::leanh::LeanObject,
    mut v_as_4324_: *mut crate::leanh::LeanObject,
    mut v_i_4325_: *mut crate::leanh::LeanObject,
    mut v_stop_4326_: *mut crate::leanh::LeanObject,
    mut v_b_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4328_: usize = 0;
    let mut v_stop_boxed_4329_: usize = 0;
    let mut v_res_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4328_ = crate::leanh::lean_unbox_usize(v_i_4325_);
    crate::leanh::lean_dec(v_i_4325_);
    v_stop_boxed_4329_ = crate::leanh::lean_unbox_usize(v_stop_4326_);
    crate::leanh::lean_dec(v_stop_4326_);
    v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_4322_, v_structName_4323_, v_as_4324_, v_i_boxed_4328_, v_stop_boxed_4329_, v_b_4327_);
    crate::leanh::lean_dec_ref(v_as_4324_);
    return v_res_4330_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(
    mut v_env_4331_: *mut crate::leanh::LeanObject,
    mut v_structName_4332_: *mut crate::leanh::LeanObject,
    mut v_as_4333_: *mut crate::leanh::LeanObject,
    mut v_start_4334_: *mut crate::leanh::LeanObject,
    mut v_stop_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    v___x_4336_ = l_Lean_instInhabitedStructureInfo_default___closed__0;
    v___x_4337_ = lean_nat_dec_lt(v_start_4334_, v_stop_4335_);
    if v___x_4337_ == 0 {
        crate::leanh::lean_dec(v_structName_4332_);
        crate::leanh::lean_dec_ref(v_env_4331_);
        return v___x_4336_;
    } else {
        let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4339_: u8 = 0;
        v___x_4338_ = lean_array_get_size(v_as_4333_);
        v___x_4339_ = lean_nat_dec_le(v_stop_4335_, v___x_4338_);
        if v___x_4339_ == 0 {
            let mut v___x_4340_: u8 = 0;
            v___x_4340_ = lean_nat_dec_lt(v_start_4334_, v___x_4338_);
            if v___x_4340_ == 0 {
                crate::leanh::lean_dec(v_structName_4332_);
                crate::leanh::lean_dec_ref(v_env_4331_);
                return v___x_4336_;
            } else {
                let mut v___x_4341_: usize = 0;
                let mut v___x_4342_: usize = 0;
                let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4341_ = lean_usize_of_nat(v_start_4334_);
                v___x_4342_ = lean_usize_of_nat(v___x_4338_);
                v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_4331_, v_structName_4332_, v_as_4333_, v___x_4341_, v___x_4342_, v___x_4336_);
                return v___x_4343_;
            }
        } else {
            let mut v___x_4344_: usize = 0;
            let mut v___x_4345_: usize = 0;
            let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4344_ = lean_usize_of_nat(v_start_4334_);
            v___x_4345_ = lean_usize_of_nat(v_stop_4335_);
            v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_4331_, v_structName_4332_, v_as_4333_, v___x_4344_, v___x_4345_, v___x_4336_);
            return v___x_4346_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(
    mut v_env_4347_: *mut crate::leanh::LeanObject,
    mut v_structName_4348_: *mut crate::leanh::LeanObject,
    mut v_as_4349_: *mut crate::leanh::LeanObject,
    mut v_start_4350_: *mut crate::leanh::LeanObject,
    mut v_stop_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(
        v_env_4347_,
        v_structName_4348_,
        v_as_4349_,
        v_start_4350_,
        v_stop_4351_,
    );
    crate::leanh::lean_dec(v_stop_4351_);
    crate::leanh::lean_dec(v_start_4350_);
    crate::leanh::lean_dec_ref(v_as_4349_);
    return v_res_4352_;
}
pub unsafe fn l_Lean_getStructureSubobjects(
    mut v_env_4353_: *mut crate::leanh::LeanObject,
    mut v_structName_4354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_structName_4354_);
    crate::leanh::lean_inc_ref(v_env_4353_);
    v___x_4355_ = l_Lean_getStructureFields(v_env_4353_, v_structName_4354_);
    v___x_4356_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4357_ = lean_array_get_size(v___x_4355_);
    v___x_4358_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(
        v_env_4353_,
        v_structName_4354_,
        v___x_4355_,
        v___x_4356_,
        v___x_4357_,
    );
    crate::leanh::lean_dec_ref(v___x_4355_);
    return v___x_4358_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_as_4360_: *mut crate::leanh::LeanObject,
    mut v_i_4361_: usize,
    mut v_stop_4362_: usize,
) -> u8 {
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v___x_4366_: usize = 0;
    let mut v___x_4367_: usize = 0;
    let mut v___x_4369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4363_ = lean_usize_dec_eq(v_i_4361_, v_stop_4362_);
                if v___x_4363_ == 0 {
                    v___x_4364_ = lean_array_uget_borrowed(v_as_4360_, v_i_4361_);
                    v___x_4365_ = lean_name_eq(v_a_4359_, v___x_4364_);
                    if v___x_4365_ == 0 {
                        v___x_4366_ = 1usize;
                        v___x_4367_ = lean_usize_add(v_i_4361_, v___x_4366_);
                        v_i_4361_ = v___x_4367_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4365_;
                    }
                } else {
                    v___x_4369_ = 0;
                    return v___x_4369_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_as_4371_: *mut crate::leanh::LeanObject,
    mut v_i_4372_: *mut crate::leanh::LeanObject,
    mut v_stop_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4374_: usize = 0;
    let mut v_stop_boxed_4375_: usize = 0;
    let mut v_res_4376_: u8 = 0;
    let mut v_r_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4374_ = crate::leanh::lean_unbox_usize(v_i_4372_);
    crate::leanh::lean_dec(v_i_4372_);
    v_stop_boxed_4375_ = crate::leanh::lean_unbox_usize(v_stop_4373_);
    crate::leanh::lean_dec(v_stop_4373_);
    v_res_4376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_4370_, v_as_4371_, v_i_boxed_4374_, v_stop_boxed_4375_);
    crate::leanh::lean_dec_ref(v_as_4371_);
    crate::leanh::lean_dec(v_a_4370_);
    v_r_4377_ = crate::leanh::lean_box((v_res_4376_) as usize);
    return v_r_4377_;
}
pub unsafe fn l_Array_contains___at___00Lean_findField_x3f_spec__0(
    mut v_as_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    v___x_4380_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4381_ = lean_array_get_size(v_as_4378_);
    v___x_4382_ = lean_nat_dec_lt(v___x_4380_, v___x_4381_);
    if v___x_4382_ == 0 {
        return v___x_4382_;
    } else {
        if v___x_4382_ == 0 {
            return v___x_4382_;
        } else {
            let mut v___x_4383_: usize = 0;
            let mut v___x_4384_: usize = 0;
            let mut v___x_4385_: u8 = 0;
            v___x_4383_ = 0usize;
            v___x_4384_ = lean_usize_of_nat(v___x_4381_);
            v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_4379_, v_as_4378_, v___x_4383_, v___x_4384_);
            return v___x_4385_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(
    mut v_as_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4388_: u8 = 0;
    let mut v_r_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4388_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_4386_, v_a_4387_);
    crate::leanh::lean_dec(v_a_4387_);
    crate::leanh::lean_dec_ref(v_as_4386_);
    v_r_4389_ = crate::leanh::lean_box((v_res_4388_) as usize);
    return v_r_4389_;
}
pub unsafe fn l_Lean_findField_x3f(
    mut v_env_4393_: *mut crate::leanh::LeanObject,
    mut v_structName_4394_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    crate::leanh::lean_inc(v_structName_4394_);
    crate::leanh::lean_inc_ref(v_env_4393_);
    v___x_4396_ = l_Lean_getStructureFields(v_env_4393_, v_structName_4394_);
    v___x_4397_ =
        l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_4396_, v_fieldName_4395_);
    crate::leanh::lean_dec_ref(v___x_4396_);
    if v___x_4397_ == 0 {
        let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4401_: usize = 0;
        let mut v___x_4402_: usize = 0;
        let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_env_4393_);
        v___x_4398_ = l_Lean_getStructureSubobjects(v_env_4393_, v_structName_4394_);
        v___x_4399_ = crate::leanh::lean_box(0);
        v___x_4400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0;
        v_sz_4401_ = lean_array_size(v___x_4398_);
        v___x_4402_ = 0usize;
        v___x_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_4393_, v_fieldName_4395_, v___x_4398_, v_sz_4401_, v___x_4402_, v___x_4400_);
        crate::leanh::lean_dec_ref(v___x_4398_);
        v_fst_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
        crate::leanh::lean_inc(v_fst_4404_);
        crate::leanh::lean_dec_ref(v___x_4403_);
        if crate::leanh::lean_obj_tag(v_fst_4404_) == 0 {
            return v___x_4399_;
        } else {
            let mut v_val_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_4405_ = crate::leanh::lean_ctor_get(v_fst_4404_, 0);
            crate::leanh::lean_inc(v_val_4405_);
            crate::leanh::lean_dec_ref_known(v_fst_4404_, 1);
            return v_val_4405_;
        }
    } else {
        let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_4393_);
        v___x_4406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4406_, 0, v_structName_4394_);
        return v___x_4406_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(
    mut v_env_4407_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4408_: *mut crate::leanh::LeanObject,
    mut v_as_4409_: *mut crate::leanh::LeanObject,
    mut v_sz_4410_: usize,
    mut v_i_4411_: usize,
    mut v_b_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4413_: u8 = 0;
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: usize = 0;
    let mut v___x_4421_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4413_ = lean_usize_dec_lt(v_i_4411_, v_sz_4410_);
                if v___x_4413_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_4407_);
                    crate::leanh::lean_inc_ref(v_b_4412_);
                    return v_b_4412_;
                } else {
                    v___x_4414_ = crate::leanh::lean_box(0);
                    v_a_4415_ = lean_array_uget_borrowed(v_as_4409_, v_i_4411_);
                    crate::leanh::lean_inc(v_a_4415_);
                    crate::leanh::lean_inc_ref(v_env_4407_);
                    v___x_4416_ = l_Lean_findField_x3f(v_env_4407_, v_a_4415_, v_fieldName_4408_);
                    if crate::leanh::lean_obj_tag(v___x_4416_) == 1 {
                        crate::leanh::lean_dec_ref(v_env_4407_);
                        v___x_4417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4417_, 0, v___x_4416_);
                        v___x_4418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4417_);
                        crate::leanh::lean_ctor_set(v___x_4418_, 1, v___x_4414_);
                        return v___x_4418_;
                    } else {
                        crate::leanh::lean_dec(v___x_4416_);
                        v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0;
                        v___x_4420_ = 1usize;
                        v___x_4421_ = lean_usize_add(v_i_4411_, v___x_4420_);
                        v_i_4411_ = v___x_4421_;
                        v_b_4412_ = v___x_4419_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(
    mut v_env_4423_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4424_: *mut crate::leanh::LeanObject,
    mut v_as_4425_: *mut crate::leanh::LeanObject,
    mut v_sz_4426_: *mut crate::leanh::LeanObject,
    mut v_i_4427_: *mut crate::leanh::LeanObject,
    mut v_b_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4429_: usize = 0;
    let mut v_i_boxed_4430_: usize = 0;
    let mut v_res_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4429_ = crate::leanh::lean_unbox_usize(v_sz_4426_);
    crate::leanh::lean_dec(v_sz_4426_);
    v_i_boxed_4430_ = crate::leanh::lean_unbox_usize(v_i_4427_);
    crate::leanh::lean_dec(v_i_4427_);
    v_res_4431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_4423_, v_fieldName_4424_, v_as_4425_, v_sz_boxed_4429_, v_i_boxed_4430_, v_b_4428_);
    crate::leanh::lean_dec_ref(v_b_4428_);
    crate::leanh::lean_dec_ref(v_as_4425_);
    crate::leanh::lean_dec(v_fieldName_4424_);
    return v_res_4431_;
}
pub unsafe fn l_Lean_findField_x3f___boxed(
    mut v_env_4432_: *mut crate::leanh::LeanObject,
    mut v_structName_4433_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_Lean_findField_x3f(v_env_4432_, v_structName_4433_, v_fieldName_4434_);
    crate::leanh::lean_dec(v_fieldName_4434_);
    return v_res_4435_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(
    mut v_projName_4439_: *mut crate::leanh::LeanObject,
    mut v_as_4440_: *mut crate::leanh::LeanObject,
    mut v_sz_4441_: usize,
    mut v_i_4442_: usize,
    mut v_b_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: u8 = 0;
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: usize = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4444_ = lean_usize_dec_lt(v_i_4442_, v_sz_4441_);
                if v___x_4444_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_4443_);
                    return v_b_4443_;
                } else {
                    v_a_4445_ = lean_array_uget_borrowed(v_as_4440_, v_i_4442_);
                    v_projFn_4446_ = crate::leanh::lean_ctor_get(v_a_4445_, 1);
                    v___x_4447_ = crate::leanh::lean_box(0);
                    v___x_4448_ = l_Lean_Name_isSuffixOf(v_projName_4439_, v_projFn_4446_);
                    if v___x_4448_ == 0 {
                        v___x_4449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0;
                        v___x_4450_ = 1usize;
                        v___x_4451_ = lean_usize_add(v_i_4442_, v___x_4450_);
                        v_i_4442_ = v___x_4451_;
                        v_b_4443_ = v___x_4449_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4445_);
                        v___x_4453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4453_, 0, v_a_4445_);
                        v___x_4454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
                        v___x_4455_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4455_, 0, v___x_4454_);
                        crate::leanh::lean_ctor_set(v___x_4455_, 1, v___x_4447_);
                        return v___x_4455_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(
    mut v_projName_4456_: *mut crate::leanh::LeanObject,
    mut v_as_4457_: *mut crate::leanh::LeanObject,
    mut v_sz_4458_: *mut crate::leanh::LeanObject,
    mut v_i_4459_: *mut crate::leanh::LeanObject,
    mut v_b_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4461_: usize = 0;
    let mut v_i_boxed_4462_: usize = 0;
    let mut v_res_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4461_ = crate::leanh::lean_unbox_usize(v_sz_4458_);
    crate::leanh::lean_dec(v_sz_4458_);
    v_i_boxed_4462_ = crate::leanh::lean_unbox_usize(v_i_4459_);
    crate::leanh::lean_dec(v_i_4459_);
    v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_4456_, v_as_4457_, v_sz_boxed_4461_, v_i_boxed_4462_, v_b_4460_);
    crate::leanh::lean_dec_ref(v_b_4460_);
    crate::leanh::lean_dec_ref(v_as_4457_);
    crate::leanh::lean_dec(v_projName_4456_);
    return v_res_4463_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(
    mut v_env_4464_: *mut crate::leanh::LeanObject,
    mut v_projName_4465_: *mut crate::leanh::LeanObject,
    mut v_structName_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4474_: usize = 0;
    let mut v___x_4475_: usize = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v_snd_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v_unused_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4494_: usize = 0;
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v_val_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v_structName_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_unused_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4468_ = l_Lean_NameSet_contains(v_a_4467_, v_structName_4466_);
                if v___x_4468_ == 0 {
                    crate::leanh::lean_inc(v_structName_4466_);
                    crate::leanh::lean_inc_ref(v_env_4464_);
                    v___x_4469_ = l_Lean_getStructureParentInfo(v_env_4464_, v_structName_4466_);
                    v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0;
                    v_sz_4494_ = lean_array_size(v___x_4469_);
                    v___x_4495_ = 0usize;
                    v___x_4496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_4465_, v___x_4469_, v_sz_4494_, v___x_4495_, v___x_4493_);
                    v_fst_4497_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                    v_isSharedCheck_4514_ = (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v_unused_4515_ = crate::leanh::lean_ctor_get(v___x_4496_, 1);
                        crate::leanh::lean_dec(v_unused_4515_);
                        v___x_4499_ = v___x_4496_;
                        v_isShared_4500_ = v_isSharedCheck_4514_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4497_);
                        crate::leanh::lean_dec(v___x_4496_);
                        v___x_4499_ = crate::leanh::lean_box(0);
                        v_isShared_4500_ = v_isSharedCheck_4514_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_structName_4466_);
                    crate::leanh::lean_dec_ref(v_env_4464_);
                    v___x_4516_ = crate::leanh::lean_box(0);
                    v___x_4517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4517_, 0, v___x_4516_);
                    crate::leanh::lean_ctor_set(v___x_4517_, 1, v_a_4467_);
                    return v___x_4517_;
                }
            }
            1 => {
                v___x_4471_ = l_Lean_NameSet_insert(v_a_4467_, v_structName_4466_);
                v___x_4472_ = crate::leanh::lean_box(0);
                v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0;
                v_sz_4474_ = lean_array_size(v___x_4469_);
                v___x_4475_ = 0usize;
                v___x_4476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_4464_, v_projName_4465_, v___x_4469_, v_sz_4474_, v___x_4475_, v___x_4473_, v___x_4471_);
                crate::leanh::lean_dec_ref(v___x_4469_);
                v_fst_4477_ = crate::leanh::lean_ctor_get(v___x_4476_, 0);
                crate::leanh::lean_inc(v_fst_4477_);
                v_fst_4478_ = crate::leanh::lean_ctor_get(v_fst_4477_, 0);
                v_isSharedCheck_4491_ = (!crate::leanh::lean_is_exclusive(v_fst_4477_)) as u8;
                if v_isSharedCheck_4491_ == 0 {
                    v_unused_4492_ = crate::leanh::lean_ctor_get(v_fst_4477_, 1);
                    crate::leanh::lean_dec(v_unused_4492_);
                    v___x_4480_ = v_fst_4477_;
                    v_isShared_4481_ = v_isSharedCheck_4491_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4478_);
                    crate::leanh::lean_dec(v_fst_4477_);
                    v___x_4480_ = crate::leanh::lean_box(0);
                    v_isShared_4481_ = v_isSharedCheck_4491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_4478_) == 0 {
                    v_snd_4482_ = crate::leanh::lean_ctor_get(v___x_4476_, 1);
                    crate::leanh::lean_inc(v_snd_4482_);
                    crate::leanh::lean_dec_ref(v___x_4476_);
                    if v_isShared_4481_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4480_, 1, v_snd_4482_);
                        crate::leanh::lean_ctor_set(v___x_4480_, 0, v___x_4472_);
                        v___x_4484_ = v___x_4480_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4472_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 1, v_snd_4482_);
                        v___x_4484_ = v_reuseFailAlloc_4485_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_snd_4486_ = crate::leanh::lean_ctor_get(v___x_4476_, 1);
                    crate::leanh::lean_inc(v_snd_4486_);
                    crate::leanh::lean_dec_ref(v___x_4476_);
                    v_val_4487_ = crate::leanh::lean_ctor_get(v_fst_4478_, 0);
                    crate::leanh::lean_inc(v_val_4487_);
                    crate::leanh::lean_dec_ref_known(v_fst_4478_, 1);
                    if v_isShared_4481_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4480_, 1, v_snd_4486_);
                        crate::leanh::lean_ctor_set(v___x_4480_, 0, v_val_4487_);
                        v___x_4489_ = v___x_4480_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_val_4487_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_snd_4486_);
                        v___x_4489_ = v_reuseFailAlloc_4490_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4484_;
            }
            4 => {
                return v___x_4489_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_fst_4497_) == 0 {
                    crate::leanh::lean_del_object(v___x_4499_);
                    state = 1;
                    continue;
                } else {
                    v_val_4501_ = crate::leanh::lean_ctor_get(v_fst_4497_, 0);
                    crate::leanh::lean_inc(v_val_4501_);
                    crate::leanh::lean_dec_ref_known(v_fst_4497_, 1);
                    if crate::leanh::lean_obj_tag(v_val_4501_) == 1 {
                        crate::leanh::lean_dec_ref(v___x_4469_);
                        crate::leanh::lean_dec(v_structName_4466_);
                        crate::leanh::lean_dec_ref(v_env_4464_);
                        v_val_4502_ = crate::leanh::lean_ctor_get(v_val_4501_, 0);
                        v_isSharedCheck_4513_ =
                            (!crate::leanh::lean_is_exclusive(v_val_4501_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4504_ = v_val_4501_;
                            v_isShared_4505_ = v_isSharedCheck_4513_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4502_);
                            crate::leanh::lean_dec(v_val_4501_);
                            v___x_4504_ = crate::leanh::lean_box(0);
                            v_isShared_4505_ = v_isSharedCheck_4513_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4501_);
                        crate::leanh::lean_del_object(v___x_4499_);
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                v_structName_4506_ = crate::leanh::lean_ctor_get(v_val_4502_, 0);
                crate::leanh::lean_inc(v_structName_4506_);
                crate::leanh::lean_dec(v_val_4502_);
                if v_isShared_4505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4504_, 0, v_structName_4506_);
                    v___x_4508_ = v___x_4504_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_structName_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4512_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4499_, 1, v_a_4467_);
                    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4508_);
                    v___x_4510_ = v___x_4499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_a_4467_);
                    v___x_4510_ = v_reuseFailAlloc_4511_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(
    mut v_env_4518_: *mut crate::leanh::LeanObject,
    mut v_projName_4519_: *mut crate::leanh::LeanObject,
    mut v_as_4520_: *mut crate::leanh::LeanObject,
    mut v_sz_4521_: usize,
    mut v_i_4522_: usize,
    mut v_b_4523_: *mut crate::leanh::LeanObject,
    mut v___y_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: usize = 0;
    let mut v___x_4543_: usize = 0;
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4525_ = lean_usize_dec_lt(v_i_4522_, v_sz_4521_);
                if v___x_4525_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_4518_);
                    v___x_4526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4526_, 0, v_b_4523_);
                    crate::leanh::lean_ctor_set(v___x_4526_, 1, v___y_4524_);
                    return v___x_4526_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4523_);
                    v_a_4527_ = lean_array_uget_borrowed(v_as_4520_, v_i_4522_);
                    v_structName_4528_ = crate::leanh::lean_ctor_get(v_a_4527_, 0);
                    crate::leanh::lean_inc(v_structName_4528_);
                    crate::leanh::lean_inc_ref(v_env_4518_);
                    v___x_4529_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(
                        v_env_4518_,
                        v_projName_4519_,
                        v_structName_4528_,
                        v___y_4524_,
                    );
                    v_fst_4530_ = crate::leanh::lean_ctor_get(v___x_4529_, 0);
                    v_snd_4531_ = crate::leanh::lean_ctor_get(v___x_4529_, 1);
                    v_isSharedCheck_4545_ = (!crate::leanh::lean_is_exclusive(v___x_4529_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4533_ = v___x_4529_;
                        v_isShared_4534_ = v_isSharedCheck_4545_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4531_);
                        crate::leanh::lean_inc(v_fst_4530_);
                        crate::leanh::lean_dec(v___x_4529_);
                        v___x_4533_ = crate::leanh::lean_box(0);
                        v_isShared_4534_ = v_isSharedCheck_4545_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4535_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_fst_4530_) == 1 {
                    crate::leanh::lean_dec_ref(v_env_4518_);
                    v___x_4536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4536_, 0, v_fst_4530_);
                    if v_isShared_4534_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4533_, 1, v___x_4535_);
                        crate::leanh::lean_ctor_set(v___x_4533_, 0, v___x_4536_);
                        v___x_4538_ = v___x_4533_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4536_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4540_, 1, v___x_4535_);
                        v___x_4538_ = v_reuseFailAlloc_4540_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4533_);
                    crate::leanh::lean_dec(v_fst_4530_);
                    v___x_4541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0;
                    v___x_4542_ = 1usize;
                    v___x_4543_ = lean_usize_add(v_i_4522_, v___x_4542_);
                    v_i_4522_ = v___x_4543_;
                    v_b_4523_ = v___x_4541_;
                    v___y_4524_ = v_snd_4531_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_4539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4539_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4539_, 1, v_snd_4531_);
                return v___x_4539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(
    mut v_env_4546_: *mut crate::leanh::LeanObject,
    mut v_projName_4547_: *mut crate::leanh::LeanObject,
    mut v_as_4548_: *mut crate::leanh::LeanObject,
    mut v_sz_4549_: *mut crate::leanh::LeanObject,
    mut v_i_4550_: *mut crate::leanh::LeanObject,
    mut v_b_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4553_: usize = 0;
    let mut v_i_boxed_4554_: usize = 0;
    let mut v_res_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4553_ = crate::leanh::lean_unbox_usize(v_sz_4549_);
    crate::leanh::lean_dec(v_sz_4549_);
    v_i_boxed_4554_ = crate::leanh::lean_unbox_usize(v_i_4550_);
    crate::leanh::lean_dec(v_i_4550_);
    v_res_4555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_4546_, v_projName_4547_, v_as_4548_, v_sz_boxed_4553_, v_i_boxed_4554_, v_b_4551_, v___y_4552_);
    crate::leanh::lean_dec_ref(v_as_4548_);
    crate::leanh::lean_dec(v_projName_4547_);
    return v_res_4555_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(
    mut v_env_4556_: *mut crate::leanh::LeanObject,
    mut v_projName_4557_: *mut crate::leanh::LeanObject,
    mut v_structName_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4560_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(
        v_env_4556_,
        v_projName_4557_,
        v_structName_4558_,
        v_a_4559_,
    );
    crate::leanh::lean_dec(v_projName_4557_);
    return v_res_4560_;
}
pub unsafe fn l_Lean_findParentProjStruct_x3f(
    mut v_env_4561_: *mut crate::leanh::LeanObject,
    mut v_structName_4562_: *mut crate::leanh::LeanObject,
    mut v_projName_4563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4564_ = l_Lean_NameSet_empty;
    v___x_4565_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(
        v_env_4561_,
        v_projName_4563_,
        v_structName_4562_,
        v___x_4564_,
    );
    v_fst_4566_ = crate::leanh::lean_ctor_get(v___x_4565_, 0);
    crate::leanh::lean_inc(v_fst_4566_);
    crate::leanh::lean_dec_ref(v___x_4565_);
    return v_fst_4566_;
}
pub unsafe fn l_Lean_findParentProjStruct_x3f___boxed(
    mut v_env_4567_: *mut crate::leanh::LeanObject,
    mut v_structName_4568_: *mut crate::leanh::LeanObject,
    mut v_projName_4569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4570_ =
        l_Lean_findParentProjStruct_x3f(v_env_4567_, v_structName_4568_, v_projName_4569_);
    crate::leanh::lean_dec(v_projName_4569_);
    return v_res_4570_;
}
pub unsafe fn l_Lean_mkFlatCtorOfStructCtorName(
    mut v_structCtorName_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l_Lean_mkFlatCtorOfStructCtorName___closed__1;
    v___x_4576_ = l_Lean_Name_append(v_structCtorName_4574_, v___x_4575_);
    return v___x_4576_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(
    mut v_env_4577_: *mut crate::leanh::LeanObject,
    mut v_structName_4578_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4579_: u8,
    mut v_as_4580_: *mut crate::leanh::LeanObject,
    mut v_i_4581_: usize,
    mut v_stop_4582_: usize,
    mut v_b_4583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4589_ = lean_usize_dec_eq(v_i_4581_, v_stop_4582_);
                if v___x_4589_ == 0 {
                    v___x_4590_ = lean_array_uget_borrowed(v_as_4580_, v_i_4581_);
                    crate::leanh::lean_inc(v___x_4590_);
                    crate::leanh::lean_inc(v_structName_4578_);
                    crate::leanh::lean_inc_ref(v_env_4577_);
                    v___x_4591_ =
                        l_Lean_isSubobjectField_x3f(v_env_4577_, v_structName_4578_, v___x_4590_);
                    if crate::leanh::lean_obj_tag(v___x_4591_) == 0 {
                        crate::leanh::lean_inc(v___x_4590_);
                        v___x_4592_ = lean_array_push(v_b_4583_, v___x_4590_);
                        v___y_4585_ = v___x_4592_;
                        state = 1;
                        continue;
                    } else {
                        if v_includeSubobjectFields_4579_ == 0 {
                            v_val_4593_ = crate::leanh::lean_ctor_get(v___x_4591_, 0);
                            crate::leanh::lean_inc(v_val_4593_);
                            crate::leanh::lean_dec_ref_known(v___x_4591_, 1);
                            crate::leanh::lean_inc_ref(v_env_4577_);
                            v___x_4594_ =
                                l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(
                                    v_env_4577_,
                                    v_val_4593_,
                                    v_b_4583_,
                                    v_includeSubobjectFields_4579_,
                                );
                            v___y_4585_ = v___x_4594_;
                            state = 1;
                            continue;
                        } else {
                            v_val_4595_ = crate::leanh::lean_ctor_get(v___x_4591_, 0);
                            crate::leanh::lean_inc(v_val_4595_);
                            crate::leanh::lean_dec_ref_known(v___x_4591_, 1);
                            crate::leanh::lean_inc(v___x_4590_);
                            v___x_4596_ = lean_array_push(v_b_4583_, v___x_4590_);
                            crate::leanh::lean_inc_ref(v_env_4577_);
                            v___x_4597_ =
                                l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(
                                    v_env_4577_,
                                    v_val_4595_,
                                    v___x_4596_,
                                    v_includeSubobjectFields_4579_,
                                );
                            v___y_4585_ = v___x_4597_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_structName_4578_);
                    crate::leanh::lean_dec_ref(v_env_4577_);
                    return v_b_4583_;
                }
            }
            1 => {
                v___x_4586_ = 1usize;
                v___x_4587_ = lean_usize_add(v_i_4581_, v___x_4586_);
                v_i_4581_ = v___x_4587_;
                v_b_4583_ = v___y_4585_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(
    mut v_env_4598_: *mut crate::leanh::LeanObject,
    mut v_structName_4599_: *mut crate::leanh::LeanObject,
    mut v_fullNames_4600_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4601_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    crate::leanh::lean_inc(v_structName_4599_);
    crate::leanh::lean_inc_ref(v_env_4598_);
    v___x_4602_ = l_Lean_getStructureFields(v_env_4598_, v_structName_4599_);
    v___x_4603_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4604_ = lean_array_get_size(v___x_4602_);
    v___x_4605_ = lean_nat_dec_lt(v___x_4603_, v___x_4604_);
    if v___x_4605_ == 0 {
        crate::leanh::lean_dec_ref(v___x_4602_);
        crate::leanh::lean_dec(v_structName_4599_);
        crate::leanh::lean_dec_ref(v_env_4598_);
        return v_fullNames_4600_;
    } else {
        let mut v___x_4606_: u8 = 0;
        v___x_4606_ = lean_nat_dec_le(v___x_4604_, v___x_4604_);
        if v___x_4606_ == 0 {
            if v___x_4605_ == 0 {
                crate::leanh::lean_dec_ref(v___x_4602_);
                crate::leanh::lean_dec(v_structName_4599_);
                crate::leanh::lean_dec_ref(v_env_4598_);
                return v_fullNames_4600_;
            } else {
                let mut v___x_4607_: usize = 0;
                let mut v___x_4608_: usize = 0;
                let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4607_ = 0usize;
                v___x_4608_ = lean_usize_of_nat(v___x_4604_);
                v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_4598_, v_structName_4599_, v_includeSubobjectFields_4601_, v___x_4602_, v___x_4607_, v___x_4608_, v_fullNames_4600_);
                crate::leanh::lean_dec_ref(v___x_4602_);
                return v___x_4609_;
            }
        } else {
            let mut v___x_4610_: usize = 0;
            let mut v___x_4611_: usize = 0;
            let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4610_ = 0usize;
            v___x_4611_ = lean_usize_of_nat(v___x_4604_);
            v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_4598_, v_structName_4599_, v_includeSubobjectFields_4601_, v___x_4602_, v___x_4610_, v___x_4611_, v_fullNames_4600_);
            crate::leanh::lean_dec_ref(v___x_4602_);
            return v___x_4612_;
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(
    mut v_env_4613_: *mut crate::leanh::LeanObject,
    mut v_structName_4614_: *mut crate::leanh::LeanObject,
    mut v_fullNames_4615_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeSubobjectFields_boxed_4617_: u8 = 0;
    let mut v_res_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeSubobjectFields_boxed_4617_ =
        (crate::leanh::lean_unbox(v_includeSubobjectFields_4616_) as u8);
    v_res_4618_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(
        v_env_4613_,
        v_structName_4614_,
        v_fullNames_4615_,
        v_includeSubobjectFields_boxed_4617_,
    );
    return v_res_4618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(
    mut v_env_4619_: *mut crate::leanh::LeanObject,
    mut v_structName_4620_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4621_: *mut crate::leanh::LeanObject,
    mut v_as_4622_: *mut crate::leanh::LeanObject,
    mut v_i_4623_: *mut crate::leanh::LeanObject,
    mut v_stop_4624_: *mut crate::leanh::LeanObject,
    mut v_b_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeSubobjectFields_boxed_4626_: u8 = 0;
    let mut v_i_boxed_4627_: usize = 0;
    let mut v_stop_boxed_4628_: usize = 0;
    let mut v_res_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeSubobjectFields_boxed_4626_ =
        (crate::leanh::lean_unbox(v_includeSubobjectFields_4621_) as u8);
    v_i_boxed_4627_ = crate::leanh::lean_unbox_usize(v_i_4623_);
    crate::leanh::lean_dec(v_i_4623_);
    v_stop_boxed_4628_ = crate::leanh::lean_unbox_usize(v_stop_4624_);
    crate::leanh::lean_dec(v_stop_4624_);
    v_res_4629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_4619_, v_structName_4620_, v_includeSubobjectFields_boxed_4626_, v_as_4622_, v_i_boxed_4627_, v_stop_boxed_4628_, v_b_4625_);
    crate::leanh::lean_dec_ref(v_as_4622_);
    return v_res_4629_;
}
pub unsafe fn l_Lean_getStructureFieldsFlattened(
    mut v_env_4630_: *mut crate::leanh::LeanObject,
    mut v_structName_4631_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4632_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = l_Lean_instInhabitedStructureInfo_default___closed__0;
    v___x_4634_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(
        v_env_4630_,
        v_structName_4631_,
        v___x_4633_,
        v_includeSubobjectFields_4632_,
    );
    return v___x_4634_;
}
pub unsafe fn l_Lean_getStructureFieldsFlattened___boxed(
    mut v_env_4635_: *mut crate::leanh::LeanObject,
    mut v_structName_4636_: *mut crate::leanh::LeanObject,
    mut v_includeSubobjectFields_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeSubobjectFields_boxed_4638_: u8 = 0;
    let mut v_res_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeSubobjectFields_boxed_4638_ =
        (crate::leanh::lean_unbox(v_includeSubobjectFields_4637_) as u8);
    v_res_4639_ = l_Lean_getStructureFieldsFlattened(
        v_env_4635_,
        v_structName_4636_,
        v_includeSubobjectFields_boxed_4638_,
    );
    return v_res_4639_;
}
pub unsafe fn l_Lean_isStructure(
    mut v_env_4640_: *mut crate::leanh::LeanObject,
    mut v_constName_4641_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4642_ = l_Lean_getStructureInfo_x3f(v_env_4640_, v_constName_4641_);
    if crate::leanh::lean_obj_tag(v___x_4642_) == 0 {
        let mut v___x_4643_: u8 = 0;
        v___x_4643_ = 0;
        return v___x_4643_;
    } else {
        let mut v___x_4644_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_4642_, 1);
        v___x_4644_ = 1;
        return v___x_4644_;
    }
}
pub unsafe fn l_Lean_isStructure___boxed(
    mut v_env_4645_: *mut crate::leanh::LeanObject,
    mut v_constName_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4647_: u8 = 0;
    let mut v_r_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Lean_isStructure(v_env_4645_, v_constName_4646_);
    v_r_4648_ = crate::leanh::lean_box((v_res_4647_) as usize);
    return v_r_4648_;
}
pub unsafe fn l_Lean_getProjFnForField_x3f(
    mut v_env_4649_: *mut crate::leanh::LeanObject,
    mut v_structName_4650_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v_projFn_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4661_: u8 = 0;
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4652_ =
                    l_Lean_getFieldInfo_x3f(v_env_4649_, v_structName_4650_, v_fieldName_4651_);
                if crate::leanh::lean_obj_tag(v___x_4652_) == 1 {
                    v_val_4653_ = crate::leanh::lean_ctor_get(v___x_4652_, 0);
                    v_isSharedCheck_4661_ = (!crate::leanh::lean_is_exclusive(v___x_4652_)) as u8;
                    if v_isSharedCheck_4661_ == 0 {
                        v___x_4655_ = v___x_4652_;
                        v_isShared_4656_ = v_isSharedCheck_4661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4653_);
                        crate::leanh::lean_dec(v___x_4652_);
                        v___x_4655_ = crate::leanh::lean_box(0);
                        v_isShared_4656_ = v_isSharedCheck_4661_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4652_);
                    v___x_4662_ = crate::leanh::lean_box(0);
                    return v___x_4662_;
                }
            }
            1 => {
                v_projFn_4657_ = crate::leanh::lean_ctor_get(v_val_4653_, 1);
                crate::leanh::lean_inc(v_projFn_4657_);
                crate::leanh::lean_dec(v_val_4653_);
                if v_isShared_4656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4655_, 0, v_projFn_4657_);
                    v___x_4659_ = v___x_4655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_projFn_4657_);
                    v___x_4659_ = v_reuseFailAlloc_4660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getProjFnInfoForField_x3f(
    mut v_env_4663_: *mut crate::leanh::LeanObject,
    mut v_structName_4664_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_env_4663_);
                v___x_4666_ = l_Lean_getProjFnForField_x3f(
                    v_env_4663_,
                    v_structName_4664_,
                    v_fieldName_4665_,
                );
                if crate::leanh::lean_obj_tag(v___x_4666_) == 1 {
                    v_val_4667_ = crate::leanh::lean_ctor_get(v___x_4666_, 0);
                    crate::leanh::lean_inc_n(v_val_4667_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4666_, 1);
                    v___x_4668_ =
                        l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4663_, v_val_4667_);
                    if crate::leanh::lean_obj_tag(v___x_4668_) == 0 {
                        crate::leanh::lean_dec(v_val_4667_);
                        v___x_4669_ = crate::leanh::lean_box(0);
                        return v___x_4669_;
                    } else {
                        v_val_4670_ = crate::leanh::lean_ctor_get(v___x_4668_, 0);
                        v_isSharedCheck_4678_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4668_)) as u8;
                        if v_isSharedCheck_4678_ == 0 {
                            v___x_4672_ = v___x_4668_;
                            v_isShared_4673_ = v_isSharedCheck_4678_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4670_);
                            crate::leanh::lean_dec(v___x_4668_);
                            v___x_4672_ = crate::leanh::lean_box(0);
                            v_isShared_4673_ = v_isSharedCheck_4678_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4666_);
                    crate::leanh::lean_dec_ref(v_env_4663_);
                    v___x_4679_ = crate::leanh::lean_box(0);
                    return v___x_4679_;
                }
            }
            1 => {
                v___x_4674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4674_, 0, v_val_4667_);
                crate::leanh::lean_ctor_set(v___x_4674_, 1, v_val_4670_);
                if v_isShared_4673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4672_, 0, v___x_4674_);
                    v___x_4676_ = v___x_4672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4674_);
                    v___x_4676_ = v_reuseFailAlloc_4677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefaultFnOfProjFn(
    mut v_projFn_4683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l_Lean_mkDefaultFnOfProjFn___closed__1;
    v___x_4685_ = l_Lean_Name_append(v_projFn_4683_, v___x_4684_);
    return v___x_4685_;
}
pub unsafe fn l_Lean_mkInheritedDefaultFnOfProjFn(
    mut v_projFn_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4690_ = l_Lean_mkInheritedDefaultFnOfProjFn___closed__1;
    v___x_4691_ = l_Lean_Name_append(v_projFn_4689_, v___x_4690_);
    return v___x_4691_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(
    mut v_mkName_4692_: *mut crate::leanh::LeanObject,
    mut v_env_4693_: *mut crate::leanh::LeanObject,
    mut v_structName_4694_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v_defFn_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: u8 = 0;
    let mut v___x_4703_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defFn_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v___x_4712_: u8 = 0;
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fieldName_4695_);
                crate::leanh::lean_inc(v_structName_4694_);
                crate::leanh::lean_inc_ref(v_env_4693_);
                v___x_4696_ = l_Lean_getProjFnForField_x3f(
                    v_env_4693_,
                    v_structName_4694_,
                    v_fieldName_4695_,
                );
                if crate::leanh::lean_obj_tag(v___x_4696_) == 1 {
                    crate::leanh::lean_dec(v_fieldName_4695_);
                    crate::leanh::lean_dec(v_structName_4694_);
                    v_val_4697_ = crate::leanh::lean_ctor_get(v___x_4696_, 0);
                    v_isSharedCheck_4708_ = (!crate::leanh::lean_is_exclusive(v___x_4696_)) as u8;
                    if v_isSharedCheck_4708_ == 0 {
                        v___x_4699_ = v___x_4696_;
                        v_isShared_4700_ = v_isSharedCheck_4708_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4697_);
                        crate::leanh::lean_dec(v___x_4696_);
                        v___x_4699_ = crate::leanh::lean_box(0);
                        v_isShared_4700_ = v_isSharedCheck_4708_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4696_);
                    v___x_4709_ = l_Lean_Name_append(v_structName_4694_, v_fieldName_4695_);
                    v_defFn_4710_ = crate::leanh::lean_apply_1(v_mkName_4692_, v___x_4709_);
                    v___x_4711_ = 1;
                    crate::leanh::lean_inc(v_defFn_4710_);
                    v___x_4712_ =
                        l_Lean_Environment_contains(v_env_4693_, v_defFn_4710_, v___x_4711_);
                    if v___x_4712_ == 0 {
                        crate::leanh::lean_dec(v_defFn_4710_);
                        v___x_4713_ = crate::leanh::lean_box(0);
                        return v___x_4713_;
                    } else {
                        v___x_4714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4714_, 0, v_defFn_4710_);
                        return v___x_4714_;
                    }
                }
            }
            1 => {
                v_defFn_4701_ = crate::leanh::lean_apply_1(v_mkName_4692_, v_val_4697_);
                v___x_4702_ = 1;
                crate::leanh::lean_inc(v_defFn_4701_);
                v___x_4703_ = l_Lean_Environment_contains(v_env_4693_, v_defFn_4701_, v___x_4702_);
                if v___x_4703_ == 0 {
                    crate::leanh::lean_dec(v_defFn_4701_);
                    crate::leanh::lean_del_object(v___x_4699_);
                    v___x_4704_ = crate::leanh::lean_box(0);
                    return v___x_4704_;
                } else {
                    if v_isShared_4700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4699_, 0, v_defFn_4701_);
                        v___x_4706_ = v___x_4699_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_defFn_4701_);
                        v___x_4706_ = v_reuseFailAlloc_4707_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getDefaultFnForField_x3f(
    mut v_env_4716_: *mut crate::leanh::LeanObject,
    mut v_structName_4717_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Lean_getDefaultFnForField_x3f___closed__0;
    v___x_4720_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(
        v___x_4719_,
        v_env_4716_,
        v_structName_4717_,
        v_fieldName_4718_,
    );
    return v___x_4720_;
}
pub unsafe fn l_Lean_getEffectiveDefaultFnForField_x3f(
    mut v_env_4722_: *mut crate::leanh::LeanObject,
    mut v_structName_4723_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_fieldName_4724_);
    crate::leanh::lean_inc(v_structName_4723_);
    crate::leanh::lean_inc_ref(v_env_4722_);
    v___x_4725_ =
        l_Lean_getDefaultFnForField_x3f(v_env_4722_, v_structName_4723_, v_fieldName_4724_);
    if crate::leanh::lean_obj_tag(v___x_4725_) == 0 {
        let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4726_ = l_Lean_getEffectiveDefaultFnForField_x3f___closed__0;
        v___x_4727_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(
            v___x_4726_,
            v_env_4722_,
            v_structName_4723_,
            v_fieldName_4724_,
        );
        return v___x_4727_;
    } else {
        crate::leanh::lean_dec(v_fieldName_4724_);
        crate::leanh::lean_dec(v_structName_4723_);
        crate::leanh::lean_dec_ref(v_env_4722_);
        return v___x_4725_;
    }
}
pub unsafe fn l_Lean_mkAutoParamFnOfProjFn(
    mut v_projFn_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_mkAutoParamFnOfProjFn___closed__1;
    v___x_4733_ = l_Lean_Name_append(v_projFn_4731_, v___x_4732_);
    return v___x_4733_;
}
pub unsafe fn l_Lean_getAutoParamFnForField_x3f(
    mut v_env_4735_: *mut crate::leanh::LeanObject,
    mut v_structName_4736_: *mut crate::leanh::LeanObject,
    mut v_fieldName_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = l_Lean_getAutoParamFnForField_x3f___closed__0;
    v___x_4739_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(
        v___x_4738_,
        v_env_4735_,
        v_structName_4736_,
        v_fieldName_4737_,
    );
    return v___x_4739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(
    mut v_path_4740_: *mut crate::leanh::LeanObject,
    mut v_env_4741_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4742_: *mut crate::leanh::LeanObject,
    mut v_as_4743_: *mut crate::leanh::LeanObject,
    mut v_i_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subobject_x3f_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4751_ = lean_array_get_size(v_as_4743_);
                v___x_4752_ = lean_nat_dec_lt(v_i_4744_, v___x_4751_);
                if v___x_4752_ == 0 {
                    crate::leanh::lean_dec(v_i_4744_);
                    crate::leanh::lean_dec_ref(v_env_4741_);
                    crate::leanh::lean_dec(v_path_4740_);
                    v___x_4753_ = crate::leanh::lean_box(0);
                    v___x_4754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4754_, 0, v___x_4753_);
                    crate::leanh::lean_ctor_set(v___x_4754_, 1, v___y_4745_);
                    return v___x_4754_;
                } else {
                    v___x_4755_ = lean_array_fget_borrowed(v_as_4743_, v_i_4744_);
                    v_subobject_x3f_4756_ = crate::leanh::lean_ctor_get(v___x_4755_, 2);
                    if crate::leanh::lean_obj_tag(v_subobject_x3f_4756_) == 1 {
                        v_projFn_4757_ = crate::leanh::lean_ctor_get(v___x_4755_, 1);
                        v_val_4758_ = crate::leanh::lean_ctor_get(v_subobject_x3f_4756_, 0);
                        crate::leanh::lean_inc(v_path_4740_);
                        crate::leanh::lean_inc(v_projFn_4757_);
                        v___x_4759_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4759_, 0, v_projFn_4757_);
                        crate::leanh::lean_ctor_set(v___x_4759_, 1, v_path_4740_);
                        crate::leanh::lean_inc(v_val_4758_);
                        crate::leanh::lean_inc_ref(v_env_4741_);
                        v___x_4760_ =
                            l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(
                                v_env_4741_,
                                v_baseStructName_4742_,
                                v_val_4758_,
                                v___x_4759_,
                                v___y_4745_,
                            );
                        v_fst_4761_ = crate::leanh::lean_ctor_get(v___x_4760_, 0);
                        crate::leanh::lean_inc(v_fst_4761_);
                        if crate::leanh::lean_obj_tag(v_fst_4761_) == 0 {
                            v_snd_4762_ = crate::leanh::lean_ctor_get(v___x_4760_, 1);
                            crate::leanh::lean_inc(v_snd_4762_);
                            crate::leanh::lean_dec_ref(v___x_4760_);
                            v_snd_4747_ = v_snd_4762_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fst_4761_, 1);
                            crate::leanh::lean_dec(v_i_4744_);
                            crate::leanh::lean_dec_ref(v_env_4741_);
                            crate::leanh::lean_dec(v_path_4740_);
                            return v___x_4760_;
                        }
                    } else {
                        v_snd_4747_ = v___y_4745_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4748_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4749_ = lean_nat_add(v_i_4744_, v___x_4748_);
                crate::leanh::lean_dec(v_i_4744_);
                v_i_4744_ = v___x_4749_;
                v___y_4745_ = v_snd_4747_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(
    mut v_env_4763_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4764_: *mut crate::leanh::LeanObject,
    mut v_structName_4765_: *mut crate::leanh::LeanObject,
    mut v_path_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parentInfo_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: u8 = 0;
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4781_ = lean_name_eq(v_baseStructName_4764_, v_structName_4765_);
                if v___x_4781_ == 0 {
                    v___x_4782_ = l_Lean_NameSet_contains(v_a_4767_, v_structName_4765_);
                    if v___x_4782_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v___x_4781_ == 0 {
                            crate::leanh::lean_dec(v_path_4766_);
                            crate::leanh::lean_dec(v_structName_4765_);
                            crate::leanh::lean_dec_ref(v_env_4763_);
                            v___x_4783_ = crate::leanh::lean_box(0);
                            v___x_4784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4783_);
                            crate::leanh::lean_ctor_set(v___x_4784_, 1, v_a_4767_);
                            return v___x_4784_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_structName_4765_);
                    crate::leanh::lean_dec_ref(v_env_4763_);
                    v___x_4785_ = l_List_reverse___redArg(v_path_4766_);
                    v___x_4786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4786_, 0, v___x_4785_);
                    v___x_4787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                    crate::leanh::lean_ctor_set(v___x_4787_, 1, v_a_4767_);
                    return v___x_4787_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_structName_4765_);
                v___x_4769_ = l_Lean_NameSet_insert(v_a_4767_, v_structName_4765_);
                crate::leanh::lean_inc_ref(v_env_4763_);
                v___x_4770_ = l_Lean_getStructureInfo_x3f(v_env_4763_, v_structName_4765_);
                if crate::leanh::lean_obj_tag(v___x_4770_) == 1 {
                    v_val_4771_ = crate::leanh::lean_ctor_get(v___x_4770_, 0);
                    crate::leanh::lean_inc(v_val_4771_);
                    crate::leanh::lean_dec_ref_known(v___x_4770_, 1);
                    v_fieldInfo_4772_ = crate::leanh::lean_ctor_get(v_val_4771_, 2);
                    crate::leanh::lean_inc_ref(v_fieldInfo_4772_);
                    v_parentInfo_4773_ = crate::leanh::lean_ctor_get(v_val_4771_, 3);
                    crate::leanh::lean_inc_ref(v_parentInfo_4773_);
                    crate::leanh::lean_dec(v_val_4771_);
                    v___x_4774_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc_ref(v_env_4763_);
                    crate::leanh::lean_inc(v_path_4766_);
                    v___x_4775_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_4766_, v_env_4763_, v_baseStructName_4764_, v_fieldInfo_4772_, v___x_4774_, v___x_4769_);
                    crate::leanh::lean_dec_ref(v_fieldInfo_4772_);
                    v_fst_4776_ = crate::leanh::lean_ctor_get(v___x_4775_, 0);
                    crate::leanh::lean_inc(v_fst_4776_);
                    if crate::leanh::lean_obj_tag(v_fst_4776_) == 0 {
                        v_snd_4777_ = crate::leanh::lean_ctor_get(v___x_4775_, 1);
                        crate::leanh::lean_inc(v_snd_4777_);
                        crate::leanh::lean_dec_ref(v___x_4775_);
                        v___x_4778_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_4766_, v_env_4763_, v_baseStructName_4764_, v_parentInfo_4773_, v___x_4774_, v_snd_4777_);
                        crate::leanh::lean_dec_ref(v_parentInfo_4773_);
                        return v___x_4778_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_4776_, 1);
                        crate::leanh::lean_dec_ref(v_parentInfo_4773_);
                        crate::leanh::lean_dec(v_path_4766_);
                        crate::leanh::lean_dec_ref(v_env_4763_);
                        return v___x_4775_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4770_);
                    crate::leanh::lean_dec(v_path_4766_);
                    crate::leanh::lean_dec_ref(v_env_4763_);
                    v___x_4779_ = crate::leanh::lean_box(0);
                    v___x_4780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4780_, 0, v___x_4779_);
                    crate::leanh::lean_ctor_set(v___x_4780_, 1, v___x_4769_);
                    return v___x_4780_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(
    mut v_path_4788_: *mut crate::leanh::LeanObject,
    mut v_env_4789_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4790_: *mut crate::leanh::LeanObject,
    mut v_as_4791_: *mut crate::leanh::LeanObject,
    mut v_i_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: u8 = 0;
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4794_ = lean_array_get_size(v_as_4791_);
                v___x_4795_ = lean_nat_dec_lt(v_i_4792_, v___x_4794_);
                if v___x_4795_ == 0 {
                    crate::leanh::lean_dec(v_i_4792_);
                    crate::leanh::lean_dec_ref(v_env_4789_);
                    crate::leanh::lean_dec(v_path_4788_);
                    v___x_4796_ = crate::leanh::lean_box(0);
                    v___x_4797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4797_, 0, v___x_4796_);
                    crate::leanh::lean_ctor_set(v___x_4797_, 1, v___y_4793_);
                    return v___x_4797_;
                } else {
                    v___x_4798_ = lean_array_fget_borrowed(v_as_4791_, v_i_4792_);
                    v_structName_4799_ = crate::leanh::lean_ctor_get(v___x_4798_, 0);
                    v_projFn_4800_ = crate::leanh::lean_ctor_get(v___x_4798_, 1);
                    crate::leanh::lean_inc(v_path_4788_);
                    crate::leanh::lean_inc(v_projFn_4800_);
                    v___x_4801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4801_, 0, v_projFn_4800_);
                    crate::leanh::lean_ctor_set(v___x_4801_, 1, v_path_4788_);
                    crate::leanh::lean_inc(v_structName_4799_);
                    crate::leanh::lean_inc_ref(v_env_4789_);
                    v___x_4802_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(
                        v_env_4789_,
                        v_baseStructName_4790_,
                        v_structName_4799_,
                        v___x_4801_,
                        v___y_4793_,
                    );
                    v_fst_4803_ = crate::leanh::lean_ctor_get(v___x_4802_, 0);
                    crate::leanh::lean_inc(v_fst_4803_);
                    if crate::leanh::lean_obj_tag(v_fst_4803_) == 0 {
                        v_snd_4804_ = crate::leanh::lean_ctor_get(v___x_4802_, 1);
                        crate::leanh::lean_inc(v_snd_4804_);
                        crate::leanh::lean_dec_ref(v___x_4802_);
                        v___x_4805_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4806_ = lean_nat_add(v_i_4792_, v___x_4805_);
                        crate::leanh::lean_dec(v_i_4792_);
                        v_i_4792_ = v___x_4806_;
                        v___y_4793_ = v_snd_4804_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_4803_, 1);
                        crate::leanh::lean_dec(v_i_4792_);
                        crate::leanh::lean_dec_ref(v_env_4789_);
                        crate::leanh::lean_dec(v_path_4788_);
                        return v___x_4802_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(
    mut v_path_4808_: *mut crate::leanh::LeanObject,
    mut v_env_4809_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4810_: *mut crate::leanh::LeanObject,
    mut v_as_4811_: *mut crate::leanh::LeanObject,
    mut v_i_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4814_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_4808_, v_env_4809_, v_baseStructName_4810_, v_as_4811_, v_i_4812_, v___y_4813_);
    crate::leanh::lean_dec_ref(v_as_4811_);
    crate::leanh::lean_dec(v_baseStructName_4810_);
    return v_res_4814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(
    mut v_path_4815_: *mut crate::leanh::LeanObject,
    mut v_env_4816_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4817_: *mut crate::leanh::LeanObject,
    mut v_as_4818_: *mut crate::leanh::LeanObject,
    mut v_i_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4821_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_4815_, v_env_4816_, v_baseStructName_4817_, v_as_4818_, v_i_4819_, v___y_4820_);
    crate::leanh::lean_dec_ref(v_as_4818_);
    crate::leanh::lean_dec(v_baseStructName_4817_);
    return v_res_4821_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(
    mut v_env_4822_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4823_: *mut crate::leanh::LeanObject,
    mut v_structName_4824_: *mut crate::leanh::LeanObject,
    mut v_path_4825_: *mut crate::leanh::LeanObject,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4827_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(
        v_env_4822_,
        v_baseStructName_4823_,
        v_structName_4824_,
        v_path_4825_,
        v_a_4826_,
    );
    crate::leanh::lean_dec(v_baseStructName_4823_);
    return v_res_4827_;
}
pub unsafe fn l_Lean_getPathToBaseStructure_x3f(
    mut v_env_4828_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4829_: *mut crate::leanh::LeanObject,
    mut v_structName_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = crate::leanh::lean_box(0);
    v___x_4832_ = l_Lean_NameSet_empty;
    v___x_4833_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(
        v_env_4828_,
        v_baseStructName_4829_,
        v_structName_4830_,
        v___x_4831_,
        v___x_4832_,
    );
    v_fst_4834_ = crate::leanh::lean_ctor_get(v___x_4833_, 0);
    crate::leanh::lean_inc(v_fst_4834_);
    crate::leanh::lean_dec_ref(v___x_4833_);
    return v_fst_4834_;
}
pub unsafe fn l_Lean_getPathToBaseStructure_x3f___boxed(
    mut v_env_4835_: *mut crate::leanh::LeanObject,
    mut v_baseStructName_4836_: *mut crate::leanh::LeanObject,
    mut v_structName_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ =
        l_Lean_getPathToBaseStructure_x3f(v_env_4835_, v_baseStructName_4836_, v_structName_4837_);
    crate::leanh::lean_dec(v_baseStructName_4836_);
    return v_res_4838_;
}
pub unsafe fn l_Lean_isNonRecStructure(
    mut v_env_4839_: *mut crate::leanh::LeanObject,
    mut v_constName_4840_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4841_: u8 = 0;
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = 0;
    v___x_4842_ = l_Lean_Environment_find_x3f(v_env_4839_, v_constName_4840_, v___x_4841_);
    if crate::leanh::lean_obj_tag(v___x_4842_) == 1 {
        let mut v_val_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4843_ = crate::leanh::lean_ctor_get(v___x_4842_, 0);
        crate::leanh::lean_inc(v_val_4843_);
        crate::leanh::lean_dec_ref_known(v___x_4842_, 1);
        if crate::leanh::lean_obj_tag(v_val_4843_) == 5 {
            let mut v_val_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_numIndices_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ctors_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isRec_4847_: u8 = 0;
            let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4849_: u8 = 0;
            v_val_4844_ = crate::leanh::lean_ctor_get(v_val_4843_, 0);
            crate::leanh::lean_inc_ref(v_val_4844_);
            crate::leanh::lean_dec_ref_known(v_val_4843_, 1);
            v_numIndices_4845_ = crate::leanh::lean_ctor_get(v_val_4844_, 2);
            crate::leanh::lean_inc(v_numIndices_4845_);
            v_ctors_4846_ = crate::leanh::lean_ctor_get(v_val_4844_, 4);
            crate::leanh::lean_inc(v_ctors_4846_);
            v_isRec_4847_ = crate::leanh::lean_ctor_get_uint8(
                v_val_4844_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
            );
            crate::leanh::lean_dec_ref(v_val_4844_);
            v___x_4848_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_4849_ = lean_nat_dec_eq(v_numIndices_4845_, v___x_4848_);
            crate::leanh::lean_dec(v_numIndices_4845_);
            if v___x_4849_ == 0 {
                crate::leanh::lean_dec(v_ctors_4846_);
                return v___x_4841_;
            } else {
                if crate::leanh::lean_obj_tag(v_ctors_4846_) == 1 {
                    let mut v_tail_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_tail_4850_ = crate::leanh::lean_ctor_get(v_ctors_4846_, 1);
                    crate::leanh::lean_inc(v_tail_4850_);
                    crate::leanh::lean_dec_ref_known(v_ctors_4846_, 2);
                    if crate::leanh::lean_obj_tag(v_tail_4850_) == 0 {
                        if v_isRec_4847_ == 0 {
                            return v___x_4849_;
                        } else {
                            return v___x_4841_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_4850_);
                        return v___x_4841_;
                    }
                } else {
                    crate::leanh::lean_dec(v_ctors_4846_);
                    return v___x_4841_;
                }
            }
        } else {
            crate::leanh::lean_dec(v_val_4843_);
            return v___x_4841_;
        }
    } else {
        crate::leanh::lean_dec(v___x_4842_);
        return v___x_4841_;
    }
}
pub unsafe fn l_Lean_isNonRecStructure___boxed(
    mut v_env_4851_: *mut crate::leanh::LeanObject,
    mut v_constName_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4853_: u8 = 0;
    let mut v_r_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4853_ = l_Lean_isNonRecStructure(v_env_4851_, v_constName_4852_);
    v_r_4854_ = crate::leanh::lean_box((v_res_4853_) as usize);
    return v_r_4854_;
}
pub unsafe fn l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(
    mut v_msg_4855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4856_ = crate::leanh::lean_box(0);
    v___x_4857_ = lean_panic_fn_borrowed(v___x_4856_, v_msg_4855_);
    return v___x_4857_;
}
pub unsafe fn _init_l_Lean_getNonRecStructureCtor_x3f___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_getStructureCtor___closed__2;
    v___x_4860_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_4861_ = crate::leanh::lean_unsigned_to_nat(374);
    v___x_4862_ = l_Lean_getNonRecStructureCtor_x3f___closed__0;
    v___x_4863_ = l_Lean_getStructureInfo___closed__0;
    v___x_4864_ = l_mkPanicMessageWithDecl(
        v___x_4863_,
        v___x_4862_,
        v___x_4861_,
        v___x_4860_,
        v___x_4859_,
    );
    return v___x_4864_;
}
pub unsafe fn l_Lean_getNonRecStructureCtor_x3f(
    mut v_env_4865_: *mut crate::leanh::LeanObject,
    mut v_constName_4866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4886_: u8 = 0;
    let mut v_val_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4891_: u8 = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4870_ = 0;
                crate::leanh::lean_inc_ref(v_env_4865_);
                v___x_4871_ =
                    l_Lean_Environment_find_x3f(v_env_4865_, v_constName_4866_, v___x_4870_);
                if crate::leanh::lean_obj_tag(v___x_4871_) == 1 {
                    v_val_4872_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                    crate::leanh::lean_inc(v_val_4872_);
                    crate::leanh::lean_dec_ref_known(v___x_4871_, 1);
                    if crate::leanh::lean_obj_tag(v_val_4872_) == 5 {
                        v_val_4873_ = crate::leanh::lean_ctor_get(v_val_4872_, 0);
                        crate::leanh::lean_inc_ref(v_val_4873_);
                        crate::leanh::lean_dec_ref_known(v_val_4872_, 1);
                        v_numIndices_4874_ = crate::leanh::lean_ctor_get(v_val_4873_, 2);
                        crate::leanh::lean_inc(v_numIndices_4874_);
                        v_ctors_4875_ = crate::leanh::lean_ctor_get(v_val_4873_, 4);
                        crate::leanh::lean_inc(v_ctors_4875_);
                        v_isRec_4876_ = crate::leanh::lean_ctor_get_uint8(
                            v_val_4873_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        );
                        crate::leanh::lean_dec_ref(v_val_4873_);
                        v___x_4877_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4878_ = lean_nat_dec_eq(v_numIndices_4874_, v___x_4877_);
                        crate::leanh::lean_dec(v_numIndices_4874_);
                        if v___x_4878_ == 0 {
                            crate::leanh::lean_dec(v_ctors_4875_);
                            crate::leanh::lean_dec_ref(v_env_4865_);
                            v___x_4879_ = crate::leanh::lean_box(0);
                            return v___x_4879_;
                        } else {
                            if crate::leanh::lean_obj_tag(v_ctors_4875_) == 1 {
                                v_tail_4880_ = crate::leanh::lean_ctor_get(v_ctors_4875_, 1);
                                if crate::leanh::lean_obj_tag(v_tail_4880_) == 0 {
                                    if v_isRec_4876_ == 0 {
                                        v_head_4881_ =
                                            crate::leanh::lean_ctor_get(v_ctors_4875_, 0);
                                        crate::leanh::lean_inc(v_head_4881_);
                                        crate::leanh::lean_dec_ref_known(v_ctors_4875_, 2);
                                        v___x_4882_ = l_Lean_Environment_find_x3f(
                                            v_env_4865_,
                                            v_head_4881_,
                                            v_isRec_4876_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_4882_) == 1 {
                                            v_val_4883_ =
                                                crate::leanh::lean_ctor_get(v___x_4882_, 0);
                                            v_isSharedCheck_4891_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4882_))
                                                    as u8;
                                            if v_isSharedCheck_4891_ == 0 {
                                                v___x_4885_ = v___x_4882_;
                                                v_isShared_4886_ = v_isSharedCheck_4891_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_4883_);
                                                crate::leanh::lean_dec(v___x_4882_);
                                                v___x_4885_ = crate::leanh::lean_box(0);
                                                v_isShared_4886_ = v_isSharedCheck_4891_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_4882_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_ctors_4875_, 2);
                                        crate::leanh::lean_dec_ref(v_env_4865_);
                                        v___x_4892_ = crate::leanh::lean_box(0);
                                        return v___x_4892_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_ctors_4875_, 2);
                                    crate::leanh::lean_dec_ref(v_env_4865_);
                                    v___x_4893_ = crate::leanh::lean_box(0);
                                    return v___x_4893_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_ctors_4875_);
                                crate::leanh::lean_dec_ref(v_env_4865_);
                                v___x_4894_ = crate::leanh::lean_box(0);
                                return v___x_4894_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4872_);
                        crate::leanh::lean_dec_ref(v_env_4865_);
                        v___x_4895_ = crate::leanh::lean_box(0);
                        return v___x_4895_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4871_);
                    crate::leanh::lean_dec_ref(v_env_4865_);
                    v___x_4896_ = crate::leanh::lean_box(0);
                    return v___x_4896_;
                }
            }
            1 => {
                v___x_4868_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_getNonRecStructureCtor_x3f___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_getNonRecStructureCtor_x3f___closed__1_once),
                    _init_l_Lean_getNonRecStructureCtor_x3f___closed__1,
                );
                v___x_4869_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_4868_);
                return v___x_4869_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_4883_) == 6 {
                    v_val_4887_ = crate::leanh::lean_ctor_get(v_val_4883_, 0);
                    crate::leanh::lean_inc_ref(v_val_4887_);
                    crate::leanh::lean_dec_ref_known(v_val_4883_, 1);
                    if v_isShared_4886_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4885_, 0, v_val_4887_);
                        v___x_4889_ = v___x_4885_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_val_4887_);
                        v___x_4889_ = v_reuseFailAlloc_4890_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4885_);
                    crate::leanh::lean_dec(v_val_4883_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_4889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getNonRecStructureNumFields(
    mut v_env_4897_: *mut crate::leanh::LeanObject,
    mut v_constName_4898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4899_ = 0;
    crate::leanh::lean_inc_ref(v_env_4897_);
    v___x_4900_ = l_Lean_Environment_find_x3f(v_env_4897_, v_constName_4898_, v___x_4899_);
    if crate::leanh::lean_obj_tag(v___x_4900_) == 1 {
        let mut v_val_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4901_ = crate::leanh::lean_ctor_get(v___x_4900_, 0);
        crate::leanh::lean_inc(v_val_4901_);
        crate::leanh::lean_dec_ref_known(v___x_4900_, 1);
        if crate::leanh::lean_obj_tag(v_val_4901_) == 5 {
            let mut v_val_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_numIndices_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ctors_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isRec_4905_: u8 = 0;
            let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4907_: u8 = 0;
            v_val_4902_ = crate::leanh::lean_ctor_get(v_val_4901_, 0);
            crate::leanh::lean_inc_ref(v_val_4902_);
            crate::leanh::lean_dec_ref_known(v_val_4901_, 1);
            v_numIndices_4903_ = crate::leanh::lean_ctor_get(v_val_4902_, 2);
            crate::leanh::lean_inc(v_numIndices_4903_);
            v_ctors_4904_ = crate::leanh::lean_ctor_get(v_val_4902_, 4);
            crate::leanh::lean_inc(v_ctors_4904_);
            v_isRec_4905_ = crate::leanh::lean_ctor_get_uint8(
                v_val_4902_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
            );
            crate::leanh::lean_dec_ref(v_val_4902_);
            v___x_4906_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_4907_ = lean_nat_dec_eq(v_numIndices_4903_, v___x_4906_);
            crate::leanh::lean_dec(v_numIndices_4903_);
            if v___x_4907_ == 0 {
                crate::leanh::lean_dec(v_ctors_4904_);
                crate::leanh::lean_dec_ref(v_env_4897_);
                return v___x_4906_;
            } else {
                if crate::leanh::lean_obj_tag(v_ctors_4904_) == 1 {
                    let mut v_tail_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_tail_4908_ = crate::leanh::lean_ctor_get(v_ctors_4904_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_4908_) == 0 {
                        if v_isRec_4905_ == 0 {
                            let mut v_head_4909_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4910_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_head_4909_ = crate::leanh::lean_ctor_get(v_ctors_4904_, 0);
                            crate::leanh::lean_inc(v_head_4909_);
                            crate::leanh::lean_dec_ref_known(v_ctors_4904_, 2);
                            v___x_4910_ = l_Lean_Environment_find_x3f(
                                v_env_4897_,
                                v_head_4909_,
                                v_isRec_4905_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4910_) == 1 {
                                let mut v_val_4911_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_val_4911_ = crate::leanh::lean_ctor_get(v___x_4910_, 0);
                                crate::leanh::lean_inc(v_val_4911_);
                                crate::leanh::lean_dec_ref_known(v___x_4910_, 1);
                                if crate::leanh::lean_obj_tag(v_val_4911_) == 6 {
                                    let mut v_val_4912_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_numFields_4913_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_val_4912_ = crate::leanh::lean_ctor_get(v_val_4911_, 0);
                                    crate::leanh::lean_inc_ref(v_val_4912_);
                                    crate::leanh::lean_dec_ref_known(v_val_4911_, 1);
                                    v_numFields_4913_ = crate::leanh::lean_ctor_get(v_val_4912_, 4);
                                    crate::leanh::lean_inc(v_numFields_4913_);
                                    crate::leanh::lean_dec_ref(v_val_4912_);
                                    return v_numFields_4913_;
                                } else {
                                    crate::leanh::lean_dec(v_val_4911_);
                                    return v___x_4906_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4910_);
                                return v___x_4906_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_ctors_4904_, 2);
                            crate::leanh::lean_dec_ref(v_env_4897_);
                            return v___x_4906_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_ctors_4904_, 2);
                        crate::leanh::lean_dec_ref(v_env_4897_);
                        return v___x_4906_;
                    }
                } else {
                    crate::leanh::lean_dec(v_ctors_4904_);
                    crate::leanh::lean_dec_ref(v_env_4897_);
                    return v___x_4906_;
                }
            }
        } else {
            let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_4901_);
            crate::leanh::lean_dec_ref(v_env_4897_);
            v___x_4914_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4914_;
        }
    } else {
        let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4900_);
        crate::leanh::lean_dec_ref(v_env_4897_);
        v___x_4915_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4915_;
    }
}
pub unsafe fn _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4916_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4916_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4917_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureResolutionState_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedStructureResolutionState_default___closed__0_once
        ),
        _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0,
    );
    v___x_4918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4918_, 0, v___x_4917_);
    return v___x_4918_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureResolutionState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureResolutionState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedStructureResolutionState_default___closed__1_once
        ),
        _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1,
    );
    return v___x_4919_;
}
pub unsafe fn _init_l_Lean_instInhabitedStructureResolutionState() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l_Lean_instInhabitedStructureResolutionState_default;
    return v___x_4920_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(
    mut v___x_4921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4921_);
    return v___x_4923_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(
    mut v___x_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4926_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_4924_);
    return v_res_4926_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedStructureResolutionState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedStructureResolutionState_default___closed__1_once
        ),
        _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1,
    );
    v___f_4928_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_4928_, 0, v___x_4927_);
    return v___f_4928_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once), _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
    v___x_4931_ = crate::leanh::lean_box(0);
    v___x_4932_ = crate::leanh::lean_box(1);
    v___x_4933_ = l_Lean_registerEnvExtension___redArg(v___f_4930_, v___x_4931_, v___x_4932_);
    return v___x_4933_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(
    mut v_a_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4935_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
    return v_res_4935_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(
    mut v_env_4936_: *mut crate::leanh::LeanObject,
    mut v_structName_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4938_ = l_Lean_structureResolutionExt;
    v_asyncMode_4939_ = crate::leanh::lean_ctor_get(v___x_4938_, 2);
    v___x_4940_ = l_Lean_instInhabitedStructureResolutionState_default;
    v___x_4941_ = crate::leanh::lean_box(0);
    v___x_4942_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4940_,
        v___x_4938_,
        v_env_4936_,
        v_asyncMode_4939_,
        v___x_4941_,
    );
    v___x_4943_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(
            v___x_4942_,
            v_structName_4937_,
        );
    crate::leanh::lean_dec(v___x_4942_);
    return v___x_4943_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(
    mut v_env_4944_: *mut crate::leanh::LeanObject,
    mut v_structName_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4946_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(
        v_env_4944_,
        v_structName_4945_,
    );
    crate::leanh::lean_dec(v_structName_4945_);
    return v_res_4946_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(
    mut v___x_4947_: *mut crate::leanh::LeanObject,
    mut v___x_4948_: *mut crate::leanh::LeanObject,
    mut v_structName_4949_: *mut crate::leanh::LeanObject,
    mut v_resolutionOrder_4950_: *mut crate::leanh::LeanObject,
    mut v_s_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4952_ = l_Lean_PersistentHashMap_insert___redArg(
        v___x_4947_,
        v___x_4948_,
        v_s_4951_,
        v_structName_4949_,
        v_resolutionOrder_4950_,
    );
    return v___x_4952_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(
    mut v___f_4953_: *mut crate::leanh::LeanObject,
    mut v_env_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = l_Lean_structureResolutionExt;
    v_asyncMode_4956_ = crate::leanh::lean_ctor_get(v___x_4955_, 2);
    v___x_4957_ = crate::leanh::lean_box(0);
    v___x_4958_ = l_Lean_EnvExtension_modifyState___redArg(
        v___x_4955_,
        v_env_4954_,
        v___f_4953_,
        v_asyncMode_4956_,
        v___x_4957_,
    );
    return v___x_4958_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(
    mut v_inst_4959_: *mut crate::leanh::LeanObject,
    mut v_structName_4960_: *mut crate::leanh::LeanObject,
    mut v_resolutionOrder_4961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_4962_ = crate::leanh::lean_ctor_get(v_inst_4959_, 1);
    crate::leanh::lean_inc(v_modifyEnv_4962_);
    crate::leanh::lean_dec_ref(v_inst_4959_);
    v___x_4963_ = l_Lean_setStructureParents___redArg___closed__0;
    v___x_4964_ = l_Lean_setStructureParents___redArg___closed__1;
    v___f_4965_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4965_, 0, v___x_4963_);
    crate::leanh::lean_closure_set(v___f_4965_, 1, v___x_4964_);
    crate::leanh::lean_closure_set(v___f_4965_, 2, v_structName_4960_);
    crate::leanh::lean_closure_set(v___f_4965_, 3, v_resolutionOrder_4961_);
    v___f_4966_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4966_, 0, v___f_4965_);
    v___x_4967_ = crate::leanh::lean_apply_1(v_modifyEnv_4962_, v___f_4966_);
    return v___x_4967_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(
    mut v_m_4968_: *mut crate::leanh::LeanObject,
    mut v_inst_4969_: *mut crate::leanh::LeanObject,
    mut v_structName_4970_: *mut crate::leanh::LeanObject,
    mut v_resolutionOrder_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(
        v_inst_4969_,
        v_structName_4970_,
        v_resolutionOrder_4971_,
    );
    return v___x_4972_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(
    mut v___x_4990_: *mut crate::leanh::LeanObject,
    mut v_resOrders_4991_: *mut crate::leanh::LeanObject,
    mut v___x_4992_: *mut crate::leanh::LeanObject,
    mut v_toPure_4993_: *mut crate::leanh::LeanObject,
    mut v_____s_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_4999_: u8 = 0;
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_unused_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4995_ = crate::leanh::lean_ctor_get(v_____s_4994_, 0);
                v_isSharedCheck_5010_ = (!crate::leanh::lean_is_exclusive(v_____s_4994_)) as u8;
                if v_isSharedCheck_5010_ == 0 {
                    v_unused_5011_ = crate::leanh::lean_ctor_get(v_____s_4994_, 1);
                    crate::leanh::lean_dec(v_unused_5011_);
                    v___x_4997_ = v_____s_4994_;
                    v_isShared_4998_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4995_);
                    crate::leanh::lean_dec(v_____s_4994_);
                    v___x_4997_ = crate::leanh::lean_box(0);
                    v_isShared_4998_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_fst_4995_) == 0 {
                    v___x_4999_ = 0;
                    v___x_5000_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5001_ =
                        lean_array_get_borrowed(v___x_4990_, v_resOrders_4991_, v___x_5000_);
                    v___x_5002_ = lean_array_get_borrowed(v___x_4992_, v___x_5001_, v___x_5000_);
                    v___x_5003_ = crate::leanh::lean_box((v___x_4999_) as usize);
                    crate::leanh::lean_inc(v___x_5002_);
                    if v_isShared_4998_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4997_, 1, v___x_5002_);
                        crate::leanh::lean_ctor_set(v___x_4997_, 0, v___x_5003_);
                        v___x_5005_ = v___x_4997_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5007_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5003_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 1, v___x_5002_);
                        v___x_5005_ = v_reuseFailAlloc_5007_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4997_);
                    v_val_5008_ = crate::leanh::lean_ctor_get(v_fst_4995_, 0);
                    crate::leanh::lean_inc(v_val_5008_);
                    crate::leanh::lean_dec_ref_known(v_fst_4995_, 1);
                    v___x_5009_ = crate::leanh::lean_apply_2(
                        v_toPure_4993_,
                        crate::leanh::lean_box(0),
                        v_val_5008_,
                    );
                    return v___x_5009_;
                }
            }
            2 => {
                v___x_5006_ = crate::leanh::lean_apply_2(
                    v_toPure_4993_,
                    crate::leanh::lean_box(0),
                    v___x_5005_,
                );
                return v___x_5006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(
    mut v___x_5012_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5013_: *mut crate::leanh::LeanObject,
    mut v___x_5014_: *mut crate::leanh::LeanObject,
    mut v_toPure_5015_: *mut crate::leanh::LeanObject,
    mut v_____s_5016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5017_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_5012_, v_resOrders_5013_, v___x_5014_, v_toPure_5015_, v_____s_5016_);
    crate::leanh::lean_dec(v___x_5014_);
    crate::leanh::lean_dec_ref(v_resOrders_5013_);
    crate::leanh::lean_dec_ref(v___x_5012_);
    return v_res_5017_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(
    mut v_toPure_5018_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5020_ = crate::leanh::lean_apply_2(
        v_toPure_5018_,
        crate::leanh::lean_box(0),
        v_____do__lift_5019_,
    );
    return v___x_5020_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(
    mut v___x_5021_: *mut crate::leanh::LeanObject,
    mut v_toPure_5022_: *mut crate::leanh::LeanObject,
    mut v___x_5023_: *mut crate::leanh::LeanObject,
    mut v_____s_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5028_: u8 = 0;
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5040_: u8 = 0;
    let mut v_unused_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_unused_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5025_ = crate::leanh::lean_ctor_get(v_____s_5024_, 0);
                v_isSharedCheck_5043_ = (!crate::leanh::lean_is_exclusive(v_____s_5024_)) as u8;
                if v_isSharedCheck_5043_ == 0 {
                    v_unused_5044_ = crate::leanh::lean_ctor_get(v_____s_5024_, 1);
                    crate::leanh::lean_dec(v_unused_5044_);
                    v___x_5027_ = v_____s_5024_;
                    v_isShared_5028_ = v_isSharedCheck_5043_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5025_);
                    crate::leanh::lean_dec(v_____s_5024_);
                    v___x_5027_ = crate::leanh::lean_box(0);
                    v_isShared_5028_ = v_isSharedCheck_5043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_fst_5025_) == 0 {
                    crate::leanh::lean_del_object(v___x_5027_);
                    v___x_5029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5029_, 0, v___x_5021_);
                    v___x_5030_ = crate::leanh::lean_apply_2(
                        v_toPure_5022_,
                        crate::leanh::lean_box(0),
                        v___x_5029_,
                    );
                    return v___x_5030_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5021_);
                    crate::leanh::lean_inc_ref(v_fst_5025_);
                    if v_isShared_5028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5027_, 1, v___x_5023_);
                        v___x_5032_ = v___x_5027_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_fst_5025_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 1, v___x_5023_);
                        v___x_5032_ = v_reuseFailAlloc_5042_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_isSharedCheck_5040_ = (!crate::leanh::lean_is_exclusive(v_fst_5025_)) as u8;
                if v_isSharedCheck_5040_ == 0 {
                    v_unused_5041_ = crate::leanh::lean_ctor_get(v_fst_5025_, 0);
                    crate::leanh::lean_dec(v_unused_5041_);
                    v___x_5034_ = v_fst_5025_;
                    v_isShared_5035_ = v_isSharedCheck_5040_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5025_);
                    v___x_5034_ = crate::leanh::lean_box(0);
                    v_isShared_5035_ = v_isSharedCheck_5040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5034_, 0);
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5032_);
                    v___x_5037_ = v___x_5034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5032_);
                    v___x_5037_ = v_reuseFailAlloc_5039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5038_ = crate::leanh::lean_apply_2(
                    v_toPure_5022_,
                    crate::leanh::lean_box(0),
                    v___x_5037_,
                );
                return v___x_5038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(
    mut v_toPure_5045_: *mut crate::leanh::LeanObject,
    mut v_next_5046_: *mut crate::leanh::LeanObject,
    mut v_G_5047_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_5048_) == 0 {
        let mut v_a_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_5047_);
        v_a_5049_ = crate::leanh::lean_ctor_get(v_____do__lift_5048_, 0);
        crate::leanh::lean_inc(v_a_5049_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5048_, 1);
        v___x_5050_ =
            crate::leanh::lean_apply_2(v_toPure_5045_, crate::leanh::lean_box(0), v_a_5049_);
        return v___x_5050_;
    } else {
        let mut v_a_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_5045_);
        v_a_5051_ = crate::leanh::lean_ctor_get(v_____do__lift_5048_, 0);
        crate::leanh::lean_inc(v_a_5051_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5048_, 1);
        v___x_5052_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5053_ = lean_nat_add(v_next_5046_, v___x_5052_);
        v___x_5054_ = crate::leanh::lean_apply_4(
            v_G_5047_,
            v___x_5053_,
            v_a_5051_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5054_;
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(
    mut v_toPure_5055_: *mut crate::leanh::LeanObject,
    mut v_next_5056_: *mut crate::leanh::LeanObject,
    mut v_G_5057_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5059_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_5055_, v_next_5056_, v_G_5057_, v_____do__lift_5058_);
    crate::leanh::lean_dec(v_next_5056_);
    return v_res_5059_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(
    mut v___x_5060_: *mut crate::leanh::LeanObject,
    mut v_v_5061_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5062_: u8 = 0;
    v___x_5062_ = lean_name_eq(v_v_5061_, v___x_5060_);
    return v___x_5062_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(
    mut v___x_5063_: *mut crate::leanh::LeanObject,
    mut v_v_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5065_: u8 = 0;
    let mut v_r_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5065_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_5063_, v_v_5064_);
    crate::leanh::lean_dec(v_v_5064_);
    crate::leanh::lean_dec(v___x_5063_);
    v_r_5066_ = crate::leanh::lean_box((v_res_5065_) as usize);
    return v_r_5066_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(
    mut v___x_5086_: u8,
    mut v___f_5087_: *mut crate::leanh::LeanObject,
    mut v_resOrder_5088_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: u8 = 0;
    let mut v___y_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: usize = 0;
    let mut v___x_5101_: usize = 0;
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5089_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5090_ = lean_array_get_size(v_resOrder_5088_);
                v___x_5091_ =
                    l_Array_toSubarray___redArg(v_resOrder_5088_, v___x_5089_, v___x_5090_);
                v___x_5092_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v_array_5093_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                crate::leanh::lean_inc_ref(v_array_5093_);
                v_start_5094_ = crate::leanh::lean_ctor_get(v___x_5091_, 1);
                crate::leanh::lean_inc(v_start_5094_);
                v_stop_5095_ = crate::leanh::lean_ctor_get(v___x_5091_, 2);
                crate::leanh::lean_inc(v_stop_5095_);
                crate::leanh::lean_dec_ref(v___x_5091_);
                v___x_5096_ = lean_nat_dec_lt(v_start_5094_, v_stop_5095_);
                if v___x_5096_ == 0 {
                    crate::leanh::lean_dec(v_stop_5095_);
                    crate::leanh::lean_dec(v_start_5094_);
                    crate::leanh::lean_dec_ref(v_array_5093_);
                    crate::leanh::lean_dec_ref(v___f_5087_);
                    return v___x_5086_;
                } else {
                    v___x_5105_ = lean_array_get_size(v_array_5093_);
                    v___x_5106_ = lean_nat_dec_le(v_stop_5095_, v___x_5105_);
                    if v___x_5106_ == 0 {
                        crate::leanh::lean_dec(v_stop_5095_);
                        v___y_5098_ = v___x_5105_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5098_ = v_stop_5095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5099_ = lean_nat_dec_lt(v_start_5094_, v___y_5098_);
                if v___x_5099_ == 0 {
                    crate::leanh::lean_dec(v___y_5098_);
                    crate::leanh::lean_dec(v_start_5094_);
                    crate::leanh::lean_dec_ref(v_array_5093_);
                    crate::leanh::lean_dec_ref(v___f_5087_);
                    return v___x_5096_;
                } else {
                    v___x_5100_ = lean_usize_of_nat(v_start_5094_);
                    crate::leanh::lean_dec(v_start_5094_);
                    v___x_5101_ = lean_usize_of_nat(v___y_5098_);
                    crate::leanh::lean_dec(v___y_5098_);
                    v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5092_,
                        v___f_5087_,
                        v_array_5093_,
                        v___x_5100_,
                        v___x_5101_,
                    );
                    v___x_5103_ = (crate::leanh::lean_unbox(v___x_5102_) as u8);
                    crate::leanh::lean_dec(v___x_5102_);
                    if v___x_5103_ == 0 {
                        return v___x_5099_;
                    } else {
                        v___x_5104_ = 0;
                        return v___x_5104_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(
    mut v___x_5107_: *mut crate::leanh::LeanObject,
    mut v___f_5108_: *mut crate::leanh::LeanObject,
    mut v_resOrder_5109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715__boxed_5110_: u8 = 0;
    let mut v_res_5111_: u8 = 0;
    let mut v_r_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715__boxed_5110_ = (crate::leanh::lean_unbox(v___x_5107_) as u8);
    v_res_5111_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_5110_, v___f_5108_, v_resOrder_5109_);
    v_r_5112_ = crate::leanh::lean_box((v_res_5111_) as usize);
    return v_r_5112_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(
    mut v___f_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: u8,
    mut v_v_5115_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    v___x_5116_ = crate::leanh::lean_apply_1(v___f_5113_, v_v_5115_);
    v___x_5117_ = (crate::leanh::lean_unbox(v___x_5116_) as u8);
    if v___x_5117_ == 0 {
        return v___y_5114_;
    } else {
        let mut v___x_5118_: u8 = 0;
        v___x_5118_ = 0;
        return v___x_5118_;
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(
    mut v___f_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v_v_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1771__boxed_5122_: u8 = 0;
    let mut v_res_5123_: u8 = 0;
    let mut v_r_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1771__boxed_5122_ = (crate::leanh::lean_unbox(v___y_5120_) as u8);
    v_res_5123_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_5119_, v___y_1771__boxed_5122_, v_v_5121_);
    v_r_5124_ = crate::leanh::lean_box((v_res_5123_) as usize);
    return v_r_5124_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(
    mut v___f_5125_: *mut crate::leanh::LeanObject,
    mut v___x_5126_: u8,
    mut v_v_5127_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: u8 = 0;
    v___x_5128_ = crate::leanh::lean_apply_1(v___f_5125_, v_v_5127_);
    v___x_5129_ = (crate::leanh::lean_unbox(v___x_5128_) as u8);
    if v___x_5129_ == 0 {
        return v___x_5126_;
    } else {
        let mut v___x_5130_: u8 = 0;
        v___x_5130_ = 0;
        return v___x_5130_;
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(
    mut v___f_5131_: *mut crate::leanh::LeanObject,
    mut v___x_5132_: *mut crate::leanh::LeanObject,
    mut v_v_5133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783__boxed_5134_: u8 = 0;
    let mut v_res_5135_: u8 = 0;
    let mut v_r_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783__boxed_5134_ = (crate::leanh::lean_unbox(v___x_5132_) as u8);
    v_res_5135_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_5131_, v___x_1783__boxed_5134_, v_v_5133_);
    v_r_5136_ = crate::leanh::lean_box((v_res_5135_) as usize);
    return v_r_5136_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(
    mut v___x_5137_: *mut crate::leanh::LeanObject,
    mut v_toPure_5138_: *mut crate::leanh::LeanObject,
    mut v___x_5139_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5140_: *mut crate::leanh::LeanObject,
    mut v___x_5141_: *mut crate::leanh::LeanObject,
    mut v___x_5142_: *mut crate::leanh::LeanObject,
    mut v_toBind_5143_: *mut crate::leanh::LeanObject,
    mut v___f_5144_: *mut crate::leanh::LeanObject,
    mut v___x_5145_: *mut crate::leanh::LeanObject,
    mut v_next_5146_: *mut crate::leanh::LeanObject,
    mut v___x_5147_: *mut crate::leanh::LeanObject,
    mut v_next_5148_: *mut crate::leanh::LeanObject,
    mut v_acc_5149_: *mut crate::leanh::LeanObject,
    mut v_h_5150_: *mut crate::leanh::LeanObject,
    mut v_G_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: u8 = 0;
    let mut v___x_5184_: usize = 0;
    let mut v___x_5185_: usize = 0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: u8 = 0;
    let mut v___f_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5192_: u8 = 0;
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: u8 = 0;
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___x_5204_: u8 = 0;
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: u8 = 0;
    let mut v___x_5210_: usize = 0;
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5152_ = lean_nat_dec_lt(v_next_5148_, v___x_5137_);
                if v___x_5152_ == 0 {
                    crate::leanh::lean_dec(v_G_5151_);
                    crate::leanh::lean_dec(v_next_5148_);
                    crate::leanh::lean_dec_ref(v___x_5145_);
                    crate::leanh::lean_dec(v___f_5144_);
                    crate::leanh::lean_dec(v_toBind_5143_);
                    crate::leanh::lean_dec(v___x_5142_);
                    crate::leanh::lean_dec_ref(v_resOrders_5140_);
                    crate::leanh::lean_dec(v___x_5137_);
                    v___x_5153_ = crate::leanh::lean_apply_2(
                        v_toPure_5138_,
                        crate::leanh::lean_box(0),
                        v_acc_5149_,
                    );
                    return v___x_5153_;
                } else {
                    crate::leanh::lean_dec_ref(v_acc_5149_);
                    v___x_5154_ =
                        lean_array_get_borrowed(v___x_5139_, v_resOrders_5140_, v_next_5148_);
                    v___x_5155_ = lean_array_get(v___x_5141_, v___x_5154_, v___x_5142_);
                    crate::leanh::lean_inc_n(v_next_5148_, 2);
                    crate::leanh::lean_inc(v___x_5142_);
                    crate::leanh::lean_inc_ref(v_resOrders_5140_);
                    v___x_5156_ =
                        l_Array_toSubarray___redArg(v_resOrders_5140_, v___x_5142_, v_next_5148_);
                    v___x_5157_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                    v_array_5158_ = crate::leanh::lean_ctor_get(v___x_5156_, 0);
                    crate::leanh::lean_inc_ref(v_array_5158_);
                    v_start_5159_ = crate::leanh::lean_ctor_get(v___x_5156_, 1);
                    crate::leanh::lean_inc(v_start_5159_);
                    v_stop_5160_ = crate::leanh::lean_ctor_get(v___x_5156_, 2);
                    crate::leanh::lean_inc(v_stop_5160_);
                    crate::leanh::lean_dec_ref(v___x_5156_);
                    crate::leanh::lean_inc(v_toPure_5138_);
                    v___f_5161_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                    crate::leanh::lean_closure_set(v___f_5161_, 0, v_toPure_5138_);
                    crate::leanh::lean_closure_set(v___f_5161_, 1, v_next_5148_);
                    crate::leanh::lean_closure_set(v___f_5161_, 2, v_G_5151_);
                    crate::leanh::lean_inc(v___x_5155_);
                    v___f_5188_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_5188_, 0, v___x_5155_);
                    v___x_5189_ = crate::leanh::lean_box((v___x_5152_) as usize);
                    v___f_5190_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5190_, 0, v___x_5189_);
                    crate::leanh::lean_closure_set(v___f_5190_, 1, v___f_5188_);
                    v___x_5204_ = lean_nat_dec_lt(v_start_5159_, v_stop_5160_);
                    if v___x_5204_ == 0 {
                        crate::leanh::lean_dec(v_stop_5160_);
                        crate::leanh::lean_dec(v_start_5159_);
                        crate::leanh::lean_dec_ref(v_array_5158_);
                        v___y_5192_ = v___x_5152_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5205_ = crate::leanh::lean_box((v___x_5152_) as usize);
                        crate::leanh::lean_inc_ref(v___f_5190_);
                        v___f_5206_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_5206_, 0, v___f_5190_);
                        crate::leanh::lean_closure_set(v___f_5206_, 1, v___x_5205_);
                        v___x_5214_ = lean_array_get_size(v_array_5158_);
                        v___x_5215_ = lean_nat_dec_le(v_stop_5160_, v___x_5214_);
                        if v___x_5215_ == 0 {
                            crate::leanh::lean_dec(v_stop_5160_);
                            v___y_5208_ = v___x_5214_;
                            state = 6;
                            continue;
                        } else {
                            v___y_5208_ = v_stop_5160_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toBind_5143_);
                v___x_5164_ = crate::leanh::lean_apply_4(
                    v_toBind_5143_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___y_5163_,
                    v___f_5144_,
                );
                v___x_5165_ = crate::leanh::lean_apply_4(
                    v_toBind_5143_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5164_,
                    v___f_5161_,
                );
                return v___x_5165_;
            }
            2 => {
                v___x_5167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5167_, 0, v___x_5145_);
                v___x_5168_ = crate::leanh::lean_apply_2(
                    v_toPure_5138_,
                    crate::leanh::lean_box(0),
                    v___x_5167_,
                );
                v___y_5163_ = v___x_5168_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5170_ = lean_nat_dec_eq(v_next_5146_, v___x_5142_);
                crate::leanh::lean_dec(v___x_5142_);
                v___x_5171_ = crate::leanh::lean_box((v___x_5170_) as usize);
                v___x_5172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5172_, 0, v___x_5171_);
                crate::leanh::lean_ctor_set(v___x_5172_, 1, v___x_5155_);
                v___x_5173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5173_, 0, v___x_5172_);
                v___x_5174_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5174_, 0, v___x_5173_);
                crate::leanh::lean_ctor_set(v___x_5174_, 1, v___x_5147_);
                v___x_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5175_, 0, v___x_5174_);
                v___x_5176_ = crate::leanh::lean_apply_2(
                    v_toPure_5138_,
                    crate::leanh::lean_box(0),
                    v___x_5175_,
                );
                v___y_5163_ = v___x_5176_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5183_ = lean_nat_dec_lt(v___y_5181_, v___y_5182_);
                if v___x_5183_ == 0 {
                    crate::leanh::lean_dec(v___y_5182_);
                    crate::leanh::lean_dec(v___y_5181_);
                    crate::leanh::lean_dec_ref(v___y_5180_);
                    crate::leanh::lean_dec_ref(v___y_5179_);
                    crate::leanh::lean_dec_ref(v___y_5178_);
                    crate::leanh::lean_dec_ref(v___x_5145_);
                    state = 3;
                    continue;
                } else {
                    v___x_5184_ = lean_usize_of_nat(v___y_5181_);
                    crate::leanh::lean_dec(v___y_5181_);
                    v___x_5185_ = lean_usize_of_nat(v___y_5182_);
                    crate::leanh::lean_dec(v___y_5182_);
                    v___x_5186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___y_5180_,
                        v___y_5178_,
                        v___y_5179_,
                        v___x_5184_,
                        v___x_5185_,
                    );
                    v___x_5187_ = (crate::leanh::lean_unbox(v___x_5186_) as u8);
                    crate::leanh::lean_dec(v___x_5186_);
                    if v___x_5187_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5145_);
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5155_);
                        crate::leanh::lean_dec(v___x_5142_);
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_5192_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_5190_);
                    crate::leanh::lean_dec(v___x_5155_);
                    crate::leanh::lean_dec(v_next_5148_);
                    crate::leanh::lean_dec(v___x_5142_);
                    crate::leanh::lean_dec_ref(v_resOrders_5140_);
                    crate::leanh::lean_dec(v___x_5137_);
                    state = 2;
                    continue;
                } else {
                    v___x_5193_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5194_ = lean_nat_add(v_next_5148_, v___x_5193_);
                    crate::leanh::lean_dec(v_next_5148_);
                    v___x_5195_ =
                        l_Array_toSubarray___redArg(v_resOrders_5140_, v___x_5194_, v___x_5137_);
                    v_array_5196_ = crate::leanh::lean_ctor_get(v___x_5195_, 0);
                    crate::leanh::lean_inc_ref(v_array_5196_);
                    v_start_5197_ = crate::leanh::lean_ctor_get(v___x_5195_, 1);
                    crate::leanh::lean_inc(v_start_5197_);
                    v_stop_5198_ = crate::leanh::lean_ctor_get(v___x_5195_, 2);
                    crate::leanh::lean_inc(v_stop_5198_);
                    crate::leanh::lean_dec_ref(v___x_5195_);
                    v___x_5199_ = lean_nat_dec_lt(v_start_5197_, v_stop_5198_);
                    if v___x_5199_ == 0 {
                        crate::leanh::lean_dec(v_stop_5198_);
                        crate::leanh::lean_dec(v_start_5197_);
                        crate::leanh::lean_dec_ref(v_array_5196_);
                        crate::leanh::lean_dec_ref(v___f_5190_);
                        crate::leanh::lean_dec_ref(v___x_5145_);
                        state = 3;
                        continue;
                    } else {
                        v___x_5200_ = crate::leanh::lean_box((v___y_5192_) as usize);
                        v___f_5201_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_5201_, 0, v___f_5190_);
                        crate::leanh::lean_closure_set(v___f_5201_, 1, v___x_5200_);
                        v___x_5202_ = lean_array_get_size(v_array_5196_);
                        v___x_5203_ = lean_nat_dec_le(v_stop_5198_, v___x_5202_);
                        if v___x_5203_ == 0 {
                            crate::leanh::lean_dec(v_stop_5198_);
                            v___y_5178_ = v___f_5201_;
                            v___y_5179_ = v_array_5196_;
                            v___y_5180_ = v___x_5157_;
                            v___y_5181_ = v_start_5197_;
                            v___y_5182_ = v___x_5202_;
                            state = 4;
                            continue;
                        } else {
                            v___y_5178_ = v___f_5201_;
                            v___y_5179_ = v_array_5196_;
                            v___y_5180_ = v___x_5157_;
                            v___y_5181_ = v_start_5197_;
                            v___y_5182_ = v_stop_5198_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_5209_ = lean_nat_dec_lt(v_start_5159_, v___y_5208_);
                if v___x_5209_ == 0 {
                    crate::leanh::lean_dec(v___y_5208_);
                    crate::leanh::lean_dec_ref(v___f_5206_);
                    crate::leanh::lean_dec(v_start_5159_);
                    crate::leanh::lean_dec_ref(v_array_5158_);
                    v___y_5192_ = v___x_5204_;
                    state = 5;
                    continue;
                } else {
                    v___x_5210_ = lean_usize_of_nat(v_start_5159_);
                    crate::leanh::lean_dec(v_start_5159_);
                    v___x_5211_ = lean_usize_of_nat(v___y_5208_);
                    crate::leanh::lean_dec(v___y_5208_);
                    v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5157_,
                        v___f_5206_,
                        v_array_5158_,
                        v___x_5210_,
                        v___x_5211_,
                    );
                    v___x_5213_ = (crate::leanh::lean_unbox(v___x_5212_) as u8);
                    crate::leanh::lean_dec(v___x_5212_);
                    if v___x_5213_ == 0 {
                        v___y_5192_ = v___x_5209_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5190_);
                        crate::leanh::lean_dec(v___x_5155_);
                        crate::leanh::lean_dec(v_next_5148_);
                        crate::leanh::lean_dec(v___x_5142_);
                        crate::leanh::lean_dec_ref(v_resOrders_5140_);
                        crate::leanh::lean_dec(v___x_5137_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(
    mut v___x_5216_: *mut crate::leanh::LeanObject,
    mut v_toPure_5217_: *mut crate::leanh::LeanObject,
    mut v___x_5218_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5219_: *mut crate::leanh::LeanObject,
    mut v___x_5220_: *mut crate::leanh::LeanObject,
    mut v___x_5221_: *mut crate::leanh::LeanObject,
    mut v_toBind_5222_: *mut crate::leanh::LeanObject,
    mut v___f_5223_: *mut crate::leanh::LeanObject,
    mut v___x_5224_: *mut crate::leanh::LeanObject,
    mut v_next_5225_: *mut crate::leanh::LeanObject,
    mut v___x_5226_: *mut crate::leanh::LeanObject,
    mut v_next_5227_: *mut crate::leanh::LeanObject,
    mut v_acc_5228_: *mut crate::leanh::LeanObject,
    mut v_h_5229_: *mut crate::leanh::LeanObject,
    mut v_G_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_5216_, v_toPure_5217_, v___x_5218_, v_resOrders_5219_, v___x_5220_, v___x_5221_, v_toBind_5222_, v___f_5223_, v___x_5224_, v_next_5225_, v___x_5226_, v_next_5227_, v_acc_5228_, v_h_5229_, v_G_5230_);
    crate::leanh::lean_dec(v_next_5225_);
    crate::leanh::lean_dec(v___x_5220_);
    crate::leanh::lean_dec_ref(v___x_5218_);
    return v_res_5231_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(
    mut v___x_5232_: *mut crate::leanh::LeanObject,
    mut v_toPure_5233_: *mut crate::leanh::LeanObject,
    mut v___x_5234_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5235_: *mut crate::leanh::LeanObject,
    mut v___x_5236_: *mut crate::leanh::LeanObject,
    mut v___x_5237_: *mut crate::leanh::LeanObject,
    mut v_toBind_5238_: *mut crate::leanh::LeanObject,
    mut v___f_5239_: *mut crate::leanh::LeanObject,
    mut v___x_5240_: *mut crate::leanh::LeanObject,
    mut v___x_5241_: *mut crate::leanh::LeanObject,
    mut v___f_5242_: *mut crate::leanh::LeanObject,
    mut v___f_5243_: *mut crate::leanh::LeanObject,
    mut v_next_5244_: *mut crate::leanh::LeanObject,
    mut v_acc_5245_: *mut crate::leanh::LeanObject,
    mut v_h_5246_: *mut crate::leanh::LeanObject,
    mut v_G_5247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5248_: u8 = 0;
    v___x_5248_ = lean_nat_dec_lt(v_next_5244_, v___x_5232_);
    if v___x_5248_ == 0 {
        let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_5247_);
        crate::leanh::lean_dec(v_next_5244_);
        crate::leanh::lean_dec(v___f_5243_);
        crate::leanh::lean_dec(v___f_5242_);
        crate::leanh::lean_dec_ref(v___x_5240_);
        crate::leanh::lean_dec(v___f_5239_);
        crate::leanh::lean_dec(v_toBind_5238_);
        crate::leanh::lean_dec(v___x_5237_);
        crate::leanh::lean_dec(v___x_5236_);
        crate::leanh::lean_dec_ref(v_resOrders_5235_);
        crate::leanh::lean_dec_ref(v___x_5234_);
        v___x_5249_ =
            crate::leanh::lean_apply_2(v_toPure_5233_, crate::leanh::lean_box(0), v_acc_5245_);
        return v___x_5249_;
    } else {
        let mut v___f_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_acc_5245_);
        crate::leanh::lean_inc(v_next_5244_);
        crate::leanh::lean_inc(v_toPure_5233_);
        v___f_5250_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
        crate::leanh::lean_closure_set(v___f_5250_, 0, v_toPure_5233_);
        crate::leanh::lean_closure_set(v___f_5250_, 1, v_next_5244_);
        crate::leanh::lean_closure_set(v___f_5250_, 2, v_G_5247_);
        v___x_5251_ = lean_nat_sub(v___x_5232_, v_next_5244_);
        crate::leanh::lean_inc_ref(v___x_5240_);
        crate::leanh::lean_inc_n(v_toBind_5238_, 3);
        crate::leanh::lean_inc(v___x_5237_);
        v___f_5252_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed as *mut core::ffi::c_void, 15, 11);
        crate::leanh::lean_closure_set(v___f_5252_, 0, v___x_5251_);
        crate::leanh::lean_closure_set(v___f_5252_, 1, v_toPure_5233_);
        crate::leanh::lean_closure_set(v___f_5252_, 2, v___x_5234_);
        crate::leanh::lean_closure_set(v___f_5252_, 3, v_resOrders_5235_);
        crate::leanh::lean_closure_set(v___f_5252_, 4, v___x_5236_);
        crate::leanh::lean_closure_set(v___f_5252_, 5, v___x_5237_);
        crate::leanh::lean_closure_set(v___f_5252_, 6, v_toBind_5238_);
        crate::leanh::lean_closure_set(v___f_5252_, 7, v___f_5239_);
        crate::leanh::lean_closure_set(v___f_5252_, 8, v___x_5240_);
        crate::leanh::lean_closure_set(v___f_5252_, 9, v_next_5244_);
        crate::leanh::lean_closure_set(v___f_5252_, 10, v___x_5241_);
        v___x_5253_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_5252_,
            v___x_5237_,
            v___x_5240_,
            crate::leanh::lean_box(0),
        );
        v___x_5254_ = crate::leanh::lean_apply_4(
            v_toBind_5238_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5253_,
            v___f_5242_,
        );
        v___x_5255_ = crate::leanh::lean_apply_4(
            v_toBind_5238_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5254_,
            v___f_5243_,
        );
        v___x_5256_ = crate::leanh::lean_apply_4(
            v_toBind_5238_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5255_,
            v___f_5250_,
        );
        return v___x_5256_;
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(
    mut v___x_5257_: *mut crate::leanh::LeanObject,
    mut v_toPure_5258_: *mut crate::leanh::LeanObject,
    mut v___x_5259_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5260_: *mut crate::leanh::LeanObject,
    mut v___x_5261_: *mut crate::leanh::LeanObject,
    mut v___x_5262_: *mut crate::leanh::LeanObject,
    mut v_toBind_5263_: *mut crate::leanh::LeanObject,
    mut v___f_5264_: *mut crate::leanh::LeanObject,
    mut v___x_5265_: *mut crate::leanh::LeanObject,
    mut v___x_5266_: *mut crate::leanh::LeanObject,
    mut v___f_5267_: *mut crate::leanh::LeanObject,
    mut v___f_5268_: *mut crate::leanh::LeanObject,
    mut v_next_5269_: *mut crate::leanh::LeanObject,
    mut v_acc_5270_: *mut crate::leanh::LeanObject,
    mut v_h_5271_: *mut crate::leanh::LeanObject,
    mut v_G_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5273_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_5257_, v_toPure_5258_, v___x_5259_, v_resOrders_5260_, v___x_5261_, v___x_5262_, v_toBind_5263_, v___f_5264_, v___x_5265_, v___x_5266_, v___f_5267_, v___f_5268_, v_next_5269_, v_acc_5270_, v_h_5271_, v_G_5272_);
    crate::leanh::lean_dec(v___x_5257_);
    return v_res_5273_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5274_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_5274_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(
    mut v_inst_5278_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5280_ = crate::leanh::lean_ctor_get(v_inst_5278_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5280_);
    v_toBind_5281_ = crate::leanh::lean_ctor_get(v_inst_5278_, 1);
    crate::leanh::lean_inc_n(v_toBind_5281_, 2);
    crate::leanh::lean_dec_ref(v_inst_5278_);
    v_toPure_5282_ = crate::leanh::lean_ctor_get(v_toApplicative_5280_, 1);
    crate::leanh::lean_inc_n(v_toPure_5282_, 4);
    crate::leanh::lean_dec_ref(v_toApplicative_5280_);
    v___x_5283_ = crate::leanh::lean_box(0);
    v___x_5284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once), _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
    v___x_5285_ = lean_array_get_size(v_resOrders_5279_);
    crate::leanh::lean_inc_ref(v_resOrders_5279_);
    v___f_5286_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_5286_, 0, v___x_5284_);
    crate::leanh::lean_closure_set(v___f_5286_, 1, v_resOrders_5279_);
    crate::leanh::lean_closure_set(v___f_5286_, 2, v___x_5283_);
    crate::leanh::lean_closure_set(v___f_5286_, 3, v_toPure_5282_);
    v___f_5287_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_5287_, 0, v_toPure_5282_);
    v___x_5288_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5289_ = crate::leanh::lean_box(0);
    v___x_5290_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1;
    v___f_5291_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_5291_, 0, v___x_5290_);
    crate::leanh::lean_closure_set(v___f_5291_, 1, v_toPure_5282_);
    crate::leanh::lean_closure_set(v___f_5291_, 2, v___x_5289_);
    crate::leanh::lean_inc_ref(v___f_5287_);
    v___f_5292_ = crate::leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed as *mut core::ffi::c_void, 16, 12);
    crate::leanh::lean_closure_set(v___f_5292_, 0, v___x_5285_);
    crate::leanh::lean_closure_set(v___f_5292_, 1, v_toPure_5282_);
    crate::leanh::lean_closure_set(v___f_5292_, 2, v___x_5284_);
    crate::leanh::lean_closure_set(v___f_5292_, 3, v_resOrders_5279_);
    crate::leanh::lean_closure_set(v___f_5292_, 4, v___x_5283_);
    crate::leanh::lean_closure_set(v___f_5292_, 5, v___x_5288_);
    crate::leanh::lean_closure_set(v___f_5292_, 6, v_toBind_5281_);
    crate::leanh::lean_closure_set(v___f_5292_, 7, v___f_5287_);
    crate::leanh::lean_closure_set(v___f_5292_, 8, v___x_5290_);
    crate::leanh::lean_closure_set(v___f_5292_, 9, v___x_5289_);
    crate::leanh::lean_closure_set(v___f_5292_, 10, v___f_5291_);
    crate::leanh::lean_closure_set(v___f_5292_, 11, v___f_5287_);
    v___x_5293_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_5292_,
        v___x_5288_,
        v___x_5290_,
        crate::leanh::lean_box(0),
    );
    v___x_5294_ = crate::leanh::lean_apply_4(
        v_toBind_5281_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5293_,
        v___f_5286_,
    );
    return v___x_5294_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(
    mut v_m_5295_: *mut crate::leanh::LeanObject,
    mut v_inst_5296_: *mut crate::leanh::LeanObject,
    mut v_resOrders_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5298_ =
        l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(
            v_inst_5296_,
            v_resOrders_5297_,
        );
    return v___x_5298_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__0(
    mut v_x_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structName_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_structName_5300_ = crate::leanh::lean_ctor_get(v_x_5299_, 0);
    crate::leanh::lean_inc(v_structName_5300_);
    return v_structName_5300_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(
    mut v_x_5301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5302_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_5301_);
    crate::leanh::lean_dec_ref(v_x_5301_);
    return v_res_5302_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__1(
    mut v_toPure_5303_: *mut crate::leanh::LeanObject,
    mut v_result_5304_: *mut crate::leanh::LeanObject,
    mut v_____r_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5306_ =
        crate::leanh::lean_apply_2(v_toPure_5303_, crate::leanh::lean_box(0), v_result_5304_);
    return v___x_5306_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__2(
    mut v_toPure_5307_: *mut crate::leanh::LeanObject,
    mut v_inst_5308_: *mut crate::leanh::LeanObject,
    mut v_structName_5309_: *mut crate::leanh::LeanObject,
    mut v_toBind_5310_: *mut crate::leanh::LeanObject,
    mut v_result_5311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_resolutionOrder_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_resolutionOrder_5312_ = crate::leanh::lean_ctor_get(v_result_5311_, 0);
    crate::leanh::lean_inc_ref(v_resolutionOrder_5312_);
    v___f_5313_ = crate::leanh::lean_alloc_closure(
        l_Lean_computeStructureResolutionOrder___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5313_, 0, v_toPure_5307_);
    crate::leanh::lean_closure_set(v___f_5313_, 1, v_result_5311_);
    v___x_5314_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(
        v_inst_5308_,
        v_structName_5309_,
        v_resolutionOrder_5312_,
    );
    v___x_5315_ = crate::leanh::lean_apply_4(
        v_toBind_5310_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5314_,
        v___f_5313_,
    );
    return v___x_5315_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__5(
    mut v_toPure_5316_: *mut crate::leanh::LeanObject,
    mut v_____s_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_5318_ = crate::leanh::lean_ctor_get(v_____s_5317_, 1);
                crate::leanh::lean_inc(v_snd_5318_);
                crate::leanh::lean_dec_ref(v_____s_5317_);
                v_fst_5319_ = crate::leanh::lean_ctor_get(v_snd_5318_, 0);
                v_snd_5320_ = crate::leanh::lean_ctor_get(v_snd_5318_, 1);
                v_isSharedCheck_5328_ = (!crate::leanh::lean_is_exclusive(v_snd_5318_)) as u8;
                if v_isSharedCheck_5328_ == 0 {
                    v___x_5322_ = v_snd_5318_;
                    v_isShared_5323_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5320_);
                    crate::leanh::lean_inc(v_fst_5319_);
                    crate::leanh::lean_dec(v_snd_5318_);
                    v___x_5322_ = crate::leanh::lean_box(0);
                    v_isShared_5323_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5323_ == 0 {
                    v___x_5325_ = v___x_5322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_fst_5319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_snd_5320_);
                    v___x_5325_ = v_reuseFailAlloc_5327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5326_ = crate::leanh::lean_apply_2(
                    v_toPure_5316_,
                    crate::leanh::lean_box(0),
                    v___x_5325_,
                );
                return v___x_5326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__9(
    mut v___x_5329_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5330_: *mut crate::leanh::LeanObject,
    mut v_x_5331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5332_: u8 = 0;
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_5331_);
    v___x_5332_ = l_Array_contains___redArg(v___x_5329_, v_parentNames_5330_, v_x_5331_);
    v___x_5333_ = crate::leanh::lean_box((v___x_5332_) as usize);
    v___x_5334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5333_);
    crate::leanh::lean_ctor_set(v___x_5334_, 1, v_x_5331_);
    return v___x_5334_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__8(
    mut v___x_5335_: *mut crate::leanh::LeanObject,
    mut v___f_5336_: *mut crate::leanh::LeanObject,
    mut v_x_5337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    v___x_5338_ = lean_array_get_size(v_x_5337_);
    v___x_5339_ = lean_mk_empty_array_with_capacity(v___x_5335_);
    v___x_5340_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
    v___x_5341_ = lean_nat_dec_lt(v___x_5335_, v___x_5338_);
    if v___x_5341_ == 0 {
        crate::leanh::lean_dec_ref(v_x_5337_);
        crate::leanh::lean_dec_ref(v___f_5336_);
        return v___x_5339_;
    } else {
        let mut v___x_5342_: u8 = 0;
        v___x_5342_ = lean_nat_dec_le(v___x_5338_, v___x_5338_);
        if v___x_5342_ == 0 {
            if v___x_5341_ == 0 {
                crate::leanh::lean_dec_ref(v_x_5337_);
                crate::leanh::lean_dec_ref(v___f_5336_);
                return v___x_5339_;
            } else {
                let mut v___x_5343_: usize = 0;
                let mut v___x_5344_: usize = 0;
                let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5343_ = 0usize;
                v___x_5344_ = lean_usize_of_nat(v___x_5338_);
                v___x_5345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5340_,
                    v___f_5336_,
                    v_x_5337_,
                    v___x_5343_,
                    v___x_5344_,
                    v___x_5339_,
                );
                return v___x_5345_;
            }
        } else {
            let mut v___x_5346_: usize = 0;
            let mut v___x_5347_: usize = 0;
            let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5346_ = 0usize;
            v___x_5347_ = lean_usize_of_nat(v___x_5338_);
            v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5340_,
                v___f_5336_,
                v_x_5337_,
                v___x_5346_,
                v___x_5347_,
                v___x_5339_,
            );
            return v___x_5348_;
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(
    mut v___x_5349_: *mut crate::leanh::LeanObject,
    mut v___f_5350_: *mut crate::leanh::LeanObject,
    mut v_x_5351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5352_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(
        v___x_5349_,
        v___f_5350_,
        v_x_5351_,
    );
    crate::leanh::lean_dec(v___x_5349_);
    return v_res_5352_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__7(
    mut v_snd_5353_: *mut crate::leanh::LeanObject,
    mut v_x1_5354_: *mut crate::leanh::LeanObject,
    mut v_x2_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5356_: u8 = 0;
    v___x_5356_ = lean_name_eq(v_x2_5355_, v_snd_5353_);
    if v___x_5356_ == 0 {
        let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5357_ = lean_array_push(v_x1_5354_, v_x2_5355_);
        return v___x_5357_;
    } else {
        crate::leanh::lean_dec(v_x2_5355_);
        return v_x1_5354_;
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(
    mut v_snd_5358_: *mut crate::leanh::LeanObject,
    mut v_x1_5359_: *mut crate::leanh::LeanObject,
    mut v_x2_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5361_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(
        v_snd_5358_,
        v_x1_5359_,
        v_x2_5360_,
    );
    crate::leanh::lean_dec(v_snd_5358_);
    return v_res_5361_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__11(
    mut v___x_5362_: *mut crate::leanh::LeanObject,
    mut v___f_5363_: *mut crate::leanh::LeanObject,
    mut v_x1_5364_: *mut crate::leanh::LeanObject,
    mut v_x2_5365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: u8 = 0;
    let mut v___x_5375_: usize = 0;
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5366_ = lean_array_get_size(v_x2_5365_);
                crate::leanh::lean_inc_ref(v_x2_5365_);
                v___x_5367_ = l_Array_toSubarray___redArg(v_x2_5365_, v___x_5362_, v___x_5366_);
                v___x_5368_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v_array_5369_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                crate::leanh::lean_inc_ref(v_array_5369_);
                v_start_5370_ = crate::leanh::lean_ctor_get(v___x_5367_, 1);
                crate::leanh::lean_inc(v_start_5370_);
                v_stop_5371_ = crate::leanh::lean_ctor_get(v___x_5367_, 2);
                crate::leanh::lean_inc(v_stop_5371_);
                crate::leanh::lean_dec_ref(v___x_5367_);
                v___x_5380_ = lean_nat_dec_lt(v_start_5370_, v_stop_5371_);
                if v___x_5380_ == 0 {
                    crate::leanh::lean_dec(v_stop_5371_);
                    crate::leanh::lean_dec(v_start_5370_);
                    crate::leanh::lean_dec_ref(v_array_5369_);
                    crate::leanh::lean_dec_ref(v_x2_5365_);
                    crate::leanh::lean_dec_ref(v___f_5363_);
                    return v_x1_5364_;
                } else {
                    v___x_5381_ = lean_array_get_size(v_array_5369_);
                    v___x_5382_ = lean_nat_dec_le(v_stop_5371_, v___x_5381_);
                    if v___x_5382_ == 0 {
                        crate::leanh::lean_dec(v_stop_5371_);
                        v___y_5373_ = v___x_5381_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5373_ = v_stop_5371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5374_ = lean_nat_dec_lt(v_start_5370_, v___y_5373_);
                if v___x_5374_ == 0 {
                    crate::leanh::lean_dec(v___y_5373_);
                    crate::leanh::lean_dec(v_start_5370_);
                    crate::leanh::lean_dec_ref(v_array_5369_);
                    crate::leanh::lean_dec_ref(v_x2_5365_);
                    crate::leanh::lean_dec_ref(v___f_5363_);
                    return v_x1_5364_;
                } else {
                    v___x_5375_ = lean_usize_of_nat(v_start_5370_);
                    crate::leanh::lean_dec(v_start_5370_);
                    v___x_5376_ = lean_usize_of_nat(v___y_5373_);
                    crate::leanh::lean_dec(v___y_5373_);
                    v___x_5377_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5368_,
                        v___f_5363_,
                        v_array_5369_,
                        v___x_5375_,
                        v___x_5376_,
                    );
                    v___x_5378_ = (crate::leanh::lean_unbox(v___x_5377_) as u8);
                    crate::leanh::lean_dec(v___x_5377_);
                    if v___x_5378_ == 0 {
                        crate::leanh::lean_dec_ref(v_x2_5365_);
                        return v_x1_5364_;
                    } else {
                        v___x_5379_ = lean_array_push(v_x1_5364_, v_x2_5365_);
                        return v___x_5379_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__10(
    mut v_snd_5383_: *mut crate::leanh::LeanObject,
    mut v_x_5384_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5385_: u8 = 0;
    v___x_5385_ = lean_name_eq(v_x_5384_, v_snd_5383_);
    return v___x_5385_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(
    mut v_snd_5386_: *mut crate::leanh::LeanObject,
    mut v_x_5387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5388_: u8 = 0;
    let mut v_r_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5388_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_5386_, v_x_5387_);
    crate::leanh::lean_dec(v_x_5387_);
    crate::leanh::lean_dec(v_snd_5386_);
    v_r_5389_ = crate::leanh::lean_box((v_res_5388_) as usize);
    return v_r_5389_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__12(
    mut v_toPure_5391_: *mut crate::leanh::LeanObject,
    mut v___x_5392_: *mut crate::leanh::LeanObject,
    mut v_fst_5393_: *mut crate::leanh::LeanObject,
    mut v_fst_5394_: *mut crate::leanh::LeanObject,
    mut v___f_5395_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5396_: u8,
    mut v_parentNames_5397_: *mut crate::leanh::LeanObject,
    mut v_snd_5398_: *mut crate::leanh::LeanObject,
    mut v___f_5399_: *mut crate::leanh::LeanObject,
    mut v___x_5400_: *mut crate::leanh::LeanObject,
    mut v_____x_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defects_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5418_: usize = 0;
    let mut v___x_5419_: usize = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: u8 = 0;
    let mut v___x_5424_: u8 = 0;
    let mut v___x_5425_: usize = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: usize = 0;
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: u8 = 0;
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    let mut v___y_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5459_: usize = 0;
    let mut v___x_5460_: usize = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: u8 = 0;
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: u8 = 0;
    let mut v___f_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: u8 = 0;
    let mut v___x_5474_: usize = 0;
    let mut v___x_5475_: usize = 0;
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: usize = 0;
    let mut v___x_5478_: usize = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5410_ = crate::leanh::lean_ctor_get(v_____x_5401_, 0);
                crate::leanh::lean_inc(v_fst_5410_);
                v_snd_5411_ = crate::leanh::lean_ctor_get(v_____x_5401_, 1);
                crate::leanh::lean_inc_n(v_snd_5411_, 2);
                crate::leanh::lean_dec_ref(v_____x_5401_);
                v___f_5412_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5412_, 0, v_snd_5411_);
                crate::leanh::lean_inc(v___x_5392_);
                v___f_5413_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_5413_, 0, v___x_5392_);
                crate::leanh::lean_closure_set(v___f_5413_, 1, v___f_5412_);
                v___x_5429_ = (crate::leanh::lean_unbox(v_fst_5410_) as u8);
                crate::leanh::lean_dec(v_fst_5410_);
                if v___x_5429_ == 0 {
                    if v_relaxed_5396_ == 0 {
                        v___x_5430_ = l_Lean_setStructureParents___redArg___closed__0;
                        crate::leanh::lean_inc_ref(v_parentNames_5397_);
                        v___f_5431_ = crate::leanh::lean_alloc_closure(
                            l_Lean_mergeStructureResolutionOrders___redArg___lam__9
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_5431_, 0, v___x_5430_);
                        crate::leanh::lean_closure_set(v___f_5431_, 1, v_parentNames_5397_);
                        v___x_5467_ = lean_array_get_size(v_fst_5394_);
                        v___x_5468_ = lean_mk_empty_array_with_capacity(v___x_5392_);
                        v___x_5469_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                        v___x_5470_ = lean_nat_dec_lt(v___x_5392_, v___x_5467_);
                        if v___x_5470_ == 0 {
                            v___y_5457_ = v___x_5468_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5411_);
                            v___f_5471_ = crate::leanh::lean_alloc_closure(
                                l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_5471_, 0, v_snd_5411_);
                            crate::leanh::lean_inc(v___x_5400_);
                            v___f_5472_ = crate::leanh::lean_alloc_closure(
                                l_Lean_mergeStructureResolutionOrders___redArg___lam__11
                                    as *mut core::ffi::c_void,
                                4,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_5472_, 0, v___x_5400_);
                            crate::leanh::lean_closure_set(v___f_5472_, 1, v___f_5471_);
                            v___x_5473_ = lean_nat_dec_le(v___x_5467_, v___x_5467_);
                            if v___x_5473_ == 0 {
                                if v___x_5470_ == 0 {
                                    crate::leanh::lean_dec_ref(v___f_5472_);
                                    v___y_5457_ = v___x_5468_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5474_ = 0usize;
                                    v___x_5475_ = lean_usize_of_nat(v___x_5467_);
                                    crate::leanh::lean_inc(v_fst_5394_);
                                    v___x_5476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_5469_, v___f_5472_, v_fst_5394_, v___x_5474_, v___x_5475_, v___x_5468_);
                                    v___y_5457_ = v___x_5476_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v___x_5477_ = 0usize;
                                v___x_5478_ = lean_usize_of_nat(v___x_5467_);
                                crate::leanh::lean_inc(v_fst_5394_);
                                v___x_5479_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_5469_,
                                        v___f_5472_,
                                        v_fst_5394_,
                                        v___x_5477_,
                                        v___x_5478_,
                                        v___x_5468_,
                                    );
                                v___y_5457_ = v___x_5479_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5400_);
                        crate::leanh::lean_dec_ref(v___f_5399_);
                        crate::leanh::lean_dec_ref(v_parentNames_5397_);
                        v_defects_5415_ = v_snd_5398_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5400_);
                    crate::leanh::lean_dec_ref(v___f_5399_);
                    crate::leanh::lean_dec_ref(v_parentNames_5397_);
                    v_defects_5415_ = v_snd_5398_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5406_, 0, v___y_5404_);
                crate::leanh::lean_ctor_set(v___x_5406_, 1, v___y_5403_);
                v___x_5407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5407_, 0, v___y_5405_);
                crate::leanh::lean_ctor_set(v___x_5407_, 1, v___x_5406_);
                v___x_5408_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5408_, 0, v___x_5407_);
                v___x_5409_ = crate::leanh::lean_apply_2(
                    v_toPure_5391_,
                    crate::leanh::lean_box(0),
                    v___x_5408_,
                );
                return v___x_5409_;
            }
            2 => {
                v___x_5416_ = lean_array_push(v_fst_5393_, v_snd_5411_);
                v___x_5417_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v_sz_5418_ = lean_array_size(v_fst_5394_);
                v___x_5419_ = 0usize;
                v___x_5420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5417_,
                    v___f_5413_,
                    v_sz_5418_,
                    v___x_5419_,
                    v_fst_5394_,
                );
                v___x_5421_ = lean_array_get_size(v___x_5420_);
                v___x_5422_ = lean_mk_empty_array_with_capacity(v___x_5392_);
                v___x_5423_ = lean_nat_dec_lt(v___x_5392_, v___x_5421_);
                crate::leanh::lean_dec(v___x_5392_);
                if v___x_5423_ == 0 {
                    crate::leanh::lean_dec(v___x_5420_);
                    crate::leanh::lean_dec_ref(v___f_5395_);
                    v___y_5403_ = v_defects_5415_;
                    v___y_5404_ = v___x_5416_;
                    v___y_5405_ = v___x_5422_;
                    state = 1;
                    continue;
                } else {
                    v___x_5424_ = lean_nat_dec_le(v___x_5421_, v___x_5421_);
                    if v___x_5424_ == 0 {
                        if v___x_5423_ == 0 {
                            crate::leanh::lean_dec(v___x_5420_);
                            crate::leanh::lean_dec_ref(v___f_5395_);
                            v___y_5403_ = v_defects_5415_;
                            v___y_5404_ = v___x_5416_;
                            v___y_5405_ = v___x_5422_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5425_ = lean_usize_of_nat(v___x_5421_);
                            v___x_5426_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5417_,
                                    v___f_5395_,
                                    v___x_5420_,
                                    v___x_5419_,
                                    v___x_5425_,
                                    v___x_5422_,
                                );
                            v___y_5403_ = v_defects_5415_;
                            v___y_5404_ = v___x_5416_;
                            v___y_5405_ = v___x_5426_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_5427_ = lean_usize_of_nat(v___x_5421_);
                        v___x_5428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5417_,
                            v___f_5395_,
                            v___x_5420_,
                            v___x_5419_,
                            v___x_5427_,
                            v___x_5422_,
                        );
                        v___y_5403_ = v_defects_5415_;
                        v___y_5404_ = v___x_5416_;
                        v___y_5405_ = v___x_5428_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5434_ = l_Array_eraseReps___redArg(v___x_5430_, v___y_5433_);
                crate::leanh::lean_inc_n(v_snd_5411_, 2);
                v___x_5435_ =
                    l_Array_contains___redArg(v___x_5430_, v_parentNames_5397_, v_snd_5411_);
                v___x_5436_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v_sz_5437_ = lean_array_size(v___x_5434_);
                v___x_5438_ = 0usize;
                v___x_5439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5436_,
                    v___f_5431_,
                    v_sz_5437_,
                    v___x_5438_,
                    v___x_5434_,
                );
                v___x_5440_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5440_, 0, v_snd_5411_);
                crate::leanh::lean_ctor_set(v___x_5440_, 1, v___x_5439_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5440_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5435_,
                );
                v___x_5441_ = lean_array_push(v_snd_5398_, v___x_5440_);
                v_defects_5415_ = v___x_5441_;
                state = 2;
                continue;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_5443_);
                v___x_5448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___y_5443_,
                    v___y_5446_,
                    v___y_5445_,
                    v___y_5444_,
                    v___y_5447_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_5447_);
                crate::leanh::lean_dec(v___y_5446_);
                v___y_5433_ = v___x_5448_;
                state = 3;
                continue;
            }
            5 => {
                v___x_5455_ = lean_nat_dec_le(v___y_5454_, v___y_5450_);
                if v___x_5455_ == 0 {
                    crate::leanh::lean_dec(v___y_5450_);
                    crate::leanh::lean_inc(v___y_5454_);
                    v___y_5443_ = v___y_5451_;
                    v___y_5444_ = v___y_5454_;
                    v___y_5445_ = v___y_5452_;
                    v___y_5446_ = v___y_5453_;
                    v___y_5447_ = v___y_5454_;
                    state = 4;
                    continue;
                } else {
                    v___y_5443_ = v___y_5451_;
                    v___y_5444_ = v___y_5454_;
                    v___y_5445_ = v___y_5452_;
                    v___y_5446_ = v___y_5453_;
                    v___y_5447_ = v___y_5450_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_5458_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v_sz_5459_ = lean_array_size(v___y_5457_);
                v___x_5460_ = 0usize;
                v___x_5461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5458_,
                    v___f_5399_,
                    v_sz_5459_,
                    v___x_5460_,
                    v___y_5457_,
                );
                v___x_5462_ = lean_array_get_size(v___x_5461_);
                v___x_5463_ = lean_nat_dec_eq(v___x_5462_, v___x_5392_);
                if v___x_5463_ == 0 {
                    v___x_5464_ =
                        l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0;
                    v___x_5465_ = lean_nat_sub(v___x_5462_, v___x_5400_);
                    crate::leanh::lean_dec(v___x_5400_);
                    v___x_5466_ = lean_nat_dec_le(v___x_5392_, v___x_5465_);
                    if v___x_5466_ == 0 {
                        crate::leanh::lean_inc(v___x_5465_);
                        v___y_5450_ = v___x_5465_;
                        v___y_5451_ = v___x_5464_;
                        v___y_5452_ = v___x_5461_;
                        v___y_5453_ = v___x_5462_;
                        v___y_5454_ = v___x_5465_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_5392_);
                        v___y_5450_ = v___x_5465_;
                        v___y_5451_ = v___x_5464_;
                        v___y_5452_ = v___x_5461_;
                        v___y_5453_ = v___x_5462_;
                        v___y_5454_ = v___x_5392_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5400_);
                    v___y_5433_ = v___x_5461_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(
    mut v_toPure_5480_: *mut crate::leanh::LeanObject,
    mut v___x_5481_: *mut crate::leanh::LeanObject,
    mut v_fst_5482_: *mut crate::leanh::LeanObject,
    mut v_fst_5483_: *mut crate::leanh::LeanObject,
    mut v___f_5484_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5485_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5486_: *mut crate::leanh::LeanObject,
    mut v_snd_5487_: *mut crate::leanh::LeanObject,
    mut v___f_5488_: *mut crate::leanh::LeanObject,
    mut v___x_5489_: *mut crate::leanh::LeanObject,
    mut v_____x_5490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5491_: u8 = 0;
    let mut v_res_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5491_ = (crate::leanh::lean_unbox(v_relaxed_5485_) as u8);
    v_res_5492_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(
        v_toPure_5480_,
        v___x_5481_,
        v_fst_5482_,
        v_fst_5483_,
        v___f_5484_,
        v_relaxed_boxed_5491_,
        v_parentNames_5486_,
        v_snd_5487_,
        v___f_5488_,
        v___x_5489_,
        v_____x_5490_,
    );
    return v_res_5492_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__13(
    mut v___x_5493_: *mut crate::leanh::LeanObject,
    mut v_toPure_5494_: *mut crate::leanh::LeanObject,
    mut v___f_5495_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5496_: u8,
    mut v_parentNames_5497_: *mut crate::leanh::LeanObject,
    mut v___f_5498_: *mut crate::leanh::LeanObject,
    mut v___x_5499_: *mut crate::leanh::LeanObject,
    mut v_inst_5500_: *mut crate::leanh::LeanObject,
    mut v_toBind_5501_: *mut crate::leanh::LeanObject,
    mut v___f_5502_: *mut crate::leanh::LeanObject,
    mut v_b_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5508_: u8 = 0;
    let mut v_fst_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_5504_ = crate::leanh::lean_ctor_get(v_b_5503_, 1);
                v_fst_5505_ = crate::leanh::lean_ctor_get(v_b_5503_, 0);
                v_isSharedCheck_5531_ = (!crate::leanh::lean_is_exclusive(v_b_5503_)) as u8;
                if v_isSharedCheck_5531_ == 0 {
                    v___x_5507_ = v_b_5503_;
                    v_isShared_5508_ = v_isSharedCheck_5531_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5504_);
                    crate::leanh::lean_inc(v_fst_5505_);
                    crate::leanh::lean_dec(v_b_5503_);
                    v___x_5507_ = crate::leanh::lean_box(0);
                    v_isShared_5508_ = v_isSharedCheck_5531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5509_ = crate::leanh::lean_ctor_get(v_snd_5504_, 0);
                v_snd_5510_ = crate::leanh::lean_ctor_get(v_snd_5504_, 1);
                v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v_snd_5504_)) as u8;
                if v_isSharedCheck_5530_ == 0 {
                    v___x_5512_ = v_snd_5504_;
                    v_isShared_5513_ = v_isSharedCheck_5530_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5510_);
                    crate::leanh::lean_inc(v_fst_5509_);
                    crate::leanh::lean_dec(v_snd_5504_);
                    v___x_5512_ = crate::leanh::lean_box(0);
                    v_isShared_5513_ = v_isSharedCheck_5530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5514_ = lean_array_get_size(v_fst_5505_);
                v___x_5515_ = lean_nat_dec_eq(v___x_5514_, v___x_5493_);
                if v___x_5515_ == 0 {
                    crate::leanh::lean_del_object(v___x_5512_);
                    crate::leanh::lean_del_object(v___x_5507_);
                    v___x_5516_ = crate::leanh::lean_box((v_relaxed_5496_) as usize);
                    crate::leanh::lean_inc(v_fst_5505_);
                    v___f_5517_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed
                            as *mut core::ffi::c_void,
                        11,
                        10,
                    );
                    crate::leanh::lean_closure_set(v___f_5517_, 0, v_toPure_5494_);
                    crate::leanh::lean_closure_set(v___f_5517_, 1, v___x_5493_);
                    crate::leanh::lean_closure_set(v___f_5517_, 2, v_fst_5509_);
                    crate::leanh::lean_closure_set(v___f_5517_, 3, v_fst_5505_);
                    crate::leanh::lean_closure_set(v___f_5517_, 4, v___f_5495_);
                    crate::leanh::lean_closure_set(v___f_5517_, 5, v___x_5516_);
                    crate::leanh::lean_closure_set(v___f_5517_, 6, v_parentNames_5497_);
                    crate::leanh::lean_closure_set(v___f_5517_, 7, v_snd_5510_);
                    crate::leanh::lean_closure_set(v___f_5517_, 8, v___f_5498_);
                    crate::leanh::lean_closure_set(v___f_5517_, 9, v___x_5499_);
                    v___x_5518_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_5500_, v_fst_5505_);
                    crate::leanh::lean_inc(v_toBind_5501_);
                    v___x_5519_ = crate::leanh::lean_apply_4(
                        v_toBind_5501_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5518_,
                        v___f_5517_,
                    );
                    v___x_5520_ = crate::leanh::lean_apply_4(
                        v_toBind_5501_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5519_,
                        v___f_5502_,
                    );
                    return v___x_5520_;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_5500_);
                    crate::leanh::lean_dec(v___x_5499_);
                    crate::leanh::lean_dec_ref(v___f_5498_);
                    crate::leanh::lean_dec_ref(v_parentNames_5497_);
                    crate::leanh::lean_dec_ref(v___f_5495_);
                    crate::leanh::lean_dec(v___x_5493_);
                    if v_isShared_5513_ == 0 {
                        v___x_5522_ = v___x_5512_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5509_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5510_);
                        v___x_5522_ = v_reuseFailAlloc_5529_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5507_, 1, v___x_5522_);
                    v___x_5524_ = v___x_5507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_fst_5505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5528_, 1, v___x_5522_);
                    v___x_5524_ = v_reuseFailAlloc_5528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5525_, 0, v___x_5524_);
                v___x_5526_ = crate::leanh::lean_apply_2(
                    v_toPure_5494_,
                    crate::leanh::lean_box(0),
                    v___x_5525_,
                );
                v___x_5527_ = crate::leanh::lean_apply_4(
                    v_toBind_5501_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5526_,
                    v___f_5502_,
                );
                return v___x_5527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(
    mut v___x_5532_: *mut crate::leanh::LeanObject,
    mut v_toPure_5533_: *mut crate::leanh::LeanObject,
    mut v___f_5534_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5535_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5536_: *mut crate::leanh::LeanObject,
    mut v___f_5537_: *mut crate::leanh::LeanObject,
    mut v___x_5538_: *mut crate::leanh::LeanObject,
    mut v_inst_5539_: *mut crate::leanh::LeanObject,
    mut v_toBind_5540_: *mut crate::leanh::LeanObject,
    mut v___f_5541_: *mut crate::leanh::LeanObject,
    mut v_b_5542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5543_: u8 = 0;
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5543_ = (crate::leanh::lean_unbox(v_relaxed_5535_) as u8);
    v_res_5544_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(
        v___x_5532_,
        v_toPure_5533_,
        v___f_5534_,
        v_relaxed_boxed_5543_,
        v_parentNames_5536_,
        v___f_5537_,
        v___x_5538_,
        v_inst_5539_,
        v_toBind_5540_,
        v___f_5541_,
        v_b_5542_,
    );
    return v_res_5544_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__6(
    mut v___x_5545_: *mut crate::leanh::LeanObject,
    mut v_x_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5547_ = crate::leanh::lean_box(0);
    v___x_5548_ = lean_array_get_borrowed(v___x_5547_, v_x_5546_, v___x_5545_);
    crate::leanh::lean_inc(v___x_5548_);
    return v___x_5548_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(
    mut v___x_5549_: *mut crate::leanh::LeanObject,
    mut v_x_5550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5551_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v___x_5549_, v_x_5550_);
    crate::leanh::lean_dec_ref(v_x_5550_);
    crate::leanh::lean_dec(v___x_5549_);
    return v_res_5551_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__14(
    mut v_toPure_5556_: *mut crate::leanh::LeanObject,
    mut v___f_5557_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5558_: u8,
    mut v_parentNames_5559_: *mut crate::leanh::LeanObject,
    mut v_inst_5560_: *mut crate::leanh::LeanObject,
    mut v_toBind_5561_: *mut crate::leanh::LeanObject,
    mut v___f_5562_: *mut crate::leanh::LeanObject,
    mut v_structName_5563_: *mut crate::leanh::LeanObject,
    mut v___f_5564_: *mut crate::leanh::LeanObject,
    mut v___f_5565_: *mut crate::leanh::LeanObject,
    mut v_parentResOrders_5566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resOrder_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defects_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: u8 = 0;
    let mut v___x_5588_: u8 = 0;
    let mut v___x_5589_: usize = 0;
    let mut v___x_5590_: usize = 0;
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: usize = 0;
    let mut v___x_5593_: usize = 0;
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5567_ = crate::leanh::lean_unsigned_to_nat(0);
                v___f_5568_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0;
                v_j_5581_ = lean_array_get_size(v_parentResOrders_5566_);
                crate::leanh::lean_inc_ref(v_parentNames_5559_);
                v_as_5582_ = lean_array_push(v_parentResOrders_5566_, v_parentNames_5559_);
                v___x_5583_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                    crate::leanh::lean_box(0),
                    v___x_5567_,
                    v_as_5582_,
                    v_j_5581_,
                );
                v___x_5584_ = lean_array_get_size(v___x_5583_);
                v___x_5585_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1;
                v___x_5586_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
                v___x_5587_ = lean_nat_dec_lt(v___x_5567_, v___x_5584_);
                if v___x_5587_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5583_);
                    crate::leanh::lean_dec_ref(v___f_5565_);
                    v___y_5570_ = v___x_5585_;
                    state = 1;
                    continue;
                } else {
                    v___x_5588_ = lean_nat_dec_le(v___x_5584_, v___x_5584_);
                    if v___x_5588_ == 0 {
                        if v___x_5587_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5583_);
                            crate::leanh::lean_dec_ref(v___f_5565_);
                            v___y_5570_ = v___x_5585_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5589_ = 0usize;
                            v___x_5590_ = lean_usize_of_nat(v___x_5584_);
                            v___x_5591_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5586_,
                                    v___f_5565_,
                                    v___x_5583_,
                                    v___x_5589_,
                                    v___x_5590_,
                                    v___x_5585_,
                                );
                            v___y_5570_ = v___x_5591_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_5592_ = 0usize;
                        v___x_5593_ = lean_usize_of_nat(v___x_5584_);
                        v___x_5594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5586_,
                            v___f_5565_,
                            v___x_5583_,
                            v___x_5592_,
                            v___x_5593_,
                            v___x_5585_,
                        );
                        v___y_5570_ = v___x_5594_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5571_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5572_ = crate::leanh::lean_box((v_relaxed_5558_) as usize);
                crate::leanh::lean_inc(v_toBind_5561_);
                crate::leanh::lean_inc_ref(v_inst_5560_);
                v___f_5573_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed
                        as *mut core::ffi::c_void,
                    11,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_5573_, 0, v___x_5567_);
                crate::leanh::lean_closure_set(v___f_5573_, 1, v_toPure_5556_);
                crate::leanh::lean_closure_set(v___f_5573_, 2, v___f_5557_);
                crate::leanh::lean_closure_set(v___f_5573_, 3, v___x_5572_);
                crate::leanh::lean_closure_set(v___f_5573_, 4, v_parentNames_5559_);
                crate::leanh::lean_closure_set(v___f_5573_, 5, v___f_5568_);
                crate::leanh::lean_closure_set(v___f_5573_, 6, v___x_5571_);
                crate::leanh::lean_closure_set(v___f_5573_, 7, v_inst_5560_);
                crate::leanh::lean_closure_set(v___f_5573_, 8, v_toBind_5561_);
                crate::leanh::lean_closure_set(v___f_5573_, 9, v___f_5562_);
                v___x_5574_ = lean_mk_empty_array_with_capacity(v___x_5571_);
                v_resOrder_5575_ = lean_array_push(v___x_5574_, v_structName_5563_);
                v_defects_5576_ =
                    l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1;
                v___x_5577_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5577_, 0, v_resOrder_5575_);
                crate::leanh::lean_ctor_set(v___x_5577_, 1, v_defects_5576_);
                v___x_5578_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5578_, 0, v___y_5570_);
                crate::leanh::lean_ctor_set(v___x_5578_, 1, v___x_5577_);
                v___x_5579_ = l___private_Init_While_0__whileM_erased___redArg(
                    v_inst_5560_,
                    v___f_5573_,
                    v___x_5578_,
                );
                v___x_5580_ = crate::leanh::lean_apply_4(
                    v_toBind_5561_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5579_,
                    v___f_5564_,
                );
                return v___x_5580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(
    mut v_toPure_5595_: *mut crate::leanh::LeanObject,
    mut v___f_5596_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5597_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5598_: *mut crate::leanh::LeanObject,
    mut v_inst_5599_: *mut crate::leanh::LeanObject,
    mut v_toBind_5600_: *mut crate::leanh::LeanObject,
    mut v___f_5601_: *mut crate::leanh::LeanObject,
    mut v_structName_5602_: *mut crate::leanh::LeanObject,
    mut v___f_5603_: *mut crate::leanh::LeanObject,
    mut v___f_5604_: *mut crate::leanh::LeanObject,
    mut v_parentResOrders_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5606_: u8 = 0;
    let mut v_res_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5606_ = (crate::leanh::lean_unbox(v_relaxed_5597_) as u8);
    v_res_5607_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(
        v_toPure_5595_,
        v___f_5596_,
        v_relaxed_boxed_5606_,
        v_parentNames_5598_,
        v_inst_5599_,
        v_toBind_5600_,
        v___f_5601_,
        v_structName_5602_,
        v___f_5603_,
        v___f_5604_,
        v_parentResOrders_5605_,
    );
    return v_res_5607_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__0(
    mut v_x_5608_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    v___x_5609_ = lean_array_get_size(v_x_5608_);
    v___x_5610_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5611_ = lean_nat_dec_eq(v___x_5609_, v___x_5610_);
    if v___x_5611_ == 0 {
        let mut v___x_5612_: u8 = 0;
        v___x_5612_ = 1;
        return v___x_5612_;
    } else {
        let mut v___x_5613_: u8 = 0;
        v___x_5613_ = 0;
        return v___x_5613_;
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(
    mut v_x_5614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5615_: u8 = 0;
    let mut v_r_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5615_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_5614_);
    crate::leanh::lean_dec_ref(v_x_5614_);
    v_r_5616_ = crate::leanh::lean_box((v_res_5615_) as usize);
    return v_r_5616_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__1(
    mut v___f_5617_: *mut crate::leanh::LeanObject,
    mut v_x1_5618_: *mut crate::leanh::LeanObject,
    mut v_x2_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: u8 = 0;
    crate::leanh::lean_inc_ref(v_x2_5619_);
    v___x_5620_ = crate::leanh::lean_apply_1(v___f_5617_, v_x2_5619_);
    v___x_5621_ = (crate::leanh::lean_unbox(v___x_5620_) as u8);
    if v___x_5621_ == 0 {
        crate::leanh::lean_dec_ref(v_x2_5619_);
        return v_x1_5618_;
    } else {
        let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5622_ = lean_array_push(v_x1_5618_, v_x2_5619_);
        return v___x_5622_;
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__4(
    mut v_toPure_5623_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut v_a_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5637_: u8 = 0;
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_5624_) == 0 {
                    v_a_5625_ = crate::leanh::lean_ctor_get(v_____do__lift_5624_, 0);
                    v_isSharedCheck_5633_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_5624_)) as u8;
                    if v_isSharedCheck_5633_ == 0 {
                        v___x_5627_ = v_____do__lift_5624_;
                        v_isShared_5628_ = v_isSharedCheck_5633_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5625_);
                        crate::leanh::lean_dec(v_____do__lift_5624_);
                        v___x_5627_ = crate::leanh::lean_box(0);
                        v_isShared_5628_ = v_isSharedCheck_5633_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5634_ = crate::leanh::lean_ctor_get(v_____do__lift_5624_, 0);
                    v_isSharedCheck_5642_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_5624_)) as u8;
                    if v_isSharedCheck_5642_ == 0 {
                        v___x_5636_ = v_____do__lift_5624_;
                        v_isShared_5637_ = v_isSharedCheck_5642_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5634_);
                        crate::leanh::lean_dec(v_____do__lift_5624_);
                        v___x_5636_ = crate::leanh::lean_box(0);
                        v_isShared_5637_ = v_isSharedCheck_5642_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5628_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5627_, 1);
                    v___x_5630_ = v___x_5627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_a_5625_);
                    v___x_5630_ = v_reuseFailAlloc_5632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5631_ = crate::leanh::lean_apply_2(
                    v_toPure_5623_,
                    crate::leanh::lean_box(0),
                    v___x_5630_,
                );
                return v___x_5631_;
            }
            3 => {
                if v_isShared_5637_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5636_, 0);
                    v___x_5639_ = v___x_5636_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5634_);
                    v___x_5639_ = v_reuseFailAlloc_5641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5640_ = crate::leanh::lean_apply_2(
                    v_toPure_5623_,
                    crate::leanh::lean_box(0),
                    v___x_5639_,
                );
                return v___x_5640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__3(
    mut v_toPure_5643_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_resolutionOrder_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_resolutionOrder_5645_ = crate::leanh::lean_ctor_get(v_____do__lift_5644_, 0);
    crate::leanh::lean_inc_ref(v_resolutionOrder_5645_);
    crate::leanh::lean_dec_ref(v_____do__lift_5644_);
    v___x_5646_ = crate::leanh::lean_apply_2(
        v_toPure_5643_,
        crate::leanh::lean_box(0),
        v_resolutionOrder_5645_,
    );
    return v___x_5646_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg(
    mut v_inst_5651_: *mut crate::leanh::LeanObject,
    mut v_inst_5652_: *mut crate::leanh::LeanObject,
    mut v_structName_5653_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5654_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5655_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5666_: usize = 0;
    let mut v___x_5667_: usize = 0;
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5656_ = crate::leanh::lean_ctor_get(v_inst_5651_, 0);
    v_toBind_5657_ = crate::leanh::lean_ctor_get(v_inst_5651_, 1);
    crate::leanh::lean_inc_n(v_toBind_5657_, 3);
    v_toPure_5658_ = crate::leanh::lean_ctor_get(v_toApplicative_5656_, 1);
    v___f_5659_ = l_Lean_mergeStructureResolutionOrders___redArg___closed__1;
    crate::leanh::lean_inc_n(v_toPure_5658_, 4);
    v___f_5660_ = crate::leanh::lean_alloc_closure(
        l_Lean_mergeStructureResolutionOrders___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5660_, 0, v_toPure_5658_);
    crate::leanh::lean_inc_ref_n(v_inst_5651_, 2);
    v___f_5661_ = crate::leanh::lean_alloc_closure(
        l_Lean_mergeStructureResolutionOrders___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5661_, 0, v_inst_5651_);
    crate::leanh::lean_closure_set(v___f_5661_, 1, v_inst_5652_);
    crate::leanh::lean_closure_set(v___f_5661_, 2, v_toBind_5657_);
    crate::leanh::lean_closure_set(v___f_5661_, 3, v___f_5660_);
    v___f_5662_ = crate::leanh::lean_alloc_closure(
        l_Lean_mergeStructureResolutionOrders___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5662_, 0, v_toPure_5658_);
    v___f_5663_ = crate::leanh::lean_alloc_closure(
        l_Lean_mergeStructureResolutionOrders___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5663_, 0, v_toPure_5658_);
    v___x_5664_ = crate::leanh::lean_box((v_relaxed_5655_) as usize);
    crate::leanh::lean_inc_ref(v_parentNames_5654_);
    v___f_5665_ = crate::leanh::lean_alloc_closure(
        l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_5665_, 0, v_toPure_5658_);
    crate::leanh::lean_closure_set(v___f_5665_, 1, v___f_5659_);
    crate::leanh::lean_closure_set(v___f_5665_, 2, v___x_5664_);
    crate::leanh::lean_closure_set(v___f_5665_, 3, v_parentNames_5654_);
    crate::leanh::lean_closure_set(v___f_5665_, 4, v_inst_5651_);
    crate::leanh::lean_closure_set(v___f_5665_, 5, v_toBind_5657_);
    crate::leanh::lean_closure_set(v___f_5665_, 6, v___f_5662_);
    crate::leanh::lean_closure_set(v___f_5665_, 7, v_structName_5653_);
    crate::leanh::lean_closure_set(v___f_5665_, 8, v___f_5663_);
    crate::leanh::lean_closure_set(v___f_5665_, 9, v___f_5659_);
    v_sz_5666_ = lean_array_size(v_parentNames_5654_);
    v___x_5667_ = 0usize;
    v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5651_,
        v___f_5661_,
        v_sz_5666_,
        v___x_5667_,
        v_parentNames_5654_,
    );
    v___x_5669_ = crate::leanh::lean_apply_4(
        v_toBind_5657_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5668_,
        v___f_5665_,
    );
    return v___x_5669_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__3(
    mut v_structName_5670_: *mut crate::leanh::LeanObject,
    mut v_toPure_5671_: *mut crate::leanh::LeanObject,
    mut v___f_5672_: *mut crate::leanh::LeanObject,
    mut v_inst_5673_: *mut crate::leanh::LeanObject,
    mut v_inst_5674_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5675_: u8,
    mut v_toBind_5676_: *mut crate::leanh::LeanObject,
    mut v___f_5677_: *mut crate::leanh::LeanObject,
    mut v_env_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_env_5678_);
    v___x_5679_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(
        v_env_5678_,
        v_structName_5670_,
    );
    if crate::leanh::lean_obj_tag(v___x_5679_) == 1 {
        let mut v_val_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_5678_);
        crate::leanh::lean_dec(v___f_5677_);
        crate::leanh::lean_dec(v_toBind_5676_);
        crate::leanh::lean_dec_ref(v_inst_5674_);
        crate::leanh::lean_dec_ref(v_inst_5673_);
        crate::leanh::lean_dec_ref(v___f_5672_);
        crate::leanh::lean_dec(v_structName_5670_);
        v_val_5680_ = crate::leanh::lean_ctor_get(v___x_5679_, 0);
        crate::leanh::lean_inc(v_val_5680_);
        crate::leanh::lean_dec_ref_known(v___x_5679_, 1);
        v___x_5681_ = l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1;
        v___x_5682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5682_, 0, v_val_5680_);
        crate::leanh::lean_ctor_set(v___x_5682_, 1, v___x_5681_);
        v___x_5683_ =
            crate::leanh::lean_apply_2(v_toPure_5671_, crate::leanh::lean_box(0), v___x_5682_);
        return v___x_5683_;
    } else {
        let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5686_: usize = 0;
        let mut v___x_5687_: usize = 0;
        let mut v_parentNames_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5679_);
        crate::leanh::lean_dec(v_toPure_5671_);
        crate::leanh::lean_inc(v_structName_5670_);
        v___x_5684_ = l_Lean_getStructureParentInfo(v_env_5678_, v_structName_5670_);
        v___x_5685_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9;
        v_sz_5686_ = lean_array_size(v___x_5684_);
        v___x_5687_ = 0usize;
        v_parentNames_5688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5685_,
            v___f_5672_,
            v_sz_5686_,
            v___x_5687_,
            v___x_5684_,
        );
        v___x_5689_ = l_Lean_mergeStructureResolutionOrders___redArg(
            v_inst_5673_,
            v_inst_5674_,
            v_structName_5670_,
            v_parentNames_5688_,
            v_relaxed_5675_,
        );
        v___x_5690_ = crate::leanh::lean_apply_4(
            v_toBind_5676_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5689_,
            v___f_5677_,
        );
        return v___x_5690_;
    }
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(
    mut v_structName_5691_: *mut crate::leanh::LeanObject,
    mut v_toPure_5692_: *mut crate::leanh::LeanObject,
    mut v___f_5693_: *mut crate::leanh::LeanObject,
    mut v_inst_5694_: *mut crate::leanh::LeanObject,
    mut v_inst_5695_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5696_: *mut crate::leanh::LeanObject,
    mut v_toBind_5697_: *mut crate::leanh::LeanObject,
    mut v___f_5698_: *mut crate::leanh::LeanObject,
    mut v_env_5699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5700_: u8 = 0;
    let mut v_res_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5700_ = (crate::leanh::lean_unbox(v_relaxed_5696_) as u8);
    v_res_5701_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(
        v_structName_5691_,
        v_toPure_5692_,
        v___f_5693_,
        v_inst_5694_,
        v_inst_5695_,
        v_relaxed_boxed_5700_,
        v_toBind_5697_,
        v___f_5698_,
        v_env_5699_,
    );
    return v_res_5701_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg(
    mut v_inst_5702_: *mut crate::leanh::LeanObject,
    mut v_inst_5703_: *mut crate::leanh::LeanObject,
    mut v_structName_5704_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5705_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5706_ = crate::leanh::lean_ctor_get(v_inst_5702_, 0);
    v_toBind_5707_ = crate::leanh::lean_ctor_get(v_inst_5702_, 1);
    crate::leanh::lean_inc_n(v_toBind_5707_, 3);
    v_getEnv_5708_ = crate::leanh::lean_ctor_get(v_inst_5703_, 0);
    crate::leanh::lean_inc(v_getEnv_5708_);
    v_toPure_5709_ = crate::leanh::lean_ctor_get(v_toApplicative_5706_, 1);
    crate::leanh::lean_inc_n(v_toPure_5709_, 2);
    v___f_5710_ = l_Lean_computeStructureResolutionOrder___redArg___closed__0;
    crate::leanh::lean_inc(v_structName_5704_);
    crate::leanh::lean_inc_ref(v_inst_5703_);
    v___f_5711_ = crate::leanh::lean_alloc_closure(
        l_Lean_computeStructureResolutionOrder___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5711_, 0, v_toPure_5709_);
    crate::leanh::lean_closure_set(v___f_5711_, 1, v_inst_5703_);
    crate::leanh::lean_closure_set(v___f_5711_, 2, v_structName_5704_);
    crate::leanh::lean_closure_set(v___f_5711_, 3, v_toBind_5707_);
    v___x_5712_ = crate::leanh::lean_box((v_relaxed_5705_) as usize);
    v___f_5713_ = crate::leanh::lean_alloc_closure(
        l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5713_, 0, v_structName_5704_);
    crate::leanh::lean_closure_set(v___f_5713_, 1, v_toPure_5709_);
    crate::leanh::lean_closure_set(v___f_5713_, 2, v___f_5710_);
    crate::leanh::lean_closure_set(v___f_5713_, 3, v_inst_5702_);
    crate::leanh::lean_closure_set(v___f_5713_, 4, v_inst_5703_);
    crate::leanh::lean_closure_set(v___f_5713_, 5, v___x_5712_);
    crate::leanh::lean_closure_set(v___f_5713_, 6, v_toBind_5707_);
    crate::leanh::lean_closure_set(v___f_5713_, 7, v___f_5711_);
    v___x_5714_ = crate::leanh::lean_apply_4(
        v_toBind_5707_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_5708_,
        v___f_5713_,
    );
    return v___x_5714_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___lam__2(
    mut v_inst_5715_: *mut crate::leanh::LeanObject,
    mut v_inst_5716_: *mut crate::leanh::LeanObject,
    mut v_toBind_5717_: *mut crate::leanh::LeanObject,
    mut v___f_5718_: *mut crate::leanh::LeanObject,
    mut v_parentName_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5720_: u8 = 0;
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5720_ = 1;
    v___x_5721_ = l_Lean_computeStructureResolutionOrder___redArg(
        v_inst_5715_,
        v_inst_5716_,
        v_parentName_5719_,
        v___x_5720_,
    );
    v___x_5722_ = crate::leanh::lean_apply_4(
        v_toBind_5717_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5721_,
        v___f_5718_,
    );
    return v___x_5722_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___redArg___boxed(
    mut v_inst_5723_: *mut crate::leanh::LeanObject,
    mut v_inst_5724_: *mut crate::leanh::LeanObject,
    mut v_structName_5725_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5727_: u8 = 0;
    let mut v_res_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5727_ = (crate::leanh::lean_unbox(v_relaxed_5726_) as u8);
    v_res_5728_ = l_Lean_computeStructureResolutionOrder___redArg(
        v_inst_5723_,
        v_inst_5724_,
        v_structName_5725_,
        v_relaxed_boxed_5727_,
    );
    return v_res_5728_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___redArg___boxed(
    mut v_inst_5729_: *mut crate::leanh::LeanObject,
    mut v_inst_5730_: *mut crate::leanh::LeanObject,
    mut v_structName_5731_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5732_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5734_: u8 = 0;
    let mut v_res_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5734_ = (crate::leanh::lean_unbox(v_relaxed_5733_) as u8);
    v_res_5735_ = l_Lean_mergeStructureResolutionOrders___redArg(
        v_inst_5729_,
        v_inst_5730_,
        v_structName_5731_,
        v_parentNames_5732_,
        v_relaxed_boxed_5734_,
    );
    return v_res_5735_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder(
    mut v_m_5736_: *mut crate::leanh::LeanObject,
    mut v_inst_5737_: *mut crate::leanh::LeanObject,
    mut v_inst_5738_: *mut crate::leanh::LeanObject,
    mut v_structName_5739_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5740_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ = l_Lean_computeStructureResolutionOrder___redArg(
        v_inst_5737_,
        v_inst_5738_,
        v_structName_5739_,
        v_relaxed_5740_,
    );
    return v___x_5741_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___boxed(
    mut v_m_5742_: *mut crate::leanh::LeanObject,
    mut v_inst_5743_: *mut crate::leanh::LeanObject,
    mut v_inst_5744_: *mut crate::leanh::LeanObject,
    mut v_structName_5745_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5747_: u8 = 0;
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5747_ = (crate::leanh::lean_unbox(v_relaxed_5746_) as u8);
    v_res_5748_ = l_Lean_computeStructureResolutionOrder(
        v_m_5742_,
        v_inst_5743_,
        v_inst_5744_,
        v_structName_5745_,
        v_relaxed_boxed_5747_,
    );
    return v_res_5748_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders(
    mut v_m_5749_: *mut crate::leanh::LeanObject,
    mut v_inst_5750_: *mut crate::leanh::LeanObject,
    mut v_inst_5751_: *mut crate::leanh::LeanObject,
    mut v_structName_5752_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5753_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5754_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5755_ = l_Lean_mergeStructureResolutionOrders___redArg(
        v_inst_5750_,
        v_inst_5751_,
        v_structName_5752_,
        v_parentNames_5753_,
        v_relaxed_5754_,
    );
    return v___x_5755_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___boxed(
    mut v_m_5756_: *mut crate::leanh::LeanObject,
    mut v_inst_5757_: *mut crate::leanh::LeanObject,
    mut v_inst_5758_: *mut crate::leanh::LeanObject,
    mut v_structName_5759_: *mut crate::leanh::LeanObject,
    mut v_parentNames_5760_: *mut crate::leanh::LeanObject,
    mut v_relaxed_5761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_relaxed_boxed_5762_: u8 = 0;
    let mut v_res_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_5762_ = (crate::leanh::lean_unbox(v_relaxed_5761_) as u8);
    v_res_5763_ = l_Lean_mergeStructureResolutionOrders(
        v_m_5756_,
        v_inst_5757_,
        v_inst_5758_,
        v_structName_5759_,
        v_parentNames_5760_,
        v_relaxed_boxed_5762_,
    );
    return v_res_5763_;
}
pub unsafe fn l_Lean_getStructureResolutionOrder___redArg___lam__0(
    mut v_x_5764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_resolutionOrder_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_resolutionOrder_5765_ = crate::leanh::lean_ctor_get(v_x_5764_, 0);
    crate::leanh::lean_inc_ref(v_resolutionOrder_5765_);
    return v_resolutionOrder_5765_;
}
pub unsafe fn l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(
    mut v_x_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5767_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_5766_);
    crate::leanh::lean_dec_ref(v_x_5766_);
    return v_res_5767_;
}
pub unsafe fn l_Lean_getStructureResolutionOrder___redArg(
    mut v_inst_5769_: *mut crate::leanh::LeanObject,
    mut v_inst_5770_: *mut crate::leanh::LeanObject,
    mut v_structName_5771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5772_ = crate::leanh::lean_ctor_get(v_inst_5769_, 0);
    v_toFunctor_5773_ = crate::leanh::lean_ctor_get(v_toApplicative_5772_, 0);
    v_map_5774_ = crate::leanh::lean_ctor_get(v_toFunctor_5773_, 0);
    crate::leanh::lean_inc(v_map_5774_);
    v___f_5775_ = l_Lean_getStructureResolutionOrder___redArg___closed__0;
    v___x_5776_ = 1;
    v___x_5777_ = l_Lean_computeStructureResolutionOrder___redArg(
        v_inst_5769_,
        v_inst_5770_,
        v_structName_5771_,
        v___x_5776_,
    );
    v___x_5778_ = crate::leanh::lean_apply_4(
        v_map_5774_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_5775_,
        v___x_5777_,
    );
    return v___x_5778_;
}
pub unsafe fn l_Lean_getStructureResolutionOrder(
    mut v_m_5779_: *mut crate::leanh::LeanObject,
    mut v_inst_5780_: *mut crate::leanh::LeanObject,
    mut v_inst_5781_: *mut crate::leanh::LeanObject,
    mut v_structName_5782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5783_ =
        l_Lean_getStructureResolutionOrder___redArg(v_inst_5780_, v_inst_5781_, v_structName_5782_);
    return v___x_5783_;
}
pub unsafe fn l_Lean_getAllParentStructures___redArg___lam__0(
    mut v___x_5784_: *mut crate::leanh::LeanObject,
    mut v_structName_5785_: *mut crate::leanh::LeanObject,
    mut v_x_5786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5787_ = l_Array_erase___redArg(v___x_5784_, v_x_5786_, v_structName_5785_);
    return v___x_5787_;
}
pub unsafe fn l_Lean_getAllParentStructures___redArg(
    mut v_inst_5788_: *mut crate::leanh::LeanObject,
    mut v_inst_5789_: *mut crate::leanh::LeanObject,
    mut v_structName_5790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5791_ = crate::leanh::lean_ctor_get(v_inst_5788_, 0);
    v_toFunctor_5792_ = crate::leanh::lean_ctor_get(v_toApplicative_5791_, 0);
    v_map_5793_ = crate::leanh::lean_ctor_get(v_toFunctor_5792_, 0);
    crate::leanh::lean_inc(v_map_5793_);
    v___x_5794_ = l_Lean_setStructureParents___redArg___closed__0;
    crate::leanh::lean_inc(v_structName_5790_);
    v___f_5795_ = crate::leanh::lean_alloc_closure(
        l_Lean_getAllParentStructures___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5795_, 0, v___x_5794_);
    crate::leanh::lean_closure_set(v___f_5795_, 1, v_structName_5790_);
    v___x_5796_ =
        l_Lean_getStructureResolutionOrder___redArg(v_inst_5788_, v_inst_5789_, v_structName_5790_);
    v___x_5797_ = crate::leanh::lean_apply_4(
        v_map_5793_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_5795_,
        v___x_5796_,
    );
    return v___x_5797_;
}
pub unsafe fn l_Lean_getAllParentStructures(
    mut v_m_5798_: *mut crate::leanh::LeanObject,
    mut v_inst_5799_: *mut crate::leanh::LeanObject,
    mut v_inst_5800_: *mut crate::leanh::LeanObject,
    mut v_structName_5801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ =
        l_Lean_getAllParentStructures___redArg(v_inst_5799_, v_inst_5800_, v_structName_5801_);
    return v___x_5802_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ProjFns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedStructureState_default = _init_l_Lean_instInhabitedStructureState_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedStructureState_default);
    l___private_Lean_Structure_0__Lean_instInhabitedStructureState =
        _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Structure_0__Lean_instInhabitedStructureState,
    );
    res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Structure_0__Lean_structureExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Structure_0__Lean_structureExt);
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedStructureResolutionState_default =
        _init_l_Lean_instInhabitedStructureResolutionState_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState_default);
    l_Lean_instInhabitedStructureResolutionState =
        _init_l_Lean_instInhabitedStructureResolutionState();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState);
    res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_structureResolutionExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_structureResolutionExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ProjFns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Structure(builtin);
}
