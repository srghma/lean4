// Lean compiler output
// Module: Lean.Meta.DiscrTree.Basic
// Imports: Lean.Meta.DiscrTree.Types Lean.CoreM Init.Data.Range.Polymorphic.Iterators Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binInsertM___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_join;
use crate::r#gen::Init::Data::Format::Instances::l_List_format___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_replaceRef, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_foldl___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_lit___override, l_Lean_Literal_lt,
    l_Lean_annotation_x3f, l_Lean_instBEqFVarId_beq, l_Lean_mkAnnotation, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_paren, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    initialize_Lean_Meta_DiscrTree_Types, l_Lean_Meta_DiscrTree_Key_ctorIdx,
    l_Lean_Meta_DiscrTree_Key_hash___boxed, l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed,
    runtime_initialize_Lean_Meta_DiscrTree_Types,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
pub static l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value:
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
    m_data: [110, 111, 105, 110, 100, 101, 120, 0],
};
static mut l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2838335181370926768 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value:
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
static mut l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instInhabited___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DiscrTree_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_DiscrTree_instInhabited___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DiscrTree_instInhabited___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value:
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
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value:
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
    m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value:
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
    m_data: [75, 101, 121, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value:
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
    m_data: [115, 116, 97, 114, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        4525596147727532808 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value:
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
    m_data: [111, 116, 104, 101, 114, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value)
            as *mut crate::leanh::LeanObject,
        11989153488816012938 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value:
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
    m_data: [108, 105, 116, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value)
            as *mut crate::leanh::LeanObject,
        15074539318474479562 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value:
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
    m_data: [76, 105, 116, 101, 114, 97, 108, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value:
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
    m_data: [110, 97, 116, 86, 97, 108, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value)
            as *mut crate::leanh::LeanObject,
        7001815944269665831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value)
            as *mut crate::leanh::LeanObject,
        9295767770006931264 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value:
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
    m_data: [115, 116, 114, 86, 97, 108, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value)
            as *mut crate::leanh::LeanObject,
        7001815944269665831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2005404019190257220 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value:
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
    m_data: [102, 118, 97, 114, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value)
            as *mut crate::leanh::LeanObject,
        3087321959384269759 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value:
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
    m_data: [70, 86, 97, 114, 73, 100, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value:
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
    m_data: [109, 107, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value)
            as *mut crate::leanh::LeanObject,
        6212595679582900358 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value)
            as *mut crate::leanh::LeanObject,
        6968149084986791158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value:
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
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value)
            as *mut crate::leanh::LeanObject,
        17383108283035838098 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value:
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
    m_data: [97, 114, 114, 111, 119, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value)
            as *mut crate::leanh::LeanObject,
        8457098344818307929 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value:
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
    m_data: [112, 114, 111, 106, 0],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6571394212498793888 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value)
            as *mut crate::leanh::LeanObject,
        12263618261203284320 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instToExprKey___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_DiscrTree_instToExprKey___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12558998168795833107 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
            6571394212498793888 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DiscrTree_instToExprKey___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_DiscrTree_instToExprKey: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_DiscrTree_instLTKey: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_Key_format___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [42, 0],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 151, 190, 0],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__4_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 136, 128, 0],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__6_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_DiscrTree_Key_format___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Key_format___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Key_format___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Key_format___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value:
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
    m_fun: l_Lean_Meta_DiscrTree_Key_format as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_instToFormatKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_DiscrTree_instToFormatKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value:
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
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1_value:
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
        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value:
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
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value:
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
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6_value:
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
        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7_value:
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
        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value:
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
    m_data: [110, 111, 100, 101, 0],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value:
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
    m_data: [32, 0],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value:
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
    m_data: [35, 0],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_format___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_format___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_format___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [60, 111, 116, 104, 101, 114, 62, 0]};
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 136, 128, 32, 0]};
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value:
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
    m_fun: l_Lean_Meta_DiscrTree_Key_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46,
        66, 97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46,
        105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99,
        101, 0,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_DiscrTree_mkNoindexAnnotation(
    mut v_e_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
    v___x_1427_ = l_Lean_mkAnnotation(v___x_1426_, v_e_1425_);
    return v___x_1427_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_hasNoindexAnnotation(
    mut v_e_1428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1;
    v___x_1430_ = l_Lean_annotation_x3f(v___x_1429_, v_e_1428_);
    if crate::leanh::lean_obj_tag(v___x_1430_) == 0 {
        let mut v___x_1431_: u8 = 0;
        v___x_1431_ = 0;
        return v___x_1431_;
    } else {
        let mut v___x_1432_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_1430_, 1);
        v___x_1432_ = 1;
        return v___x_1432_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(
    mut v_e_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: u8 = 0;
    let mut v_r_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1433_);
    crate::leanh::lean_dec_ref(v_e_1433_);
    v_r_1435_ = crate::leanh::lean_box((v_res_1434_) as usize);
    return v_r_1435_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instInhabitedTrie(
    mut v_00_u03b1_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1442_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__0_once),
        _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0,
    );
    v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instInhabited(
    mut v_00_u03b1_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__1_once),
        _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1,
    );
    return v___x_1446_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_empty(
    mut v_00_u03b1_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instInhabited___closed__1_once),
        _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1,
    );
    return v___x_1448_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = crate::leanh::lean_box(0);
    v___x_1461_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5;
    v___x_1462_ = l_Lean_mkConst(v___x_1461_, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = crate::leanh::lean_box(0);
    v___x_1471_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8;
    v___x_1472_ = l_Lean_mkConst(v___x_1471_, v___x_1470_);
    return v___x_1472_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = crate::leanh::lean_box(0);
    v___x_1481_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11;
    v___x_1482_ = l_Lean_mkConst(v___x_1481_, v___x_1480_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = crate::leanh::lean_box(0);
    v___x_1490_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15;
    v___x_1491_ = l_Lean_mkConst(v___x_1490_, v___x_1489_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_box(0);
    v___x_1498_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18;
    v___x_1499_ = l_Lean_mkConst(v___x_1498_, v___x_1497_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = crate::leanh::lean_box(0);
    v___x_1508_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21;
    v___x_1509_ = l_Lean_mkConst(v___x_1508_, v___x_1507_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = crate::leanh::lean_box(0);
    v___x_1517_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25;
    v___x_1518_ = l_Lean_mkConst(v___x_1517_, v___x_1516_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = crate::leanh::lean_box(0);
    v___x_1527_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28;
    v___x_1528_ = l_Lean_mkConst(v___x_1527_, v___x_1526_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_box(0);
    v___x_1537_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31;
    v___x_1538_ = l_Lean_mkConst(v___x_1537_, v___x_1536_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = crate::leanh::lean_box(0);
    v___x_1547_ = l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34;
    v___x_1548_ = l_Lean_mkConst(v___x_1547_, v___x_1546_);
    return v___x_1548_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instToExprKey___lam__0(
    mut v_k_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_1549_) {
        0 => {
            let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1550_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6,
            );
            return v___x_1550_;
        }
        1 => {
            let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1551_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9,
            );
            return v___x_1551_;
        }
        2 => {
            let mut v_a_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1552_ = crate::leanh::lean_ctor_get(v_k_1549_, 0);
            crate::leanh::lean_inc_ref(v_a_1552_);
            crate::leanh::lean_dec_ref_known(v_k_1549_, 1);
            v___x_1553_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12,
            );
            if crate::leanh::lean_obj_tag(v_a_1552_) == 0 {
                let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1554_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16,
                );
                v___x_1555_ = l_Lean_Expr_lit___override(v_a_1552_);
                v___x_1556_ = l_Lean_Expr_app___override(v___x_1554_, v___x_1555_);
                v___x_1557_ = l_Lean_Expr_app___override(v___x_1553_, v___x_1556_);
                return v___x_1557_;
            } else {
                let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1558_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19,
                );
                v___x_1559_ = l_Lean_Expr_lit___override(v_a_1552_);
                v___x_1560_ = l_Lean_Expr_app___override(v___x_1558_, v___x_1559_);
                v___x_1561_ = l_Lean_Expr_app___override(v___x_1553_, v___x_1560_);
                return v___x_1561_;
            }
        }
        3 => {
            let mut v_a_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1562_ = crate::leanh::lean_ctor_get(v_k_1549_, 0);
            crate::leanh::lean_inc(v_a_1562_);
            v_a_1563_ = crate::leanh::lean_ctor_get(v_k_1549_, 1);
            crate::leanh::lean_inc(v_a_1563_);
            crate::leanh::lean_dec_ref_known(v_k_1549_, 2);
            v___x_1564_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22,
            );
            v___x_1565_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26,
            );
            v___x_1566_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1562_);
            v___x_1567_ = l_Lean_Expr_app___override(v___x_1565_, v___x_1566_);
            v___x_1568_ = l_Lean_mkNatLit(v_a_1563_);
            v___x_1569_ = l_Lean_mkAppB(v___x_1564_, v___x_1567_, v___x_1568_);
            return v___x_1569_;
        }
        4 => {
            let mut v_a_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1570_ = crate::leanh::lean_ctor_get(v_k_1549_, 0);
            crate::leanh::lean_inc(v_a_1570_);
            v_a_1571_ = crate::leanh::lean_ctor_get(v_k_1549_, 1);
            crate::leanh::lean_inc(v_a_1571_);
            crate::leanh::lean_dec_ref_known(v_k_1549_, 2);
            v___x_1572_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29,
            );
            v___x_1573_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1570_);
            v___x_1574_ = l_Lean_mkNatLit(v_a_1571_);
            v___x_1575_ = l_Lean_mkAppB(v___x_1572_, v___x_1573_, v___x_1574_);
            return v___x_1575_;
        }
        5 => {
            let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1576_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32,
            );
            return v___x_1576_;
        }
        _ => {
            let mut v_a_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1577_ = crate::leanh::lean_ctor_get(v_k_1549_, 0);
            crate::leanh::lean_inc(v_a_1577_);
            v_a_1578_ = crate::leanh::lean_ctor_get(v_k_1549_, 1);
            crate::leanh::lean_inc(v_a_1578_);
            v_a_1579_ = crate::leanh::lean_ctor_get(v_k_1549_, 2);
            crate::leanh::lean_inc(v_a_1579_);
            crate::leanh::lean_dec_ref_known(v_k_1549_, 3);
            v___x_1580_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35_once
                ),
                _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35,
            );
            v___x_1581_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1577_);
            v___x_1582_ = l_Lean_mkNatLit(v_a_1578_);
            v___x_1583_ = l_Lean_mkNatLit(v_a_1579_);
            v___x_1584_ = l_Lean_mkApp3(v___x_1580_, v___x_1581_, v___x_1582_, v___x_1583_);
            return v___x_1584_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = crate::leanh::lean_box(0);
    v___x_1592_ = l_Lean_Meta_DiscrTree_instToExprKey___closed__1;
    v___x_1593_ = l_Lean_mkConst(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___closed__2_once),
        _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2,
    );
    v___f_1595_ = l_Lean_Meta_DiscrTree_instToExprKey___closed__0;
    v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1596_, 0, v___f_1595_);
    crate::leanh::lean_ctor_set(v___x_1596_, 1, v___x_1594_);
    return v___x_1596_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instToExprKey() -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instToExprKey___closed__3_once),
        _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3,
    );
    return v___x_1597_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_lt(
    mut v_x_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_u2081_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v_a_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u8 = 0;
    let mut v___y_1631_: u8 = 0;
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1598_) {
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_1599_) == 2 {
                        v_a_1606_ = crate::leanh::lean_ctor_get(v_x_1598_, 0);
                        v_a_1607_ = crate::leanh::lean_ctor_get(v_x_1599_, 0);
                        v___x_1608_ = l_Lean_Literal_lt(v_a_1606_, v_a_1607_);
                        return v___x_1608_;
                    } else {
                        v_k_u2081_1601_ = v_x_1598_;
                        v_k_u2082_1602_ = v_x_1599_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_1599_) == 3 {
                        v_a_1609_ = crate::leanh::lean_ctor_get(v_x_1598_, 0);
                        v_a_1610_ = crate::leanh::lean_ctor_get(v_x_1598_, 1);
                        v_a_1611_ = crate::leanh::lean_ctor_get(v_x_1599_, 0);
                        v_a_1612_ = crate::leanh::lean_ctor_get(v_x_1599_, 1);
                        v___x_1613_ = l_Lean_Name_quickLt(v_a_1609_, v_a_1611_);
                        if v___x_1613_ == 0 {
                            v___x_1614_ = l_Lean_instBEqFVarId_beq(v_a_1609_, v_a_1611_);
                            if v___x_1614_ == 0 {
                                return v___x_1614_;
                            } else {
                                v___x_1615_ = lean_nat_dec_lt(v_a_1610_, v_a_1612_);
                                return v___x_1615_;
                            }
                        } else {
                            return v___x_1613_;
                        }
                    } else {
                        v_k_u2081_1601_ = v_x_1598_;
                        v_k_u2082_1602_ = v_x_1599_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_1599_) == 4 {
                        v_a_1616_ = crate::leanh::lean_ctor_get(v_x_1598_, 0);
                        v_a_1617_ = crate::leanh::lean_ctor_get(v_x_1598_, 1);
                        v_a_1618_ = crate::leanh::lean_ctor_get(v_x_1599_, 0);
                        v_a_1619_ = crate::leanh::lean_ctor_get(v_x_1599_, 1);
                        v___x_1620_ = l_Lean_Name_quickLt(v_a_1616_, v_a_1618_);
                        if v___x_1620_ == 0 {
                            v___x_1621_ = lean_name_eq(v_a_1616_, v_a_1618_);
                            if v___x_1621_ == 0 {
                                return v___x_1621_;
                            } else {
                                v___x_1622_ = lean_nat_dec_lt(v_a_1617_, v_a_1619_);
                                return v___x_1622_;
                            }
                        } else {
                            return v___x_1620_;
                        }
                    } else {
                        v_k_u2081_1601_ = v_x_1598_;
                        v_k_u2082_1602_ = v_x_1599_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_x_1599_) == 6 {
                        v_a_1623_ = crate::leanh::lean_ctor_get(v_x_1598_, 0);
                        v_a_1624_ = crate::leanh::lean_ctor_get(v_x_1598_, 1);
                        v_a_1625_ = crate::leanh::lean_ctor_get(v_x_1598_, 2);
                        v_a_1626_ = crate::leanh::lean_ctor_get(v_x_1599_, 0);
                        v_a_1627_ = crate::leanh::lean_ctor_get(v_x_1599_, 1);
                        v_a_1628_ = crate::leanh::lean_ctor_get(v_x_1599_, 2);
                        v___x_1629_ = lean_nat_dec_lt(v_a_1625_, v_a_1628_);
                        v___x_1634_ = l_Lean_Name_quickLt(v_a_1623_, v_a_1626_);
                        if v___x_1634_ == 0 {
                            v___x_1635_ = lean_name_eq(v_a_1623_, v_a_1626_);
                            if v___x_1635_ == 0 {
                                v___y_1631_ = v___x_1635_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1636_ = lean_nat_dec_lt(v_a_1624_, v_a_1627_);
                                v___y_1631_ = v___x_1636_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_1631_ = v___x_1634_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_k_u2081_1601_ = v_x_1598_;
                        v_k_u2082_1602_ = v_x_1599_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_k_u2081_1601_ = v_x_1598_;
                    v_k_u2082_1602_ = v_x_1599_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1603_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_k_u2081_1601_);
                v___x_1604_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_k_u2082_1602_);
                v___x_1605_ = lean_nat_dec_lt(v___x_1603_, v___x_1604_);
                crate::leanh::lean_dec(v___x_1604_);
                crate::leanh::lean_dec(v___x_1603_);
                return v___x_1605_;
            }
            2 => {
                if v___y_1631_ == 0 {
                    v___x_1632_ = lean_name_eq(v_a_1623_, v_a_1626_);
                    if v___x_1632_ == 0 {
                        if v___x_1632_ == 0 {
                            return v___x_1632_;
                        } else {
                            return v___x_1629_;
                        }
                    } else {
                        v___x_1633_ = lean_nat_dec_eq(v_a_1624_, v_a_1627_);
                        if v___x_1633_ == 0 {
                            return v___x_1633_;
                        } else {
                            return v___x_1629_;
                        }
                    }
                } else {
                    return v___y_1631_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_lt___boxed(
    mut v_x_1637_: *mut crate::leanh::LeanObject,
    mut v_x_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: u8 = 0;
    let mut v_r_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Lean_Meta_DiscrTree_Key_lt(v_x_1637_, v_x_1638_);
    crate::leanh::lean_dec(v_x_1638_);
    crate::leanh::lean_dec(v_x_1637_);
    v_r_1640_ = crate::leanh::lean_box((v_res_1639_) as usize);
    return v_r_1640_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instLTKey() -> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = crate::leanh::lean_box(0);
    return v___x_1641_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instDecidableLtKey(
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_b_1643_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1644_: u8 = 0;
    v___x_1644_ = l_Lean_Meta_DiscrTree_Key_lt(v_a_1642_, v_b_1643_);
    return v___x_1644_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instDecidableLtKey___boxed(
    mut v_a_1645_: *mut crate::leanh::LeanObject,
    mut v_b_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: u8 = 0;
    let mut v_r_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Lean_Meta_DiscrTree_instDecidableLtKey(v_a_1645_, v_b_1646_);
    crate::leanh::lean_dec(v_b_1646_);
    crate::leanh::lean_dec(v_a_1645_);
    v_r_1648_ = crate::leanh::lean_box((v_res_1647_) as usize);
    return v_r_1648_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_format(
    mut v_x_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut v_val_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1661_) {
                0 => {
                    v___x_1662_ = l_Lean_Meta_DiscrTree_Key_format___closed__1;
                    return v___x_1662_;
                }
                1 => {
                    v___x_1663_ = l_Lean_Meta_DiscrTree_Key_format___closed__3;
                    return v___x_1663_;
                }
                2 => {
                    v_a_1664_ = crate::leanh::lean_ctor_get(v_x_1661_, 0);
                    crate::leanh::lean_inc_ref(v_a_1664_);
                    crate::leanh::lean_dec_ref_known(v_x_1661_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1664_) == 0 {
                        v_val_1665_ = crate::leanh::lean_ctor_get(v_a_1664_, 0);
                        v_isSharedCheck_1673_ = (!crate::leanh::lean_is_exclusive(v_a_1664_)) as u8;
                        if v_isSharedCheck_1673_ == 0 {
                            v___x_1667_ = v_a_1664_;
                            v_isShared_1668_ = v_isSharedCheck_1673_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1665_);
                            crate::leanh::lean_dec(v_a_1664_);
                            v___x_1667_ = crate::leanh::lean_box(0);
                            v_isShared_1668_ = v_isSharedCheck_1673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_1674_ = crate::leanh::lean_ctor_get(v_a_1664_, 0);
                        v_isSharedCheck_1682_ = (!crate::leanh::lean_is_exclusive(v_a_1664_)) as u8;
                        if v_isSharedCheck_1682_ == 0 {
                            v___x_1676_ = v_a_1664_;
                            v_isShared_1677_ = v_isSharedCheck_1682_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1674_);
                            crate::leanh::lean_dec(v_a_1664_);
                            v___x_1676_ = crate::leanh::lean_box(0);
                            v_isShared_1677_ = v_isSharedCheck_1682_;
                            state = 3;
                            continue;
                        }
                    }
                }
                5 => {
                    v___x_1683_ = l_Lean_Meta_DiscrTree_Key_format___closed__5;
                    return v___x_1683_;
                }
                6 => {
                    v_a_1684_ = crate::leanh::lean_ctor_get(v_x_1661_, 0);
                    crate::leanh::lean_inc(v_a_1684_);
                    v_a_1685_ = crate::leanh::lean_ctor_get(v_x_1661_, 1);
                    crate::leanh::lean_inc(v_a_1685_);
                    crate::leanh::lean_dec_ref_known(v_x_1661_, 3);
                    v___x_1686_ = 1;
                    v___x_1687_ = l_Lean_Name_toString(v_a_1684_, v___x_1686_);
                    v___x_1688_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1687_);
                    v___x_1689_ = l_Lean_Meta_DiscrTree_Key_format___closed__7;
                    v___x_1690_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1690_, 0, v___x_1688_);
                    crate::leanh::lean_ctor_set(v___x_1690_, 1, v___x_1689_);
                    v___x_1691_ = l_Nat_reprFast(v_a_1685_);
                    v___x_1692_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                    v___x_1693_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v___x_1690_);
                    crate::leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                    return v___x_1693_;
                }
                _ => {
                    v_a_1694_ = crate::leanh::lean_ctor_get(v_x_1661_, 0);
                    crate::leanh::lean_inc(v_a_1694_);
                    crate::leanh::lean_dec(v_x_1661_);
                    v___x_1695_ = 1;
                    v___x_1696_ = l_Lean_Name_toString(v_a_1694_, v___x_1695_);
                    v___x_1697_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                    return v___x_1697_;
                }
            },
            1 => {
                v___x_1669_ = l_Nat_reprFast(v_val_1665_);
                if v_isShared_1668_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1667_, 3);
                    crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1669_);
                    v___x_1671_ = v___x_1667_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
                    v___x_1671_ = v_reuseFailAlloc_1672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1671_;
            }
            3 => {
                v___x_1678_ = l_String_quote(v_val_1674_);
                if v_isShared_1677_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1676_, 3);
                    crate::leanh::lean_ctor_set(v___x_1676_, 0, v___x_1678_);
                    v___x_1680_ = v___x_1676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
                    v___x_1680_ = v_reuseFailAlloc_1681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2;
    v___x_1706_ = lean_string_length(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4,
    );
    v___x_1708_ = lean_nat_to_int(v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_format___redArg(
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vs_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___f_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_1724_ = crate::leanh::lean_ctor_get(v_x_1723_, 0);
                v_children_1725_ = crate::leanh::lean_ctor_get(v_x_1723_, 1);
                v_isSharedCheck_1760_ = (!crate::leanh::lean_is_exclusive(v_x_1723_)) as u8;
                if v_isSharedCheck_1760_ == 0 {
                    v___x_1727_ = v_x_1723_;
                    v_isShared_1728_ = v_isSharedCheck_1760_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_1725_);
                    crate::leanh::lean_inc(v_vs_1724_);
                    crate::leanh::lean_dec(v_x_1723_);
                    v___x_1727_ = crate::leanh::lean_box(0);
                    v_isShared_1728_ = v_isSharedCheck_1760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1722_);
                v___f_1729_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1729_, 0, v_inst_1722_);
                v___x_1730_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1;
                v___x_1750_ = lean_array_get_size(v_vs_1724_);
                v___x_1751_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1752_ = lean_nat_dec_eq(v___x_1750_, v___x_1751_);
                if v___x_1752_ == 0 {
                    v___x_1753_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3;
                    v___x_1754_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5;
                    v___x_1755_ = lean_array_to_list(v_vs_1724_);
                    v___x_1756_ = l_List_format___redArg(v_inst_1722_, v___x_1755_);
                    v___x_1757_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1754_);
                    crate::leanh::lean_ctor_set(v___x_1757_, 1, v___x_1756_);
                    v___x_1758_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1753_);
                    crate::leanh::lean_ctor_set(v___x_1758_, 1, v___x_1757_);
                    v___y_1732_ = v___x_1758_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_vs_1724_);
                    crate::leanh::lean_dec_ref(v_inst_1722_);
                    v___x_1759_ = crate::leanh::lean_box(0);
                    v___y_1732_ = v___x_1759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1728_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1727_, 5);
                    crate::leanh::lean_ctor_set(v___x_1727_, 1, v___y_1732_);
                    crate::leanh::lean_ctor_set(v___x_1727_, 0, v___x_1730_);
                    v___x_1734_ = v___x_1727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___y_1732_);
                    v___x_1734_ = v_reuseFailAlloc_1749_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1735_ = lean_array_to_list(v_children_1725_);
                v___x_1736_ = crate::leanh::lean_box(0);
                v___x_1737_ = l_List_mapTR_loop___redArg(v___f_1729_, v___x_1735_, v___x_1736_);
                v___x_1738_ = l_Std_Format_join(v___x_1737_);
                v___x_1739_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1734_);
                crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
                v___x_1740_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5,
                );
                v___x_1741_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6;
                v___x_1742_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1741_);
                crate::leanh::lean_ctor_set(v___x_1742_, 1, v___x_1739_);
                v___x_1743_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7;
                v___x_1744_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1744_, 0, v___x_1742_);
                crate::leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
                v___x_1745_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1740_);
                crate::leanh::lean_ctor_set(v___x_1745_, 1, v___x_1744_);
                v___x_1746_ = 0;
                v___x_1747_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1747_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1746_,
                );
                v___x_1748_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1748_, 0, v___x_1747_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1748_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1746_,
                );
                return v___x_1748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0(
    mut v_inst_1761_: *mut crate::leanh::LeanObject,
    mut v_x_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1763_ = crate::leanh::lean_ctor_get(v_x_1762_, 0);
                v_snd_1764_ = crate::leanh::lean_ctor_get(v_x_1762_, 1);
                v_isSharedCheck_1785_ = (!crate::leanh::lean_is_exclusive(v_x_1762_)) as u8;
                if v_isSharedCheck_1785_ == 0 {
                    v___x_1766_ = v_x_1762_;
                    v_isShared_1767_ = v_isSharedCheck_1785_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1764_);
                    crate::leanh::lean_inc(v_fst_1763_);
                    crate::leanh::lean_dec(v_x_1762_);
                    v___x_1766_ = crate::leanh::lean_box(0);
                    v_isShared_1767_ = v_isSharedCheck_1785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1768_ = crate::leanh::lean_box(1);
                v___x_1769_ = l_Lean_Meta_DiscrTree_Key_format(v_fst_1763_);
                v___x_1770_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1;
                if v_isShared_1767_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1766_, 5);
                    crate::leanh::lean_ctor_set(v___x_1766_, 1, v___x_1770_);
                    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1769_);
                    v___x_1772_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1770_);
                    v___x_1772_ = v_reuseFailAlloc_1784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1773_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_1761_, v_snd_1764_);
                v___x_1774_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1774_, 0, v___x_1772_);
                crate::leanh::lean_ctor_set(v___x_1774_, 1, v___x_1773_);
                v___x_1775_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5,
                );
                v___x_1776_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6;
                v___x_1777_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1776_);
                crate::leanh::lean_ctor_set(v___x_1777_, 1, v___x_1774_);
                v___x_1778_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7;
                v___x_1779_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1777_);
                crate::leanh::lean_ctor_set(v___x_1779_, 1, v___x_1778_);
                v___x_1780_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1775_);
                crate::leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
                v___x_1781_ = 0;
                v___x_1782_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1780_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1782_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1781_,
                );
                v___x_1783_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1768_);
                crate::leanh::lean_ctor_set(v___x_1783_, 1, v___x_1782_);
                return v___x_1783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_format(
    mut v_00_u03b1_1786_: *mut crate::leanh::LeanObject,
    mut v_inst_1787_: *mut crate::leanh::LeanObject,
    mut v_x_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_1787_, v_x_1788_);
    return v___x_1789_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instToFormatTrie___redArg(
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_format as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1791_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1791_, 1, v_inst_1790_);
    return v___x_1791_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instToFormatTrie(
    mut v_00_u03b1_1792_: *mut crate::leanh::LeanObject,
    mut v_inst_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_format as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1794_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1794_, 1, v_inst_1793_);
    return v___x_1794_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_format___redArg___lam__0(
    mut v_inst_1795_: *mut crate::leanh::LeanObject,
    mut v_p_1796_: *mut crate::leanh::LeanObject,
    mut v_k_1797_: *mut crate::leanh::LeanObject,
    mut v_c_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1803_: u8 = 0;
    let mut v___x_1804_: u8 = 0;
    let mut v___y_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1799_ = crate::leanh::lean_ctor_get(v_p_1796_, 0);
                v_snd_1800_ = crate::leanh::lean_ctor_get(v_p_1796_, 1);
                v_isSharedCheck_1829_ = (!crate::leanh::lean_is_exclusive(v_p_1796_)) as u8;
                if v_isSharedCheck_1829_ == 0 {
                    v___x_1802_ = v_p_1796_;
                    v_isShared_1803_ = v_isSharedCheck_1829_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1800_);
                    crate::leanh::lean_inc(v_fst_1799_);
                    crate::leanh::lean_dec(v_p_1796_);
                    v___x_1802_ = crate::leanh::lean_box(0);
                    v_isShared_1803_ = v_isSharedCheck_1829_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1804_ = 0;
                v___x_1826_ = (crate::leanh::lean_unbox(v_fst_1799_) as u8);
                crate::leanh::lean_dec(v_fst_1799_);
                if v___x_1826_ == 0 {
                    v___x_1827_ = crate::leanh::lean_box(1);
                    v___y_1806_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v___x_1828_ = crate::leanh::lean_box(0);
                    v___y_1806_ = v___x_1828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_1806_);
                v___x_1807_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1807_, 0, v_snd_1800_);
                crate::leanh::lean_ctor_set(v___x_1807_, 1, v___y_1806_);
                v___x_1808_ = l_Lean_Meta_DiscrTree_Key_format(v_k_1797_);
                v___x_1809_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1;
                v___x_1810_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1810_, 0, v___x_1808_);
                crate::leanh::lean_ctor_set(v___x_1810_, 1, v___x_1809_);
                v___x_1811_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_1795_, v_c_1798_);
                v___x_1812_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1810_);
                crate::leanh::lean_ctor_set(v___x_1812_, 1, v___x_1811_);
                v___x_1813_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5,
                );
                v___x_1814_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6;
                v___x_1815_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
                crate::leanh::lean_ctor_set(v___x_1815_, 1, v___x_1812_);
                v___x_1816_ = l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7;
                v___x_1817_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1817_, 0, v___x_1815_);
                crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                v___x_1818_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1818_, 0, v___x_1813_);
                crate::leanh::lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                v___x_1819_ = 0;
                v___x_1820_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1818_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1819_,
                );
                v___x_1821_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1807_);
                crate::leanh::lean_ctor_set(v___x_1821_, 1, v___x_1820_);
                v___x_1822_ = crate::leanh::lean_box((v___x_1804_) as usize);
                if v_isShared_1803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1802_, 1, v___x_1821_);
                    crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1822_);
                    v___x_1824_ = v___x_1802_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1821_);
                    v___x_1824_ = v_reuseFailAlloc_1825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_format___redArg(
    mut v_inst_1834_: *mut crate::leanh::LeanObject,
    mut v_d_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1836_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_DiscrTree_format___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1836_, 0, v_inst_1834_);
    v___x_1837_ = l_Lean_Meta_DiscrTree_format___redArg___closed__0;
    v___x_1838_ = l_Lean_PersistentHashMap_foldl___redArg(v_d_1835_, v___f_1836_, v___x_1837_);
    v_snd_1839_ = crate::leanh::lean_ctor_get(v___x_1838_, 1);
    crate::leanh::lean_inc(v_snd_1839_);
    crate::leanh::lean_dec(v___x_1838_);
    v___x_1840_ = 0;
    v___x_1841_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1841_, 0, v_snd_1839_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1841_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1840_,
    );
    return v___x_1841_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_format(
    mut v_00_u03b1_1842_: *mut crate::leanh::LeanObject,
    mut v_inst_1843_: *mut crate::leanh::LeanObject,
    mut v_d_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = l_Lean_Meta_DiscrTree_format___redArg(v_inst_1843_, v_d_1844_);
    return v___x_1845_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instToFormat___redArg(
    mut v_inst_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_DiscrTree_format as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1847_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1847_, 1, v_inst_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instToFormat(
    mut v_00_u03b1_1848_: *mut crate::leanh::LeanObject,
    mut v_inst_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_DiscrTree_format as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1850_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1850_, 1, v_inst_1849_);
    return v___x_1850_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(
    mut v_a_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = lean_st_ref_get(v_a_1851_);
    if crate::leanh::lean_obj_tag(v___x_1853_) == 1 {
        let mut v_head_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1854_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
        crate::leanh::lean_inc(v_head_1854_);
        v_tail_1855_ = crate::leanh::lean_ctor_get(v___x_1853_, 1);
        crate::leanh::lean_inc(v_tail_1855_);
        crate::leanh::lean_dec_ref_known(v___x_1853_, 2);
        v___x_1856_ = lean_st_ref_set(v_a_1851_, v_tail_1855_);
        v___x_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1857_, 0, v_head_1854_);
        v___x_1858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
        return v___x_1858_;
    } else {
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1853_);
        v___x_1859_ = crate::leanh::lean_box(0);
        v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
        return v___x_1860_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg___boxed(
    mut v_a_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_1861_);
    crate::leanh::lean_dec(v_a_1861_);
    return v_res_1863_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_1864_);
    return v___x_1868_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___boxed(
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
    mut v_a_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(
            v_a_1869_, v_a_1870_, v_a_1871_,
        );
    crate::leanh::lean_dec(v_a_1871_);
    crate::leanh::lean_dec_ref(v_a_1870_);
    crate::leanh::lean_dec(v_a_1869_);
    return v_res_1873_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = crate::leanh::lean_box(1);
    v___x_1875_ = l_Lean_MessageData_ofFormat(v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(
    mut v_as_1876_: *mut crate::leanh::LeanObject,
    mut v_sz_1877_: usize,
    mut v_i_1878_: usize,
    mut v_b_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: usize = 0;
    let mut v___x_1888_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1881_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
                if v___x_1881_ == 0 {
                    v___x_1882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1882_, 0, v_b_1879_);
                    return v___x_1882_;
                } else {
                    v_a_1883_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
                    v___x_1884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0);
                    v___x_1885_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1885_, 0, v_b_1879_);
                    crate::leanh::lean_ctor_set(v___x_1885_, 1, v___x_1884_);
                    crate::leanh::lean_inc(v_a_1883_);
                    v___x_1886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1885_);
                    crate::leanh::lean_ctor_set(v___x_1886_, 1, v_a_1883_);
                    v___x_1887_ = 1usize;
                    v___x_1888_ = lean_usize_add(v_i_1878_, v___x_1887_);
                    v_i_1878_ = v___x_1888_;
                    v_b_1879_ = v___x_1886_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___boxed(
    mut v_as_1890_: *mut crate::leanh::LeanObject,
    mut v_sz_1891_: *mut crate::leanh::LeanObject,
    mut v_i_1892_: *mut crate::leanh::LeanObject,
    mut v_b_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1895_: usize = 0;
    let mut v_i_boxed_1896_: usize = 0;
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1895_ = crate::leanh::lean_unbox_usize(v_sz_1891_);
    crate::leanh::lean_dec(v_sz_1891_);
    v_i_boxed_1896_ = crate::leanh::lean_unbox_usize(v_i_1892_);
    crate::leanh::lean_dec(v_i_1892_);
    v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_1890_, v_sz_boxed_1895_, v_i_boxed_1896_, v_b_1893_);
    crate::leanh::lean_dec_ref(v_as_1890_);
    return v_res_1897_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0;
    v_r_1900_ = l_Lean_stringToMessageData(v___x_1899_);
    return v_r_1900_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(
    mut v_f_1901_: *mut crate::leanh::LeanObject,
    mut v_args_1902_: *mut crate::leanh::LeanObject,
    mut v_parenIfNonAtomic_1903_: u8,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v_r_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1911_: usize = 0;
    let mut v___x_1912_: usize = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1907_ = lean_array_get_size(v_args_1902_);
                v___x_1908_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1909_ = lean_nat_dec_eq(v___x_1907_, v___x_1908_);
                if v___x_1909_ == 0 {
                    v_r_1910_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1_once), _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1);
                    v_sz_1911_ = lean_array_size(v_args_1902_);
                    v___x_1912_ = 0usize;
                    v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_args_1902_, v_sz_1911_, v___x_1912_, v_r_1910_);
                    if crate::leanh::lean_obj_tag(v___x_1913_) == 0 {
                        v_a_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                        v_isSharedCheck_1929_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1913_)) as u8;
                        if v_isSharedCheck_1929_ == 0 {
                            v___x_1916_ = v___x_1913_;
                            v_isShared_1917_ = v_isSharedCheck_1929_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1914_);
                            crate::leanh::lean_dec(v___x_1913_);
                            v___x_1916_ = crate::leanh::lean_box(0);
                            v_isShared_1917_ = v_isSharedCheck_1929_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_1901_);
                        return v___x_1913_;
                    }
                } else {
                    v___x_1930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1930_, 0, v_f_1901_);
                    return v___x_1930_;
                }
            }
            1 => {
                v___x_1918_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1919_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1919_, 0, v___x_1918_);
                crate::leanh::lean_ctor_set(v___x_1919_, 1, v_a_1914_);
                v___x_1920_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1920_, 0, v_f_1901_);
                crate::leanh::lean_ctor_set(v___x_1920_, 1, v___x_1919_);
                if v_parenIfNonAtomic_1903_ == 0 {
                    v___x_1921_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1920_);
                    if v_isShared_1917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1921_);
                        v___x_1923_ = v___x_1916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
                        v___x_1923_ = v_reuseFailAlloc_1924_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1925_ = l_Lean_MessageData_paren(v___x_1920_);
                    if v_isShared_1917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1925_);
                        v___x_1927_ = v___x_1916_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
                        v___x_1927_ = v_reuseFailAlloc_1928_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1923_;
            }
            3 => {
                return v___x_1927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___boxed(
    mut v_f_1931_: *mut crate::leanh::LeanObject,
    mut v_args_1932_: *mut crate::leanh::LeanObject,
    mut v_parenIfNonAtomic_1933_: *mut crate::leanh::LeanObject,
    mut v_a_1934_: *mut crate::leanh::LeanObject,
    mut v_a_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_parenIfNonAtomic_boxed_1937_: u8 = 0;
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_parenIfNonAtomic_boxed_1937_ = (crate::leanh::lean_unbox(v_parenIfNonAtomic_1933_) as u8);
    v_res_1938_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(
        v_f_1931_,
        v_args_1932_,
        v_parenIfNonAtomic_boxed_1937_,
        v_a_1934_,
        v_a_1935_,
    );
    crate::leanh::lean_dec(v_a_1935_);
    crate::leanh::lean_dec_ref(v_a_1934_);
    crate::leanh::lean_dec_ref(v_args_1932_);
    return v_res_1938_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(
    mut v_as_1939_: *mut crate::leanh::LeanObject,
    mut v_sz_1940_: usize,
    mut v_i_1941_: usize,
    mut v_b_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_1939_, v_sz_1940_, v_i_1941_, v_b_1942_);
    return v___x_1946_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___boxed(
    mut v_as_1947_: *mut crate::leanh::LeanObject,
    mut v_sz_1948_: *mut crate::leanh::LeanObject,
    mut v_i_1949_: *mut crate::leanh::LeanObject,
    mut v_b_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1954_: usize = 0;
    let mut v_i_boxed_1955_: usize = 0;
    let mut v_res_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1954_ = crate::leanh::lean_unbox_usize(v_sz_1948_);
    crate::leanh::lean_dec(v_sz_1948_);
    v_i_boxed_1955_ = crate::leanh::lean_unbox_usize(v_i_1949_);
    crate::leanh::lean_dec(v_i_1949_);
    v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(v_as_1947_, v_sz_boxed_1954_, v_i_boxed_1955_, v_b_1950_, v___y_1951_, v___y_1952_);
    crate::leanh::lean_dec(v___y_1952_);
    crate::leanh::lean_dec_ref(v___y_1951_);
    crate::leanh::lean_dec_ref(v_as_1947_);
    return v_res_1956_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1957_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0);
    v___x_1959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
    v___x_1961_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1962_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    crate::leanh::lean_ctor_set(v___x_1962_, 1, v___x_1961_);
    crate::leanh::lean_ctor_set(v___x_1962_, 2, v___x_1961_);
    crate::leanh::lean_ctor_set(v___x_1962_, 3, v___x_1961_);
    crate::leanh::lean_ctor_set(v___x_1962_, 4, v___x_1960_);
    crate::leanh::lean_ctor_set(v___x_1962_, 5, v___x_1960_);
    crate::leanh::lean_ctor_set(v___x_1962_, 6, v___x_1960_);
    crate::leanh::lean_ctor_set(v___x_1962_, 7, v___x_1960_);
    crate::leanh::lean_ctor_set(v___x_1962_, 8, v___x_1960_);
    crate::leanh::lean_ctor_set(v___x_1962_, 9, v___x_1960_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1964_ = lean_mk_empty_array_with_capacity(v___x_1963_);
    v___x_1965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = 5usize;
    v___x_1967_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1968_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1969_ = lean_mk_empty_array_with_capacity(v___x_1968_);
    v___x_1970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3);
    v___x_1971_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1971_, 0, v___x_1970_);
    crate::leanh::lean_ctor_set(v___x_1971_, 1, v___x_1969_);
    crate::leanh::lean_ctor_set(v___x_1971_, 2, v___x_1967_);
    crate::leanh::lean_ctor_set(v___x_1971_, 3, v___x_1967_);
    crate::leanh::lean_ctor_set_usize(v___x_1971_, 4, v___x_1966_);
    return v___x_1971_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = crate::leanh::lean_box(1);
    v___x_1973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4);
    v___x_1974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
    v___x_1975_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1975_, 0, v___x_1974_);
    crate::leanh::lean_ctor_set(v___x_1975_, 1, v___x_1973_);
    crate::leanh::lean_ctor_set(v___x_1975_, 2, v___x_1972_);
    return v___x_1975_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(
    mut v_msgData_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = lean_st_ref_get(v___y_1978_);
    v_env_1981_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
    crate::leanh::lean_inc_ref(v_env_1981_);
    crate::leanh::lean_dec(v___x_1980_);
    v_options_1982_ = crate::leanh::lean_ctor_get(v___y_1977_, 2);
    v___x_1983_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
    v___x_1984_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
    crate::leanh::lean_inc_ref(v_options_1982_);
    v___x_1985_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1985_, 0, v_env_1981_);
    crate::leanh::lean_ctor_set(v___x_1985_, 1, v___x_1983_);
    crate::leanh::lean_ctor_set(v___x_1985_, 2, v___x_1984_);
    crate::leanh::lean_ctor_set(v___x_1985_, 3, v_options_1982_);
    v___x_1986_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1986_, 0, v___x_1985_);
    crate::leanh::lean_ctor_set(v___x_1986_, 1, v_msgData_1976_);
    v___x_1987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1986_);
    return v___x_1987_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(
    mut v_msgData_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1988_, v___y_1989_, v___y_1990_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_msg_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1997_ = crate::leanh::lean_ctor_get(v___y_1994_, 5);
                v___x_1998_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1993_, v___y_1994_, v___y_1995_);
                v_a_1999_ = crate::leanh::lean_ctor_get(v___x_1998_, 0);
                v_isSharedCheck_2007_ = (!crate::leanh::lean_is_exclusive(v___x_1998_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    v_isShared_2002_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1999_);
                    crate::leanh::lean_dec(v___x_1998_);
                    v___x_2001_ = crate::leanh::lean_box(0);
                    v_isShared_2002_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1997_);
                v___x_2003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2003_, 0, v_ref_1997_);
                crate::leanh::lean_ctor_set(v___x_2003_, 1, v_a_1999_);
                if v_isShared_2002_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2001_, 1);
                    crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_2003_);
                    v___x_2005_ = v___x_2001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_msg_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
    mut v___y_2010_: *mut crate::leanh::LeanObject,
    mut v___y_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2008_, v___y_2009_, v___y_2010_);
    crate::leanh::lean_dec(v___y_2010_);
    crate::leanh::lean_dec_ref(v___y_2009_);
    return v_res_2012_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(
    mut v_ref_2013_: *mut crate::leanh::LeanObject,
    mut v_msg_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2031_: u8 = 0;
    let mut v_cancelTk_x3f_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2033_: u8 = 0;
    let mut v_inheritedTraceOptions_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2019_ = crate::leanh::lean_ctor_get(v___y_2016_, 0);
    v_fileMap_2020_ = crate::leanh::lean_ctor_get(v___y_2016_, 1);
    v_options_2021_ = crate::leanh::lean_ctor_get(v___y_2016_, 2);
    v_currRecDepth_2022_ = crate::leanh::lean_ctor_get(v___y_2016_, 3);
    v_maxRecDepth_2023_ = crate::leanh::lean_ctor_get(v___y_2016_, 4);
    v_ref_2024_ = crate::leanh::lean_ctor_get(v___y_2016_, 5);
    v_currNamespace_2025_ = crate::leanh::lean_ctor_get(v___y_2016_, 6);
    v_openDecls_2026_ = crate::leanh::lean_ctor_get(v___y_2016_, 7);
    v_initHeartbeats_2027_ = crate::leanh::lean_ctor_get(v___y_2016_, 8);
    v_maxHeartbeats_2028_ = crate::leanh::lean_ctor_get(v___y_2016_, 9);
    v_quotContext_2029_ = crate::leanh::lean_ctor_get(v___y_2016_, 10);
    v_currMacroScope_2030_ = crate::leanh::lean_ctor_get(v___y_2016_, 11);
    v_diag_2031_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2016_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2032_ = crate::leanh::lean_ctor_get(v___y_2016_, 12);
    v_suppressElabErrors_2033_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2016_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2034_ = crate::leanh::lean_ctor_get(v___y_2016_, 13);
    v_ref_2035_ = l_Lean_replaceRef(v_ref_2013_, v_ref_2024_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2034_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2032_);
    crate::leanh::lean_inc(v_currMacroScope_2030_);
    crate::leanh::lean_inc(v_quotContext_2029_);
    crate::leanh::lean_inc(v_maxHeartbeats_2028_);
    crate::leanh::lean_inc(v_initHeartbeats_2027_);
    crate::leanh::lean_inc(v_openDecls_2026_);
    crate::leanh::lean_inc(v_currNamespace_2025_);
    crate::leanh::lean_inc(v_maxRecDepth_2023_);
    crate::leanh::lean_inc(v_currRecDepth_2022_);
    crate::leanh::lean_inc_ref(v_options_2021_);
    crate::leanh::lean_inc_ref(v_fileMap_2020_);
    crate::leanh::lean_inc_ref(v_fileName_2019_);
    v___x_2036_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2036_, 0, v_fileName_2019_);
    crate::leanh::lean_ctor_set(v___x_2036_, 1, v_fileMap_2020_);
    crate::leanh::lean_ctor_set(v___x_2036_, 2, v_options_2021_);
    crate::leanh::lean_ctor_set(v___x_2036_, 3, v_currRecDepth_2022_);
    crate::leanh::lean_ctor_set(v___x_2036_, 4, v_maxRecDepth_2023_);
    crate::leanh::lean_ctor_set(v___x_2036_, 5, v_ref_2035_);
    crate::leanh::lean_ctor_set(v___x_2036_, 6, v_currNamespace_2025_);
    crate::leanh::lean_ctor_set(v___x_2036_, 7, v_openDecls_2026_);
    crate::leanh::lean_ctor_set(v___x_2036_, 8, v_initHeartbeats_2027_);
    crate::leanh::lean_ctor_set(v___x_2036_, 9, v_maxHeartbeats_2028_);
    crate::leanh::lean_ctor_set(v___x_2036_, 10, v_quotContext_2029_);
    crate::leanh::lean_ctor_set(v___x_2036_, 11, v_currMacroScope_2030_);
    crate::leanh::lean_ctor_set(v___x_2036_, 12, v_cancelTk_x3f_2032_);
    crate::leanh::lean_ctor_set(v___x_2036_, 13, v_inheritedTraceOptions_2034_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2036_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2031_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2036_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2033_,
    );
    v___x_2037_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2014_, v___x_2036_, v___y_2017_);
    crate::leanh::lean_dec_ref_known(v___x_2036_, 14);
    return v___x_2037_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_2038_: *mut crate::leanh::LeanObject,
    mut v_msg_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_2038_, v_msg_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
    crate::leanh::lean_dec(v___y_2042_);
    crate::leanh::lean_dec_ref(v___y_2041_);
    crate::leanh::lean_dec(v___y_2040_);
    crate::leanh::lean_dec(v_ref_2038_);
    return v_res_2044_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0;
    v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
    return v___x_2047_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2;
    v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
    return v___x_2050_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4;
    v___x_2053_ = l_Lean_stringToMessageData(v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_2056_ = l_Lean_stringToMessageData(v___x_2055_);
    return v___x_2056_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_2059_ = l_Lean_stringToMessageData(v___x_2058_);
    return v___x_2059_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2061_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_2062_ = l_Lean_stringToMessageData(v___x_2061_);
    return v___x_2062_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_2065_ = l_Lean_stringToMessageData(v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(
    mut v_msg_2066_: *mut crate::leanh::LeanObject,
    mut v_declHint_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v_isExporting_2073_: u8 = 0;
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: u8 = 0;
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2070_ = lean_st_ref_get(v___y_2068_);
                v_env_2071_ = crate::leanh::lean_ctor_get(v___x_2070_, 0);
                crate::leanh::lean_inc_ref(v_env_2071_);
                crate::leanh::lean_dec(v___x_2070_);
                v___x_2072_ = l_Lean_Name_isAnonymous(v_declHint_2067_);
                if v___x_2072_ == 0 {
                    v_isExporting_2073_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2073_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2071_);
                        crate::leanh::lean_dec(v_declHint_2067_);
                        v___x_2074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2074_, 0, v_msg_2066_);
                        return v___x_2074_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2071_);
                        v___x_2075_ = l_Lean_Environment_setExporting(v_env_2071_, v___x_2072_);
                        crate::leanh::lean_inc(v_declHint_2067_);
                        crate::leanh::lean_inc_ref(v___x_2075_);
                        v___x_2076_ = l_Lean_Environment_contains(
                            v___x_2075_,
                            v_declHint_2067_,
                            v_isExporting_2073_,
                        );
                        if v___x_2076_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2075_);
                            crate::leanh::lean_dec_ref(v_env_2071_);
                            crate::leanh::lean_dec(v_declHint_2067_);
                            v___x_2077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2077_, 0, v_msg_2066_);
                            return v___x_2077_;
                        } else {
                            v___x_2078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
                            v___x_2079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
                            v___x_2080_ = l_Lean_Options_empty;
                            v___x_2081_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2081_, 0, v___x_2075_);
                            crate::leanh::lean_ctor_set(v___x_2081_, 1, v___x_2078_);
                            crate::leanh::lean_ctor_set(v___x_2081_, 2, v___x_2079_);
                            crate::leanh::lean_ctor_set(v___x_2081_, 3, v___x_2080_);
                            crate::leanh::lean_inc(v_declHint_2067_);
                            v___x_2082_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2067_, v___x_2072_);
                            v_c_2083_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2083_, 0, v___x_2081_);
                            crate::leanh::lean_ctor_set(v_c_2083_, 1, v___x_2082_);
                            v___x_2084_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2071_,
                                v_declHint_2067_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2084_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2071_);
                                crate::leanh::lean_dec(v_declHint_2067_);
                                v___x_2085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
                                v___x_2086_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                                crate::leanh::lean_ctor_set(v___x_2086_, 1, v_c_2083_);
                                v___x_2087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
                                v___x_2088_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2086_);
                                crate::leanh::lean_ctor_set(v___x_2088_, 1, v___x_2087_);
                                v___x_2089_ = l_Lean_MessageData_note(v___x_2088_);
                                v___x_2090_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2090_, 0, v_msg_2066_);
                                crate::leanh::lean_ctor_set(v___x_2090_, 1, v___x_2089_);
                                v___x_2091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2091_, 0, v___x_2090_);
                                return v___x_2091_;
                            } else {
                                v_val_2092_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                                v_isSharedCheck_2127_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2084_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2094_ = v___x_2084_;
                                    v_isShared_2095_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2092_);
                                    crate::leanh::lean_dec(v___x_2084_);
                                    v___x_2094_ = crate::leanh::lean_box(0);
                                    v_isShared_2095_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2071_);
                    crate::leanh::lean_dec(v_declHint_2067_);
                    v___x_2128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2128_, 0, v_msg_2066_);
                    return v___x_2128_;
                }
            }
            1 => {
                v___x_2096_ = crate::leanh::lean_box(0);
                v___x_2097_ = l_Lean_Environment_header(v_env_2071_);
                crate::leanh::lean_dec_ref(v_env_2071_);
                v___x_2098_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2097_);
                v_mod_2099_ = lean_array_get(v___x_2096_, v___x_2098_, v_val_2092_);
                crate::leanh::lean_dec(v_val_2092_);
                crate::leanh::lean_dec_ref(v___x_2098_);
                v___x_2100_ = l_Lean_isPrivateName(v_declHint_2067_);
                crate::leanh::lean_dec(v_declHint_2067_);
                if v___x_2100_ == 0 {
                    v___x_2101_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
                    v___x_2102_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 1, v_c_2083_);
                    v___x_2103_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_2104_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2102_);
                    crate::leanh::lean_ctor_set(v___x_2104_, 1, v___x_2103_);
                    v___x_2105_ = l_Lean_MessageData_ofName(v_mod_2099_);
                    v___x_2106_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2104_);
                    crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2105_);
                    v___x_2107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
                    v___x_2108_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2106_);
                    crate::leanh::lean_ctor_set(v___x_2108_, 1, v___x_2107_);
                    v___x_2109_ = l_Lean_MessageData_note(v___x_2108_);
                    v___x_2110_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2110_, 0, v_msg_2066_);
                    crate::leanh::lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                    if v_isShared_2095_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2094_, 0);
                        crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2110_);
                        v___x_2112_ = v___x_2094_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
                        v___x_2112_ = v_reuseFailAlloc_2113_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2114_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
                    v___x_2115_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___x_2114_);
                    crate::leanh::lean_ctor_set(v___x_2115_, 1, v_c_2083_);
                    v___x_2116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_2117_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2115_);
                    crate::leanh::lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                    v___x_2118_ = l_Lean_MessageData_ofName(v_mod_2099_);
                    v___x_2119_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2117_);
                    crate::leanh::lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                    v___x_2120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_2121_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2119_);
                    crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2120_);
                    v___x_2122_ = l_Lean_MessageData_note(v___x_2121_);
                    v___x_2123_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2123_, 0, v_msg_2066_);
                    crate::leanh::lean_ctor_set(v___x_2123_, 1, v___x_2122_);
                    if v_isShared_2095_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2094_, 0);
                        crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2123_);
                        v___x_2125_ = v___x_2094_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
                        v___x_2125_ = v_reuseFailAlloc_2126_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2112_;
            }
            3 => {
                return v___x_2125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_msg_2129_: *mut crate::leanh::LeanObject,
    mut v_declHint_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2133_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2129_, v_declHint_2130_, v___y_2131_);
    crate::leanh::lean_dec(v___y_2131_);
    return v_res_2133_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(
    mut v_msg_2134_: *mut crate::leanh::LeanObject,
    mut v_declHint_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2140_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2134_, v_declHint_2135_, v___y_2138_);
                v_a_2141_ = crate::leanh::lean_ctor_get(v___x_2140_, 0);
                v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v___x_2140_)) as u8;
                if v_isSharedCheck_2150_ == 0 {
                    v___x_2143_ = v___x_2140_;
                    v_isShared_2144_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2141_);
                    crate::leanh::lean_dec(v___x_2140_);
                    v___x_2143_ = crate::leanh::lean_box(0);
                    v_isShared_2144_ = v_isSharedCheck_2150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2145_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2146_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                crate::leanh::lean_ctor_set(v___x_2146_, 1, v_a_2141_);
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2146_);
                    v___x_2148_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msg_2151_: *mut crate::leanh::LeanObject,
    mut v_declHint_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_2151_, v_declHint_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
    crate::leanh::lean_dec(v___y_2155_);
    crate::leanh::lean_dec_ref(v___y_2154_);
    crate::leanh::lean_dec(v___y_2153_);
    return v_res_2157_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(
    mut v_ref_2158_: *mut crate::leanh::LeanObject,
    mut v_msg_2159_: *mut crate::leanh::LeanObject,
    mut v_declHint_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_2159_, v_declHint_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
    v_a_2166_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
    crate::leanh::lean_inc(v_a_2166_);
    crate::leanh::lean_dec_ref(v___x_2165_);
    v___x_2167_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_2158_, v_a_2166_, v___y_2161_, v___y_2162_, v___y_2163_);
    return v___x_2167_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_ref_2168_: *mut crate::leanh::LeanObject,
    mut v_msg_2169_: *mut crate::leanh::LeanObject,
    mut v_declHint_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2175_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2168_, v_msg_2169_, v_declHint_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
    crate::leanh::lean_dec(v___y_2173_);
    crate::leanh::lean_dec_ref(v___y_2172_);
    crate::leanh::lean_dec(v___y_2171_);
    crate::leanh::lean_dec(v_ref_2168_);
    return v_res_2175_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_ref_2182_: *mut crate::leanh::LeanObject,
    mut v_constName_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
    v___x_2189_ = 0;
    crate::leanh::lean_inc(v_constName_2183_);
    v___x_2190_ = l_Lean_MessageData_ofConstName(v_constName_2183_, v___x_2189_);
    v___x_2191_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2188_);
    crate::leanh::lean_ctor_set(v___x_2191_, 1, v___x_2190_);
    v___x_2192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3);
    v___x_2193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2193_, 0, v___x_2191_);
    crate::leanh::lean_ctor_set(v___x_2193_, 1, v___x_2192_);
    v___x_2194_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2182_, v___x_2193_, v_constName_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
    return v___x_2194_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_ref_2195_: *mut crate::leanh::LeanObject,
    mut v_constName_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2195_, v_constName_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
    crate::leanh::lean_dec(v___y_2199_);
    crate::leanh::lean_dec_ref(v___y_2198_);
    crate::leanh::lean_dec(v___y_2197_);
    crate::leanh::lean_dec(v_ref_2195_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(
    mut v_constName_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2207_ = crate::leanh::lean_ctor_get(v___y_2204_, 5);
    v___x_2208_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2207_, v_constName_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
    return v___x_2208_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_constName_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
    crate::leanh::lean_dec(v___y_2212_);
    crate::leanh::lean_dec_ref(v___y_2211_);
    crate::leanh::lean_dec(v___y_2210_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(
    mut v_constName_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_st_ref_get(v___y_2218_);
                v_env_2221_ = crate::leanh::lean_ctor_get(v___x_2220_, 0);
                crate::leanh::lean_inc_ref(v_env_2221_);
                crate::leanh::lean_dec(v___x_2220_);
                v___x_2222_ = 0;
                crate::leanh::lean_inc(v_constName_2215_);
                v___x_2223_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2221_,
                    v_constName_2215_,
                    v___x_2222_,
                );
                if crate::leanh::lean_obj_tag(v___x_2223_) == 0 {
                    v___x_2224_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
                    return v___x_2224_;
                } else {
                    crate::leanh::lean_dec(v_constName_2215_);
                    v_val_2225_ = crate::leanh::lean_ctor_get(v___x_2223_, 0);
                    v_isSharedCheck_2232_ = (!crate::leanh::lean_is_exclusive(v___x_2223_)) as u8;
                    if v_isSharedCheck_2232_ == 0 {
                        v___x_2227_ = v___x_2223_;
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2225_);
                        crate::leanh::lean_dec(v___x_2223_);
                        v___x_2227_ = crate::leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2228_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2227_, 0);
                    v___x_2230_ = v___x_2227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_val_2225_);
                    v___x_2230_ = v_reuseFailAlloc_2231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(
    mut v_constName_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
    crate::leanh::lean_dec(v___y_2236_);
    crate::leanh::lean_dec_ref(v___y_2235_);
    crate::leanh::lean_dec(v___y_2234_);
    return v_res_2238_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(
    mut v_a_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2239_) == 0 {
                    v___x_2241_ = l_List_reverse___redArg(v_a_2240_);
                    return v___x_2241_;
                } else {
                    v_head_2242_ = crate::leanh::lean_ctor_get(v_a_2239_, 0);
                    v_tail_2243_ = crate::leanh::lean_ctor_get(v_a_2239_, 1);
                    v_isSharedCheck_2252_ = (!crate::leanh::lean_is_exclusive(v_a_2239_)) as u8;
                    if v_isSharedCheck_2252_ == 0 {
                        v___x_2245_ = v_a_2239_;
                        v_isShared_2246_ = v_isSharedCheck_2252_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2243_);
                        crate::leanh::lean_inc(v_head_2242_);
                        crate::leanh::lean_dec(v_a_2239_);
                        v___x_2245_ = crate::leanh::lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2247_ = l_Lean_mkLevelParam(v_head_2242_);
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 1, v_a_2240_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2247_);
                    v___x_2249_ = v___x_2245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_a_2240_);
                    v___x_2249_ = v_reuseFailAlloc_2251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2239_ = v_tail_2243_;
                v_a_2240_ = v___x_2249_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(
    mut v_constName_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_levelParams_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_2253_);
                v___x_2258_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
                if crate::leanh::lean_obj_tag(v___x_2258_) == 0 {
                    v_a_2259_ = crate::leanh::lean_ctor_get(v___x_2258_, 0);
                    v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v___x_2258_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2261_ = v___x_2258_;
                        v_isShared_2262_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2259_);
                        crate::leanh::lean_dec(v___x_2258_);
                        v___x_2261_ = crate::leanh::lean_box(0);
                        v_isShared_2262_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_2253_);
                    v_a_2271_ = crate::leanh::lean_ctor_get(v___x_2258_, 0);
                    v_isSharedCheck_2278_ = (!crate::leanh::lean_is_exclusive(v___x_2258_)) as u8;
                    if v_isSharedCheck_2278_ == 0 {
                        v___x_2273_ = v___x_2258_;
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2271_);
                        crate::leanh::lean_dec(v___x_2258_);
                        v___x_2273_ = crate::leanh::lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_2263_ = crate::leanh::lean_ctor_get(v_a_2259_, 1);
                crate::leanh::lean_inc(v_levelParams_2263_);
                crate::leanh::lean_dec(v_a_2259_);
                v___x_2264_ = crate::leanh::lean_box(0);
                v___x_2265_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(v_levelParams_2263_, v___x_2264_);
                v___x_2266_ = l_Lean_mkConst(v_constName_2253_, v___x_2265_);
                if v_isShared_2262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2268_;
            }
            3 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(
    mut v_constName_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_constName_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
    crate::leanh::lean_dec(v___y_2282_);
    crate::leanh::lean_dec_ref(v___y_2281_);
    crate::leanh::lean_dec(v___y_2280_);
    return v_res_2284_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1;
    v___x_2291_ = l_Lean_MessageData_ofFormat(v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4;
    v___x_2296_ = l_Lean_MessageData_ofFormat(v___x_2295_);
    return v___x_2296_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6;
    v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l_Lean_Meta_DiscrTree_Key_format___closed__6;
    v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(
    mut v_parenIfNonAtomic_2302_: u8,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v_val_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut v_val_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v_a_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v_a_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v_a_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_a_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2307_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_2303_);
                if crate::leanh::lean_obj_tag(v___x_2307_) == 0 {
                    v_a_2308_ = crate::leanh::lean_ctor_get(v___x_2307_, 0);
                    v_isSharedCheck_2426_ = (!crate::leanh::lean_is_exclusive(v___x_2307_)) as u8;
                    if v_isSharedCheck_2426_ == 0 {
                        v___x_2310_ = v___x_2307_;
                        v_isShared_2311_ = v_isSharedCheck_2426_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2308_);
                        crate::leanh::lean_dec(v___x_2307_);
                        v___x_2310_ = crate::leanh::lean_box(0);
                        v_isShared_2311_ = v_isSharedCheck_2426_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2427_ = crate::leanh::lean_ctor_get(v___x_2307_, 0);
                    v_isSharedCheck_2434_ = (!crate::leanh::lean_is_exclusive(v___x_2307_)) as u8;
                    if v_isSharedCheck_2434_ == 0 {
                        v___x_2429_ = v___x_2307_;
                        v_isShared_2430_ = v_isSharedCheck_2434_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2427_);
                        crate::leanh::lean_dec(v___x_2307_);
                        v___x_2429_ = crate::leanh::lean_box(0);
                        v_isShared_2430_ = v_isSharedCheck_2434_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2308_) == 1 {
                    v_val_2312_ = crate::leanh::lean_ctor_get(v_a_2308_, 0);
                    crate::leanh::lean_inc(v_val_2312_);
                    crate::leanh::lean_dec_ref_known(v_a_2308_, 1);
                    match crate::leanh::lean_obj_tag(v_val_2312_) {
                        0 => {
                            v___x_2313_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once), _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2);
                            if v_isShared_2311_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2313_);
                                v___x_2315_ = v___x_2310_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2316_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
                                v___x_2315_ = v_reuseFailAlloc_2316_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v___x_2317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once), _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5);
                            if v_isShared_2311_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2317_);
                                v___x_2319_ = v___x_2310_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2320_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
                                v___x_2319_ = v_reuseFailAlloc_2320_;
                                state = 3;
                                continue;
                            }
                        }
                        2 => {
                            v_a_2321_ = crate::leanh::lean_ctor_get(v_val_2312_, 0);
                            crate::leanh::lean_inc_ref(v_a_2321_);
                            crate::leanh::lean_dec_ref_known(v_val_2312_, 1);
                            if crate::leanh::lean_obj_tag(v_a_2321_) == 0 {
                                v_val_2322_ = crate::leanh::lean_ctor_get(v_a_2321_, 0);
                                v_isSharedCheck_2334_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_2321_)) as u8;
                                if v_isSharedCheck_2334_ == 0 {
                                    v___x_2324_ = v_a_2321_;
                                    v_isShared_2325_ = v_isSharedCheck_2334_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2322_);
                                    crate::leanh::lean_dec(v_a_2321_);
                                    v___x_2324_ = crate::leanh::lean_box(0);
                                    v_isShared_2325_ = v_isSharedCheck_2334_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_val_2335_ = crate::leanh::lean_ctor_get(v_a_2321_, 0);
                                crate::leanh::lean_inc_ref(v_val_2335_);
                                crate::leanh::lean_dec_ref_known(v_a_2321_, 1);
                                v___x_2336_ = l_Lean_stringToMessageData(v_val_2335_);
                                if v_isShared_2311_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2336_);
                                    v___x_2338_ = v___x_2310_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2339_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2339_,
                                        0,
                                        v___x_2336_,
                                    );
                                    v___x_2338_ = v_reuseFailAlloc_2339_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        3 => {
                            crate::leanh::lean_del_object(v___x_2310_);
                            v_a_2340_ = crate::leanh::lean_ctor_get(v_val_2312_, 0);
                            crate::leanh::lean_inc(v_a_2340_);
                            v_a_2341_ = crate::leanh::lean_ctor_get(v_val_2312_, 1);
                            crate::leanh::lean_inc(v_a_2341_);
                            crate::leanh::lean_dec_ref_known(v_val_2312_, 2);
                            v___x_2342_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_2341_, v_a_2303_, v_a_2304_, v_a_2305_);
                            crate::leanh::lean_dec(v_a_2341_);
                            if crate::leanh::lean_obj_tag(v___x_2342_) == 0 {
                                v_a_2343_ = crate::leanh::lean_ctor_get(v___x_2342_, 0);
                                crate::leanh::lean_inc(v_a_2343_);
                                crate::leanh::lean_dec_ref_known(v___x_2342_, 1);
                                v___x_2344_ = l_Lean_mkFVar(v_a_2340_);
                                v___x_2345_ = l_Lean_MessageData_ofExpr(v___x_2344_);
                                v___x_2346_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_2345_, v_a_2343_, v_parenIfNonAtomic_2302_, v_a_2304_, v_a_2305_);
                                crate::leanh::lean_dec(v_a_2343_);
                                return v___x_2346_;
                            } else {
                                crate::leanh::lean_dec(v_a_2340_);
                                v_a_2347_ = crate::leanh::lean_ctor_get(v___x_2342_, 0);
                                v_isSharedCheck_2354_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2342_)) as u8;
                                if v_isSharedCheck_2354_ == 0 {
                                    v___x_2349_ = v___x_2342_;
                                    v_isShared_2350_ = v_isSharedCheck_2354_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2347_);
                                    crate::leanh::lean_dec(v___x_2342_);
                                    v___x_2349_ = crate::leanh::lean_box(0);
                                    v_isShared_2350_ = v_isSharedCheck_2354_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            crate::leanh::lean_del_object(v___x_2310_);
                            v_a_2355_ = crate::leanh::lean_ctor_get(v_val_2312_, 0);
                            crate::leanh::lean_inc(v_a_2355_);
                            v_a_2356_ = crate::leanh::lean_ctor_get(v_val_2312_, 1);
                            crate::leanh::lean_inc(v_a_2356_);
                            crate::leanh::lean_dec_ref_known(v_val_2312_, 2);
                            v___x_2357_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_a_2355_, v_a_2303_, v_a_2304_, v_a_2305_);
                            if crate::leanh::lean_obj_tag(v___x_2357_) == 0 {
                                v_a_2358_ = crate::leanh::lean_ctor_get(v___x_2357_, 0);
                                crate::leanh::lean_inc(v_a_2358_);
                                crate::leanh::lean_dec_ref_known(v___x_2357_, 1);
                                v___x_2359_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_2356_, v_a_2303_, v_a_2304_, v_a_2305_);
                                crate::leanh::lean_dec(v_a_2356_);
                                if crate::leanh::lean_obj_tag(v___x_2359_) == 0 {
                                    v_a_2360_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                                    crate::leanh::lean_inc(v_a_2360_);
                                    crate::leanh::lean_dec_ref_known(v___x_2359_, 1);
                                    v___x_2361_ = l_Lean_MessageData_ofExpr(v_a_2358_);
                                    v___x_2362_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_2361_, v_a_2360_, v_parenIfNonAtomic_2302_, v_a_2304_, v_a_2305_);
                                    crate::leanh::lean_dec(v_a_2360_);
                                    return v___x_2362_;
                                } else {
                                    crate::leanh::lean_dec(v_a_2358_);
                                    v_a_2363_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                                    v_isSharedCheck_2370_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2359_)) as u8;
                                    if v_isSharedCheck_2370_ == 0 {
                                        v___x_2365_ = v___x_2359_;
                                        v_isShared_2366_ = v_isSharedCheck_2370_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2363_);
                                        crate::leanh::lean_dec(v___x_2359_);
                                        v___x_2365_ = crate::leanh::lean_box(0);
                                        v_isShared_2366_ = v_isSharedCheck_2370_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2356_);
                                v_a_2371_ = crate::leanh::lean_ctor_get(v___x_2357_, 0);
                                v_isSharedCheck_2378_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2357_)) as u8;
                                if v_isSharedCheck_2378_ == 0 {
                                    v___x_2373_ = v___x_2357_;
                                    v_isShared_2374_ = v_isSharedCheck_2378_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2371_);
                                    crate::leanh::lean_dec(v___x_2357_);
                                    v___x_2373_ = crate::leanh::lean_box(0);
                                    v_isShared_2374_ = v_isSharedCheck_2378_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                        5 => {
                            crate::leanh::lean_del_object(v___x_2310_);
                            v___x_2379_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2380_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v___x_2379_, v_a_2303_, v_a_2304_, v_a_2305_);
                            if crate::leanh::lean_obj_tag(v___x_2380_) == 0 {
                                v_a_2381_ = crate::leanh::lean_ctor_get(v___x_2380_, 0);
                                crate::leanh::lean_inc(v_a_2381_);
                                crate::leanh::lean_dec_ref_known(v___x_2380_, 1);
                                v___x_2382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once), _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7);
                                v___x_2383_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_2382_, v_a_2381_, v_parenIfNonAtomic_2302_, v_a_2304_, v_a_2305_);
                                crate::leanh::lean_dec(v_a_2381_);
                                return v___x_2383_;
                            } else {
                                v_a_2384_ = crate::leanh::lean_ctor_get(v___x_2380_, 0);
                                v_isSharedCheck_2391_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2380_)) as u8;
                                if v_isSharedCheck_2391_ == 0 {
                                    v___x_2386_ = v___x_2380_;
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2384_);
                                    crate::leanh::lean_dec(v___x_2380_);
                                    v___x_2386_ = crate::leanh::lean_box(0);
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_del_object(v___x_2310_);
                            v_a_2392_ = crate::leanh::lean_ctor_get(v_val_2312_, 1);
                            crate::leanh::lean_inc(v_a_2392_);
                            v_a_2393_ = crate::leanh::lean_ctor_get(v_val_2312_, 2);
                            crate::leanh::lean_inc(v_a_2393_);
                            crate::leanh::lean_dec_ref_known(v_val_2312_, 3);
                            v___x_2394_ = 1;
                            v___x_2395_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_2394_, v_a_2303_, v_a_2304_, v_a_2305_);
                            if crate::leanh::lean_obj_tag(v___x_2395_) == 0 {
                                v_a_2396_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                                v_isSharedCheck_2421_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2395_)) as u8;
                                if v_isSharedCheck_2421_ == 0 {
                                    v___x_2398_ = v___x_2395_;
                                    v_isShared_2399_ = v_isSharedCheck_2421_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2396_);
                                    crate::leanh::lean_dec(v___x_2395_);
                                    v___x_2398_ = crate::leanh::lean_box(0);
                                    v_isShared_2399_ = v_isSharedCheck_2421_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2393_);
                                crate::leanh::lean_dec(v_a_2392_);
                                return v___x_2395_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2308_);
                    v___x_2422_ = l_Lean_MessageData_nil;
                    if v_isShared_2311_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2422_);
                        v___x_2424_ = v___x_2310_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
                        v___x_2424_ = v_reuseFailAlloc_2425_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2315_;
            }
            3 => {
                return v___x_2319_;
            }
            4 => {
                v___x_2326_ = l_Nat_reprFast(v_val_2322_);
                if v_isShared_2325_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2324_, 3);
                    crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2324_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2333_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2329_ = l_Lean_MessageData_ofFormat(v___x_2328_);
                if v_isShared_2311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2329_);
                    v___x_2331_ = v___x_2310_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2331_;
            }
            7 => {
                return v___x_2338_;
            }
            8 => {
                if v_isShared_2350_ == 0 {
                    v___x_2352_ = v___x_2349_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
                    v___x_2352_ = v_reuseFailAlloc_2353_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2352_;
            }
            10 => {
                if v_isShared_2366_ == 0 {
                    v___x_2368_ = v___x_2365_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
                    v___x_2368_ = v_reuseFailAlloc_2369_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2368_;
            }
            12 => {
                if v_isShared_2374_ == 0 {
                    v___x_2376_ = v___x_2373_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
                    v___x_2376_ = v_reuseFailAlloc_2377_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2376_;
            }
            14 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2389_;
            }
            16 => {
                v___x_2400_ =
                    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(
                        v_a_2393_, v_a_2303_, v_a_2304_, v_a_2305_,
                    );
                crate::leanh::lean_dec(v_a_2393_);
                if crate::leanh::lean_obj_tag(v___x_2400_) == 0 {
                    v_a_2401_ = crate::leanh::lean_ctor_get(v___x_2400_, 0);
                    crate::leanh::lean_inc(v_a_2401_);
                    crate::leanh::lean_dec_ref_known(v___x_2400_, 1);
                    v___x_2402_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once), _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8);
                    v___x_2403_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2403_, 0, v_a_2396_);
                    crate::leanh::lean_ctor_set(v___x_2403_, 1, v___x_2402_);
                    v___x_2404_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2405_ = lean_nat_add(v_a_2392_, v___x_2404_);
                    crate::leanh::lean_dec(v_a_2392_);
                    v___x_2406_ = l_Nat_reprFast(v___x_2405_);
                    if v_isShared_2399_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2398_, 3);
                        crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2406_);
                        v___x_2408_ = v___x_2398_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2406_);
                        v___x_2408_ = v_reuseFailAlloc_2412_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2398_);
                    crate::leanh::lean_dec(v_a_2396_);
                    crate::leanh::lean_dec(v_a_2392_);
                    v_a_2413_ = crate::leanh::lean_ctor_get(v___x_2400_, 0);
                    v_isSharedCheck_2420_ = (!crate::leanh::lean_is_exclusive(v___x_2400_)) as u8;
                    if v_isSharedCheck_2420_ == 0 {
                        v___x_2415_ = v___x_2400_;
                        v_isShared_2416_ = v_isSharedCheck_2420_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2413_);
                        crate::leanh::lean_dec(v___x_2400_);
                        v___x_2415_ = crate::leanh::lean_box(0);
                        v_isShared_2416_ = v_isSharedCheck_2420_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                v___x_2409_ = l_Lean_MessageData_ofFormat(v___x_2408_);
                v___x_2410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2410_, 0, v___x_2403_);
                crate::leanh::lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                v___x_2411_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_2410_, v_a_2401_, v_parenIfNonAtomic_2302_, v_a_2304_, v_a_2305_);
                crate::leanh::lean_dec(v_a_2401_);
                return v___x_2411_;
            }
            18 => {
                if v_isShared_2416_ == 0 {
                    v___x_2418_ = v___x_2415_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2418_;
            }
            20 => {
                return v___x_2424_;
            }
            21 => {
                if v_isShared_2430_ == 0 {
                    v___x_2432_ = v___x_2429_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(
    mut v_upperBound_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
    mut v_b_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2442_ = lean_nat_dec_lt(v_a_2436_, v_upperBound_2435_);
                if v___x_2442_ == 0 {
                    crate::leanh::lean_dec(v_a_2436_);
                    v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v_b_2437_);
                    return v___x_2443_;
                } else {
                    v___x_2444_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_2442_, v___y_2438_, v___y_2439_, v___y_2440_);
                    if crate::leanh::lean_obj_tag(v___x_2444_) == 0 {
                        v_a_2445_ = crate::leanh::lean_ctor_get(v___x_2444_, 0);
                        crate::leanh::lean_inc(v_a_2445_);
                        crate::leanh::lean_dec_ref_known(v___x_2444_, 1);
                        v___x_2446_ = lean_array_push(v_b_2437_, v_a_2445_);
                        v___x_2447_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2448_ = lean_nat_add(v_a_2436_, v___x_2447_);
                        crate::leanh::lean_dec(v_a_2436_);
                        v_a_2436_ = v___x_2448_;
                        v_b_2437_ = v___x_2446_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2437_);
                        crate::leanh::lean_dec(v_a_2436_);
                        v_a_2450_ = crate::leanh::lean_ctor_get(v___x_2444_, 0);
                        v_isSharedCheck_2457_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2444_)) as u8;
                        if v_isSharedCheck_2457_ == 0 {
                            v___x_2452_ = v___x_2444_;
                            v_isShared_2453_ = v_isSharedCheck_2457_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2450_);
                            crate::leanh::lean_dec(v___x_2444_);
                            v___x_2452_ = crate::leanh::lean_box(0);
                            v_isShared_2453_ = v_isSharedCheck_2457_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2453_ == 0 {
                    v___x_2455_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
                    v___x_2455_ = v_reuseFailAlloc_2456_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(
    mut v_num_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = crate::leanh::lean_unsigned_to_nat(0);
    v_r_2464_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0;
    v___x_2465_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_num_2458_, v___x_2463_, v_r_2464_, v_a_2459_, v_a_2460_, v_a_2461_);
    return v___x_2465_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(
    mut v_num_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(
        v_num_2466_,
        v_a_2467_,
        v_a_2468_,
        v_a_2469_,
    );
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec_ref(v_a_2468_);
    crate::leanh::lean_dec(v_a_2467_);
    crate::leanh::lean_dec(v_num_2466_);
    return v_res_2471_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(
    mut v_upperBound_2472_: *mut crate::leanh::LeanObject,
    mut v_a_2473_: *mut crate::leanh::LeanObject,
    mut v_b_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_2472_, v_a_2473_, v_b_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
    crate::leanh::lean_dec(v___y_2477_);
    crate::leanh::lean_dec_ref(v___y_2476_);
    crate::leanh::lean_dec(v___y_2475_);
    crate::leanh::lean_dec(v_upperBound_2472_);
    return v_res_2479_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(
    mut v_parenIfNonAtomic_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_parenIfNonAtomic_boxed_2485_: u8 = 0;
    let mut v_res_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_parenIfNonAtomic_boxed_2485_ = (crate::leanh::lean_unbox(v_parenIfNonAtomic_2480_) as u8);
    v_res_2486_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(
        v_parenIfNonAtomic_boxed_2485_,
        v_a_2481_,
        v_a_2482_,
        v_a_2483_,
    );
    crate::leanh::lean_dec(v_a_2483_);
    crate::leanh::lean_dec_ref(v_a_2482_);
    crate::leanh::lean_dec(v_a_2481_);
    return v_res_2486_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(
    mut v_upperBound_2487_: *mut crate::leanh::LeanObject,
    mut v_inst_2488_: *mut crate::leanh::LeanObject,
    mut v_R_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_b_2491_: *mut crate::leanh::LeanObject,
    mut v_c_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_2487_, v_a_2490_, v_b_2491_, v___y_2493_, v___y_2494_, v___y_2495_);
    return v___x_2497_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(
    mut v_upperBound_2498_: *mut crate::leanh::LeanObject,
    mut v_inst_2499_: *mut crate::leanh::LeanObject,
    mut v_R_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_b_2502_: *mut crate::leanh::LeanObject,
    mut v_c_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(v_upperBound_2498_, v_inst_2499_, v_R_2500_, v_a_2501_, v_b_2502_, v_c_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
    crate::leanh::lean_dec(v___y_2506_);
    crate::leanh::lean_dec_ref(v___y_2505_);
    crate::leanh::lean_dec(v___y_2504_);
    crate::leanh::lean_dec(v_upperBound_2498_);
    return v_res_2508_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2509_: *mut crate::leanh::LeanObject,
    mut v_constName_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2516_: *mut crate::leanh::LeanObject,
    mut v_constName_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2522_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(v_00_u03b1_2516_, v_constName_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
    crate::leanh::lean_dec(v___y_2520_);
    crate::leanh::lean_dec_ref(v___y_2519_);
    crate::leanh::lean_dec(v___y_2518_);
    return v_res_2522_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b1_2523_: *mut crate::leanh::LeanObject,
    mut v_ref_2524_: *mut crate::leanh::LeanObject,
    mut v_constName_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2524_, v_constName_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b1_2531_: *mut crate::leanh::LeanObject,
    mut v_ref_2532_: *mut crate::leanh::LeanObject,
    mut v_constName_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2538_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2531_, v_ref_2532_, v_constName_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec(v_ref_2532_);
    return v_res_2538_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2539_: *mut crate::leanh::LeanObject,
    mut v_ref_2540_: *mut crate::leanh::LeanObject,
    mut v_msg_2541_: *mut crate::leanh::LeanObject,
    mut v_declHint_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2540_, v_msg_2541_, v_declHint_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2548_: *mut crate::leanh::LeanObject,
    mut v_ref_2549_: *mut crate::leanh::LeanObject,
    mut v_msg_2550_: *mut crate::leanh::LeanObject,
    mut v_declHint_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2548_, v_ref_2549_, v_msg_2550_, v_declHint_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
    crate::leanh::lean_dec(v___y_2554_);
    crate::leanh::lean_dec_ref(v___y_2553_);
    crate::leanh::lean_dec(v___y_2552_);
    crate::leanh::lean_dec(v_ref_2549_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(
    mut v_msg_2557_: *mut crate::leanh::LeanObject,
    mut v_declHint_2558_: *mut crate::leanh::LeanObject,
    mut v___y_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2557_, v_declHint_2558_, v___y_2561_);
    return v___x_2563_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(
    mut v_msg_2564_: *mut crate::leanh::LeanObject,
    mut v_declHint_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
    mut v___y_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_2564_, v_declHint_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
    crate::leanh::lean_dec(v___y_2568_);
    crate::leanh::lean_dec_ref(v___y_2567_);
    crate::leanh::lean_dec(v___y_2566_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(
    mut v_00_u03b1_2571_: *mut crate::leanh::LeanObject,
    mut v_ref_2572_: *mut crate::leanh::LeanObject,
    mut v_msg_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_2572_, v_msg_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
    return v___x_2578_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_2579_: *mut crate::leanh::LeanObject,
    mut v_ref_2580_: *mut crate::leanh::LeanObject,
    mut v_msg_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_2579_, v_ref_2580_, v_msg_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
    crate::leanh::lean_dec(v___y_2584_);
    crate::leanh::lean_dec_ref(v___y_2583_);
    crate::leanh::lean_dec(v___y_2582_);
    crate::leanh::lean_dec(v_ref_2580_);
    return v_res_2586_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_2587_: *mut crate::leanh::LeanObject,
    mut v_msg_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2588_, v___y_2590_, v___y_2591_);
    return v___x_2593_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_2594_: *mut crate::leanh::LeanObject,
    mut v_msg_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2600_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2594_, v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
    crate::leanh::lean_dec(v___y_2598_);
    crate::leanh::lean_dec_ref(v___y_2597_);
    crate::leanh::lean_dec(v___y_2596_);
    return v_res_2600_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_keysAsPattern(
    mut v_keys_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2605_ = lean_array_to_list(v_keys_2601_);
                v___x_2606_ = lean_st_mk_ref(v___x_2605_);
                v___x_2607_ = 0;
                v___x_2608_ =
                    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(
                        v___x_2607_,
                        v___x_2606_,
                        v_a_2602_,
                        v_a_2603_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2608_) == 0 {
                    v_a_2609_ = crate::leanh::lean_ctor_get(v___x_2608_, 0);
                    v_isSharedCheck_2617_ = (!crate::leanh::lean_is_exclusive(v___x_2608_)) as u8;
                    if v_isSharedCheck_2617_ == 0 {
                        v___x_2611_ = v___x_2608_;
                        v_isShared_2612_ = v_isSharedCheck_2617_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2609_);
                        crate::leanh::lean_dec(v___x_2608_);
                        v___x_2611_ = crate::leanh::lean_box(0);
                        v_isShared_2612_ = v_isSharedCheck_2617_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2606_);
                    return v___x_2608_;
                }
            }
            1 => {
                v___x_2613_ = lean_st_ref_get(v___x_2606_);
                crate::leanh::lean_dec(v___x_2606_);
                crate::leanh::lean_dec(v___x_2613_);
                if v_isShared_2612_ == 0 {
                    v___x_2615_ = v___x_2611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2609_);
                    v___x_2615_ = v_reuseFailAlloc_2616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_keysAsPattern___boxed(
    mut v_keys_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2622_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_2618_, v_a_2619_, v_a_2620_);
    crate::leanh::lean_dec(v_a_2620_);
    crate::leanh::lean_dec_ref(v_a_2619_);
    return v_res_2622_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
    mut v_keys_2625_: *mut crate::leanh::LeanObject,
    mut v_v_2626_: *mut crate::leanh::LeanObject,
    mut v_i_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    v___x_2628_ = lean_array_get_size(v_keys_2625_);
    v___x_2629_ = lean_nat_dec_lt(v_i_2627_, v___x_2628_);
    if v___x_2629_ == 0 {
        let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2630_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
        v___x_2632_ = lean_array_push(v___x_2631_, v_v_2626_);
        v___x_2633_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0;
        v___x_2634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2632_);
        crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
        return v___x_2634_;
    } else {
        let mut v_k_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_2635_ = lean_array_fget_borrowed(v_keys_2625_, v_i_2627_);
        v___x_2636_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2637_ = lean_nat_add(v_i_2627_, v___x_2636_);
        v_c_2638_ =
            l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
                v_keys_2625_,
                v_v_2626_,
                v___x_2637_,
            );
        crate::leanh::lean_dec(v___x_2637_);
        v___x_2639_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0;
        crate::leanh::lean_inc(v_k_2635_);
        v___x_2640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2640_, 0, v_k_2635_);
        crate::leanh::lean_ctor_set(v___x_2640_, 1, v_c_2638_);
        v___x_2641_ = lean_mk_empty_array_with_capacity(v___x_2636_);
        v___x_2642_ = lean_array_push(v___x_2641_, v___x_2640_);
        v___x_2643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2639_);
        crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2642_);
        return v___x_2643_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___boxed(
    mut v_keys_2644_: *mut crate::leanh::LeanObject,
    mut v_v_2645_: *mut crate::leanh::LeanObject,
    mut v_i_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
        v_keys_2644_,
        v_v_2645_,
        v_i_2646_,
    );
    crate::leanh::lean_dec(v_i_2646_);
    crate::leanh::lean_dec_ref(v_keys_2644_);
    return v_res_2647_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
    mut v_00_u03b1_2648_: *mut crate::leanh::LeanObject,
    mut v_keys_2649_: *mut crate::leanh::LeanObject,
    mut v_v_2650_: *mut crate::leanh::LeanObject,
    mut v_i_2651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
        v_keys_2649_,
        v_v_2650_,
        v_i_2651_,
    );
    return v___x_2652_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___boxed(
    mut v_00_u03b1_2653_: *mut crate::leanh::LeanObject,
    mut v_keys_2654_: *mut crate::leanh::LeanObject,
    mut v_v_2655_: *mut crate::leanh::LeanObject,
    mut v_i_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        v_00_u03b1_2653_,
        v_keys_2654_,
        v_v_2655_,
        v_i_2656_,
    );
    crate::leanh::lean_dec(v_i_2656_);
    crate::leanh::lean_dec_ref(v_keys_2654_);
    return v_res_2657_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(
    mut v_inst_2658_: *mut crate::leanh::LeanObject,
    mut v_vs_2659_: *mut crate::leanh::LeanObject,
    mut v_v_2660_: *mut crate::leanh::LeanObject,
    mut v_i_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: u8 = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2662_ = lean_array_get_size(v_vs_2659_);
                v___x_2663_ = lean_nat_dec_lt(v_i_2661_, v___x_2662_);
                if v___x_2663_ == 0 {
                    crate::leanh::lean_dec(v_i_2661_);
                    crate::leanh::lean_dec_ref(v_inst_2658_);
                    v___x_2664_ = lean_array_push(v_vs_2659_, v_v_2660_);
                    return v___x_2664_;
                } else {
                    v___x_2665_ = lean_array_fget_borrowed(v_vs_2659_, v_i_2661_);
                    crate::leanh::lean_inc_ref(v_inst_2658_);
                    crate::leanh::lean_inc(v___x_2665_);
                    crate::leanh::lean_inc(v_v_2660_);
                    v___x_2666_ = crate::leanh::lean_apply_2(v_inst_2658_, v_v_2660_, v___x_2665_);
                    v___x_2667_ = (crate::leanh::lean_unbox(v___x_2666_) as u8);
                    if v___x_2667_ == 0 {
                        v___x_2668_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2669_ = lean_nat_add(v_i_2661_, v___x_2668_);
                        crate::leanh::lean_dec(v_i_2661_);
                        v_i_2661_ = v___x_2669_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2658_);
                        v___x_2671_ = lean_array_fset(v_vs_2659_, v_i_2661_, v_v_2660_);
                        crate::leanh::lean_dec(v_i_2661_);
                        return v___x_2671_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(
    mut v_00_u03b1_2672_: *mut crate::leanh::LeanObject,
    mut v_inst_2673_: *mut crate::leanh::LeanObject,
    mut v_vs_2674_: *mut crate::leanh::LeanObject,
    mut v_v_2675_: *mut crate::leanh::LeanObject,
    mut v_i_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(
            v_inst_2673_,
            v_vs_2674_,
            v_v_2675_,
            v_i_2676_,
        );
    return v___x_2677_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(
    mut v_inst_2678_: *mut crate::leanh::LeanObject,
    mut v_vs_2679_: *mut crate::leanh::LeanObject,
    mut v_v_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2682_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(
            v_inst_2678_,
            v_vs_2679_,
            v_v_2680_,
            v___x_2681_,
        );
    return v___x_2682_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(
    mut v_00_u03b1_2683_: *mut crate::leanh::LeanObject,
    mut v_inst_2684_: *mut crate::leanh::LeanObject,
    mut v_vs_2685_: *mut crate::leanh::LeanObject,
    mut v_v_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(
        v_inst_2684_,
        v_vs_2685_,
        v_v_2686_,
    );
    return v___x_2687_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_b_2689_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: u8 = 0;
    v_fst_2690_ = crate::leanh::lean_ctor_get(v_a_2688_, 0);
    v_fst_2691_ = crate::leanh::lean_ctor_get(v_b_2689_, 0);
    v___x_2692_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2690_, v_fst_2691_);
    return v___x_2692_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(
    mut v_a_2693_: *mut crate::leanh::LeanObject,
    mut v_b_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2695_: u8 = 0;
    let mut v_r_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(
            v_a_2693_, v_b_2694_,
        );
    crate::leanh::lean_dec_ref(v_b_2694_);
    crate::leanh::lean_dec_ref(v_a_2693_);
    v_r_2696_ = crate::leanh::lean_box((v_res_2695_) as usize);
    return v_r_2696_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(
    mut v_x_2697_: *mut crate::leanh::LeanObject,
    mut v_keys_2698_: *mut crate::leanh::LeanObject,
    mut v_v_2699_: *mut crate::leanh::LeanObject,
    mut v_k_2700_: *mut crate::leanh::LeanObject,
    mut v_x_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2703_ = lean_nat_add(v_x_2697_, v___x_2702_);
    v_c_2704_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
        v_keys_2698_,
        v_v_2699_,
        v___x_2703_,
    );
    crate::leanh::lean_dec(v___x_2703_);
    v___x_2705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2705_, 0, v_k_2700_);
    crate::leanh::lean_ctor_set(v___x_2705_, 1, v_c_2704_);
    return v___x_2705_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(
    mut v_x_2706_: *mut crate::leanh::LeanObject,
    mut v_keys_2707_: *mut crate::leanh::LeanObject,
    mut v_v_2708_: *mut crate::leanh::LeanObject,
    mut v_k_2709_: *mut crate::leanh::LeanObject,
    mut v_x_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2711_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(
            v_x_2706_,
            v_keys_2707_,
            v_v_2708_,
            v_k_2709_,
            v_x_2710_,
        );
    crate::leanh::lean_dec_ref(v_keys_2707_);
    crate::leanh::lean_dec(v_x_2706_);
    return v_res_2711_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(
    mut v_x_2713_: *mut crate::leanh::LeanObject,
    mut v_inst_2714_: *mut crate::leanh::LeanObject,
    mut v_keys_2715_: *mut crate::leanh::LeanObject,
    mut v_v_2716_: *mut crate::leanh::LeanObject,
    mut v_k_2717_: *mut crate::leanh::LeanObject,
    mut v_x_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ =
        l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(
            v_x_2713_,
            v_inst_2714_,
            v_keys_2715_,
            v_v_2716_,
            v_k_2717_,
            v_x_2718_,
        );
    crate::leanh::lean_dec(v_x_2713_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(
    mut v_inst_2739_: *mut crate::leanh::LeanObject,
    mut v_keys_2740_: *mut crate::leanh::LeanObject,
    mut v_v_2741_: *mut crate::leanh::LeanObject,
    mut v_x_2742_: *mut crate::leanh::LeanObject,
    mut v_x_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vs_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2748_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_2744_ = crate::leanh::lean_ctor_get(v_x_2743_, 0);
                v_children_2745_ = crate::leanh::lean_ctor_get(v_x_2743_, 1);
                v_isSharedCheck_2766_ = (!crate::leanh::lean_is_exclusive(v_x_2743_)) as u8;
                if v_isSharedCheck_2766_ == 0 {
                    v___x_2747_ = v_x_2743_;
                    v_isShared_2748_ = v_isSharedCheck_2766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_2745_);
                    crate::leanh::lean_inc(v_vs_2744_);
                    crate::leanh::lean_dec(v_x_2743_);
                    v___x_2747_ = crate::leanh::lean_box(0);
                    v_isShared_2748_ = v_isSharedCheck_2766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2749_ = lean_array_get_size(v_keys_2740_);
                v___x_2750_ = lean_nat_dec_lt(v_x_2742_, v___x_2749_);
                if v___x_2750_ == 0 {
                    crate::leanh::lean_dec(v_x_2742_);
                    crate::leanh::lean_dec_ref(v_keys_2740_);
                    v___x_2751_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_2739_, v_vs_2744_, v_v_2741_);
                    if v_isShared_2748_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2747_, 0, v___x_2751_);
                        v___x_2753_ = v___x_2747_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_children_2745_);
                        v___x_2753_ = v_reuseFailAlloc_2754_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___f_2755_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0;
                    v_k_2756_ = lean_array_fget(v_keys_2740_, v_x_2742_);
                    crate::leanh::lean_inc_n(v_k_2756_, 2);
                    crate::leanh::lean_inc(v_v_2741_);
                    crate::leanh::lean_inc_ref(v_keys_2740_);
                    crate::leanh::lean_inc(v_x_2742_);
                    v___f_2757_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
                    crate::leanh::lean_closure_set(v___f_2757_, 0, v_x_2742_);
                    crate::leanh::lean_closure_set(v___f_2757_, 1, v_inst_2739_);
                    crate::leanh::lean_closure_set(v___f_2757_, 2, v_keys_2740_);
                    crate::leanh::lean_closure_set(v___f_2757_, 3, v_v_2741_);
                    crate::leanh::lean_closure_set(v___f_2757_, 4, v_k_2756_);
                    v___f_2758_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed as *mut core::ffi::c_void, 5, 4);
                    crate::leanh::lean_closure_set(v___f_2758_, 0, v_x_2742_);
                    crate::leanh::lean_closure_set(v___f_2758_, 1, v_keys_2740_);
                    crate::leanh::lean_closure_set(v___f_2758_, 2, v_v_2741_);
                    crate::leanh::lean_closure_set(v___f_2758_, 3, v_k_2756_);
                    v___x_2759_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10;
                    v___x_2760_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1;
                    v___x_2761_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2761_, 0, v_k_2756_);
                    crate::leanh::lean_ctor_set(v___x_2761_, 1, v___x_2760_);
                    v_c_2762_ = l_Array_binInsertM___redArg(
                        v___x_2759_,
                        v___f_2755_,
                        v___f_2757_,
                        v___f_2758_,
                        v_children_2745_,
                        v___x_2761_,
                    );
                    if v_isShared_2748_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2747_, 1, v_c_2762_);
                        v___x_2764_ = v___x_2747_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_vs_2744_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_c_2762_);
                        v___x_2764_ = v_reuseFailAlloc_2765_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2753_;
            }
            3 => {
                return v___x_2764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(
    mut v_x_2767_: *mut crate::leanh::LeanObject,
    mut v_inst_2768_: *mut crate::leanh::LeanObject,
    mut v_keys_2769_: *mut crate::leanh::LeanObject,
    mut v_v_2770_: *mut crate::leanh::LeanObject,
    mut v_k_2771_: *mut crate::leanh::LeanObject,
    mut v_x_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_unused_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2773_ = crate::leanh::lean_ctor_get(v_x_2772_, 1);
                v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v_x_2772_)) as u8;
                if v_isSharedCheck_2783_ == 0 {
                    v_unused_2784_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
                    crate::leanh::lean_dec(v_unused_2784_);
                    v___x_2775_ = v_x_2772_;
                    v_isShared_2776_ = v_isSharedCheck_2783_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2773_);
                    crate::leanh::lean_dec(v_x_2772_);
                    v___x_2775_ = crate::leanh::lean_box(0);
                    v_isShared_2776_ = v_isSharedCheck_2783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2777_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2778_ = lean_nat_add(v_x_2767_, v___x_2777_);
                v_c_2779_ =
                    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(
                        v_inst_2768_,
                        v_keys_2769_,
                        v_v_2770_,
                        v___x_2778_,
                        v_snd_2773_,
                    );
                if v_isShared_2776_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2775_, 1, v_c_2779_);
                    crate::leanh::lean_ctor_set(v___x_2775_, 0, v_k_2771_);
                    v___x_2781_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_k_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_c_2779_);
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(
    mut v_00_u03b1_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
    mut v_keys_2787_: *mut crate::leanh::LeanObject,
    mut v_v_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
    mut v_x_2790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(
        v_inst_2786_,
        v_keys_2787_,
        v_v_2788_,
        v_x_2789_,
        v_x_2790_,
    );
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_Meta_DiscrTree_instInhabited(crate::leanh::lean_box(0));
    return v___x_2794_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5;
    v___x_2799_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_2800_ = crate::leanh::lean_unsigned_to_nat(166);
    v___x_2801_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4;
    v___x_2802_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3;
    v___x_2803_ = l_mkPanicMessageWithDecl(
        v___x_2802_,
        v___x_2801_,
        v___x_2800_,
        v___x_2799_,
        v___x_2798_,
    );
    return v___x_2803_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
    mut v_inst_2804_: *mut crate::leanh::LeanObject,
    mut v_d_2805_: *mut crate::leanh::LeanObject,
    mut v_keys_2806_: *mut crate::leanh::LeanObject,
    mut v_v_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: u8 = 0;
    v___x_2808_ = lean_array_get_size(v_keys_2806_);
    v___x_2809_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2810_ = lean_nat_dec_eq(v___x_2808_, v___x_2809_);
    if v___x_2810_ == 0 {
        let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2811_ = crate::leanh::lean_box(0);
        v_k_2812_ = lean_array_get(v___x_2811_, v_keys_2806_, v___x_2809_);
        v___x_2813_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0;
        v___x_2814_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1;
        crate::leanh::lean_inc(v_k_2812_);
        v___x_2815_ = l_Lean_PersistentHashMap_find_x3f___redArg(
            v___x_2813_,
            v___x_2814_,
            v_d_2805_,
            v_k_2812_,
        );
        if crate::leanh::lean_obj_tag(v___x_2815_) == 0 {
            let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_2804_);
            v___x_2816_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_2817_ =
                l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(
                    v_keys_2806_,
                    v_v_2807_,
                    v___x_2816_,
                );
            crate::leanh::lean_dec_ref(v_keys_2806_);
            v___x_2818_ = l_Lean_PersistentHashMap_insert___redArg(
                v___x_2813_,
                v___x_2814_,
                v_d_2805_,
                v_k_2812_,
                v_c_2817_,
            );
            return v___x_2818_;
        } else {
            let mut v_val_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2819_ = crate::leanh::lean_ctor_get(v___x_2815_, 0);
            crate::leanh::lean_inc(v_val_2819_);
            crate::leanh::lean_dec_ref_known(v___x_2815_, 1);
            v___x_2820_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_2821_ =
                l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(
                    v_inst_2804_,
                    v_keys_2806_,
                    v_v_2807_,
                    v___x_2820_,
                    v_val_2819_,
                );
            v___x_2822_ = l_Lean_PersistentHashMap_insert___redArg(
                v___x_2813_,
                v___x_2814_,
                v_d_2805_,
                v_k_2812_,
                v_c_2821_,
            );
            return v___x_2822_;
        }
    } else {
        let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_v_2807_);
        crate::leanh::lean_dec_ref(v_keys_2806_);
        crate::leanh::lean_dec_ref(v_d_2805_);
        crate::leanh::lean_dec_ref(v_inst_2804_);
        v___x_2823_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_once),
            _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2,
        );
        v___x_2824_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6),
            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6_once),
            _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6,
        );
        v___x_2825_ = l_panic___redArg(v___x_2823_, v___x_2824_);
        return v___x_2825_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue(
    mut v_00_u03b1_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_d_2828_: *mut crate::leanh::LeanObject,
    mut v_keys_2829_: *mut crate::leanh::LeanObject,
    mut v_v_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
        v_inst_2827_,
        v_d_2828_,
        v_keys_2829_,
        v_v_2830_,
    );
    return v___x_2831_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertCore___redArg(
    mut v_inst_2832_: *mut crate::leanh::LeanObject,
    mut v_d_2833_: *mut crate::leanh::LeanObject,
    mut v_keys_2834_: *mut crate::leanh::LeanObject,
    mut v_v_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2836_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
        v_inst_2832_,
        v_d_2833_,
        v_keys_2834_,
        v_v_2835_,
    );
    return v___x_2836_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertCore(
    mut v_00_u03b1_2837_: *mut crate::leanh::LeanObject,
    mut v_inst_2838_: *mut crate::leanh::LeanObject,
    mut v_d_2839_: *mut crate::leanh::LeanObject,
    mut v_keys_2840_: *mut crate::leanh::LeanObject,
    mut v_v_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2842_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
        v_inst_2838_,
        v_d_2839_,
        v_keys_2840_,
        v_v_2841_,
    );
    return v___x_2842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_DiscrTree_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DiscrTree_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_DiscrTree_instToExprKey = _init_l_Lean_Meta_DiscrTree_instToExprKey();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_DiscrTree_instToExprKey);
    l_Lean_Meta_DiscrTree_instLTKey = _init_l_Lean_Meta_DiscrTree_instLTKey();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_DiscrTree_instLTKey);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_DiscrTree_Basic(
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
pub unsafe fn initialize_Lean_Meta_DiscrTree_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DiscrTree_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_DiscrTree_Basic(builtin);
}
