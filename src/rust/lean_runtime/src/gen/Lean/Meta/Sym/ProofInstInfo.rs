// Lean compiler output
// Module: Lean.Meta.Sym.ProofInstInfo
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.IsClass Lean.Meta.Sym.Util Lean.Meta.Sym.Eta
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Eta::{
    initialize_Lean_Meta_Sym_Eta, l_Lean_Meta_Sym_etaReduceAll,
    runtime_initialize_Lean_Meta_Sym_Eta,
};
use crate::r#gen::Lean::Meta::Sym::IsClass::{
    initialize_Lean_Meta_Sym_IsClass, l_Lean_Meta_Sym_isClass_x3f,
    runtime_initialize_Lean_Meta_Sym_IsClass,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducible,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Transform::{l_Lean_Core_betaReduce, l_Lean_Meta_zetaReduce};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_preprocessType(
    mut v_type_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v_a_1106_: *mut LeanObject,
    mut v_a_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ =
        l_Lean_Meta_Sym_unfoldReducible(v_type_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
    if lean_obj_tag(v___x_1110_) == 0 {
        let mut v_a_1111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
        v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
        lean_inc(v_a_1111_);
        lean_dec_ref_known(v___x_1110_, 1);
        v___x_1112_ = l_Lean_Core_betaReduce(v_a_1111_, v_a_1107_, v_a_1108_);
        if lean_obj_tag(v___x_1112_) == 0 {
            let mut v_a_1113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: u8 = 0;
            let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
            v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
            lean_inc(v_a_1113_);
            lean_dec_ref_known(v___x_1112_, 1);
            v___x_1114_ = 1;
            v___x_1115_ = l_Lean_Meta_zetaReduce(
                v_a_1113_,
                v___x_1114_,
                v___x_1114_,
                v___x_1114_,
                v_a_1105_,
                v_a_1106_,
                v_a_1107_,
                v_a_1108_,
            );
            if lean_obj_tag(v___x_1115_) == 0 {
                let mut v_a_1116_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
                v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
                lean_inc(v_a_1116_);
                lean_dec_ref_known(v___x_1115_, 1);
                v___x_1117_ = l_Lean_Meta_Sym_etaReduceAll(v_a_1116_, v_a_1107_, v_a_1108_);
                return v___x_1117_;
            } else {
                return v___x_1115_;
            }
        } else {
            return v___x_1112_;
        }
    } else {
        return v___x_1110_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_preprocessType___boxed(
    mut v_type_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1124_: *mut LeanObject = core::ptr::null_mut();
    v_res_1124_ =
        l_Lean_Meta_Sym_preprocessType(v_type_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
    lean_dec(v_a_1122_);
    lean_dec_ref(v_a_1121_);
    lean_dec(v_a_1120_);
    lean_dec_ref(v_a_1119_);
    return v_res_1124_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(
    mut v___x_1125_: *mut LeanObject,
    mut v_as_1126_: *mut LeanObject,
    mut v_sz_1127_: usize,
    mut v_i_1128_: usize,
    mut v_b_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___y_1146_: u8 = 0;
    let mut v___y_1147_: u8 = 0;
    let mut v_found_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: usize = 0;
    let mut v___x_1155_: usize = 0;
    let mut v_reuseFailAlloc_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1159_: u8 = 0;
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: u8 = 0;
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: u8 = 0;
    let mut v_a_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v_a_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: u8 = 0;
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_a_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1135_ = lean_usize_dec_lt(v_i_1128_, v_sz_1127_);
                if v___x_1135_ == 0 {
                    lean_dec_ref(v___x_1125_);
                    v___x_1136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1136_, 0, v_b_1129_);
                    return v___x_1136_;
                } else {
                    v_a_1137_ = lean_array_uget_borrowed(v_as_1126_, v_i_1128_);
                    lean_inc(v___y_1133_);
                    lean_inc_ref(v___y_1132_);
                    lean_inc(v___y_1131_);
                    lean_inc_ref(v___y_1130_);
                    lean_inc(v_a_1137_);
                    v___x_1138_ = lean_infer_type(
                        v_a_1137_,
                        v___y_1130_,
                        v___y_1131_,
                        v___y_1132_,
                        v___y_1133_,
                    );
                    if lean_obj_tag(v___x_1138_) == 0 {
                        v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
                        lean_inc(v_a_1139_);
                        lean_dec_ref_known(v___x_1138_, 1);
                        v_fst_1140_ = lean_ctor_get(v_b_1129_, 0);
                        v_snd_1141_ = lean_ctor_get(v_b_1129_, 1);
                        v_isSharedCheck_1178_ = (!lean_is_exclusive(v_b_1129_)) as u8;
                        if v_isSharedCheck_1178_ == 0 {
                            v___x_1143_ = v_b_1129_;
                            v_isShared_1144_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1141_);
                            lean_inc(v_fst_1140_);
                            lean_dec(v_b_1129_);
                            v___x_1143_ = lean_box(0);
                            v_isShared_1144_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_1129_);
                        lean_dec_ref(v___x_1125_);
                        v_a_1179_ = lean_ctor_get(v___x_1138_, 0);
                        v_isSharedCheck_1186_ = (!lean_is_exclusive(v___x_1138_)) as u8;
                        if v_isSharedCheck_1186_ == 0 {
                            v___x_1181_ = v___x_1138_;
                            v_isShared_1182_ = v_isSharedCheck_1186_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1179_);
                            lean_dec(v___x_1138_);
                            v___x_1181_ = lean_box(0);
                            v_isShared_1182_ = v_isSharedCheck_1186_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1139_);
                lean_inc_ref(v___x_1125_);
                v___x_1176_ = l_Lean_Meta_Sym_isClass_x3f(v___x_1125_, v_a_1139_);
                if lean_obj_tag(v___x_1176_) == 0 {
                    v___x_1177_ = 0;
                    v___y_1159_ = v___x_1177_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_1176_, 1);
                    v___y_1159_ = v___x_1135_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1149_ = lean_alloc_ctor(0, 0, (2) as u32);
                lean_ctor_set_uint8(v___x_1149_, 0 as u32, v___y_1146_);
                lean_ctor_set_uint8(v___x_1149_, 1 as u32, v___y_1147_);
                v___x_1150_ = lean_array_push(v_fst_1140_, v___x_1149_);
                v___x_1151_ = lean_box((v_found_1148_) as usize);
                if v_isShared_1144_ == 0 {
                    lean_ctor_set(v___x_1143_, 1, v___x_1151_);
                    lean_ctor_set(v___x_1143_, 0, v___x_1150_);
                    v___x_1153_ = v___x_1143_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1150_);
                    lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1151_);
                    v___x_1153_ = v_reuseFailAlloc_1157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1154_ = 1usize;
                v___x_1155_ = lean_usize_add(v_i_1128_, v___x_1154_);
                v_i_1128_ = v___x_1155_;
                v_b_1129_ = v___x_1153_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1160_ = l_Lean_Meta_isProp(
                    v_a_1139_,
                    v___y_1130_,
                    v___y_1131_,
                    v___y_1132_,
                    v___y_1133_,
                );
                if lean_obj_tag(v___x_1160_) == 0 {
                    if v___y_1159_ == 0 {
                        v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
                        lean_inc(v_a_1161_);
                        lean_dec_ref_known(v___x_1160_, 1);
                        v___x_1162_ = (lean_unbox(v_a_1161_) as u8);
                        if v___x_1162_ == 0 {
                            v___x_1163_ = (lean_unbox(v_a_1161_) as u8);
                            lean_dec(v_a_1161_);
                            v___x_1164_ = (lean_unbox(v_snd_1141_) as u8);
                            lean_dec(v_snd_1141_);
                            v___y_1146_ = v___x_1163_;
                            v___y_1147_ = v___y_1159_;
                            v_found_1148_ = v___x_1164_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_snd_1141_);
                            v___x_1165_ = (lean_unbox(v_a_1161_) as u8);
                            lean_dec(v_a_1161_);
                            v___y_1146_ = v___x_1165_;
                            v___y_1147_ = v___y_1159_;
                            v_found_1148_ = v___x_1135_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1141_);
                        v_a_1166_ = lean_ctor_get(v___x_1160_, 0);
                        lean_inc(v_a_1166_);
                        lean_dec_ref_known(v___x_1160_, 1);
                        v___x_1167_ = (lean_unbox(v_a_1166_) as u8);
                        lean_dec(v_a_1166_);
                        v___y_1146_ = v___x_1167_;
                        v___y_1147_ = v___y_1159_;
                        v_found_1148_ = v___x_1135_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1143_);
                    lean_dec(v_snd_1141_);
                    lean_dec(v_fst_1140_);
                    lean_dec_ref(v___x_1125_);
                    v_a_1168_ = lean_ctor_get(v___x_1160_, 0);
                    v_isSharedCheck_1175_ = (!lean_is_exclusive(v___x_1160_)) as u8;
                    if v_isSharedCheck_1175_ == 0 {
                        v___x_1170_ = v___x_1160_;
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1168_);
                        lean_dec(v___x_1160_);
                        v___x_1170_ = lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1171_ == 0 {
                    v___x_1173_ = v___x_1170_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
                    v___x_1173_ = v_reuseFailAlloc_1174_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1173_;
            }
            7 => {
                if v_isShared_1182_ == 0 {
                    v___x_1184_ = v___x_1181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0___boxed(
    mut v___x_1187_: *mut LeanObject,
    mut v_as_1188_: *mut LeanObject,
    mut v_sz_1189_: *mut LeanObject,
    mut v_i_1190_: *mut LeanObject,
    mut v_b_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
    mut v___y_1196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1197_: usize = 0;
    let mut v_i_boxed_1198_: usize = 0;
    let mut v_res_1199_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1189_);
    lean_dec(v_sz_1189_);
    v_i_boxed_1198_ = lean_unbox_usize(v_i_1190_);
    lean_dec(v_i_1190_);
    v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(v___x_1187_, v_as_1188_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
    lean_dec(v___y_1195_);
    lean_dec_ref(v___y_1194_);
    lean_dec(v___y_1193_);
    lean_dec_ref(v___y_1192_);
    lean_dec_ref(v_as_1188_);
    return v_res_1199_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
    mut v_xs_1206_: *mut LeanObject,
    mut v_a_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1215_: usize = 0;
    let mut v___x_1216_: usize = 0;
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v_snd_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u8 = 0;
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut v_a_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1212_ = lean_st_ref_get(v_a_1210_);
                v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
                lean_inc_ref(v_env_1213_);
                lean_dec(v___x_1212_);
                v___x_1214_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1;
                v_sz_1215_ = lean_array_size(v_xs_1206_);
                v___x_1216_ = 0usize;
                v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(v_env_1213_, v_xs_1206_, v_sz_1215_, v___x_1216_, v___x_1214_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
                if lean_obj_tag(v___x_1217_) == 0 {
                    v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1233_ = (!lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1220_ = v___x_1217_;
                        v_isShared_1221_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1218_);
                        lean_dec(v___x_1217_);
                        v___x_1220_ = lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1234_ = lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1241_ = (!lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1236_ = v___x_1217_;
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1234_);
                        lean_dec(v___x_1217_);
                        v___x_1236_ = lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1222_ = lean_ctor_get(v_a_1218_, 1);
                v___x_1223_ = (lean_unbox(v_snd_1222_) as u8);
                if v___x_1223_ == 0 {
                    lean_dec(v_a_1218_);
                    v___x_1224_ = lean_box(0);
                    if v_isShared_1221_ == 0 {
                        lean_ctor_set(v___x_1220_, 0, v___x_1224_);
                        v___x_1226_ = v___x_1220_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
                        v___x_1226_ = v_reuseFailAlloc_1227_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_fst_1228_ = lean_ctor_get(v_a_1218_, 0);
                    lean_inc(v_fst_1228_);
                    lean_dec(v_a_1218_);
                    v___x_1229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1229_, 0, v_fst_1228_);
                    if v_isShared_1221_ == 0 {
                        lean_ctor_set(v___x_1220_, 0, v___x_1229_);
                        v___x_1231_ = v___x_1220_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
                        v___x_1231_ = v_reuseFailAlloc_1232_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1226_;
            }
            3 => {
                return v___x_1231_;
            }
            4 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___boxed(
    mut v_xs_1242_: *mut LeanObject,
    mut v_a_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
    mut v_a_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
        v_xs_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_,
    );
    lean_dec(v_a_1246_);
    lean_dec_ref(v_a_1245_);
    lean_dec(v_a_1244_);
    lean_dec_ref(v_a_1243_);
    lean_dec_ref(v_xs_1242_);
    return v_res_1248_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0(
    mut v_k_1249_: *mut LeanObject,
    mut v_b_1250_: *mut LeanObject,
    mut v_c_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1255_);
    lean_inc_ref(v___y_1254_);
    lean_inc(v___y_1253_);
    lean_inc_ref(v___y_1252_);
    v___x_1257_ = lean_apply_7(
        v_k_1249_,
        v_b_1250_,
        v_c_1251_,
        v___y_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        lean_box(0),
    );
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_1258_: *mut LeanObject,
    mut v_b_1259_: *mut LeanObject,
    mut v_c_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1266_: *mut LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0(v_k_1258_, v_b_1259_, v_c_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
    lean_dec(v___y_1264_);
    lean_dec_ref(v___y_1263_);
    lean_dec(v___y_1262_);
    lean_dec_ref(v___y_1261_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(
    mut v_type_1267_: *mut LeanObject,
    mut v_k_1268_: *mut LeanObject,
    mut v_cleanupAnnotations_1269_: u8,
    mut v_whnfType_1270_: u8,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_a_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1276_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1276_, 0, v_k_1268_);
                v___x_1277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_1267_,
                    v___f_1276_,
                    v_cleanupAnnotations_1269_,
                    v_whnfType_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                );
                if lean_obj_tag(v___x_1277_) == 0 {
                    v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
                    v_isSharedCheck_1285_ = (!lean_is_exclusive(v___x_1277_)) as u8;
                    if v_isSharedCheck_1285_ == 0 {
                        v___x_1280_ = v___x_1277_;
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1278_);
                        lean_dec(v___x_1277_);
                        v___x_1280_ = lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
                    v_isSharedCheck_1293_ = (!lean_is_exclusive(v___x_1277_)) as u8;
                    if v_isSharedCheck_1293_ == 0 {
                        v___x_1288_ = v___x_1277_;
                        v_isShared_1289_ = v_isSharedCheck_1293_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1286_);
                        lean_dec(v___x_1277_);
                        v___x_1288_ = lean_box(0);
                        v_isShared_1289_ = v_isSharedCheck_1293_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1281_ == 0 {
                    v___x_1283_ = v___x_1280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
                    v___x_1283_ = v_reuseFailAlloc_1284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1283_;
            }
            3 => {
                if v_isShared_1289_ == 0 {
                    v___x_1291_ = v___x_1288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
                    v___x_1291_ = v_reuseFailAlloc_1292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___boxed(
    mut v_type_1294_: *mut LeanObject,
    mut v_k_1295_: *mut LeanObject,
    mut v_cleanupAnnotations_1296_: *mut LeanObject,
    mut v_whnfType_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1303_: u8 = 0;
    let mut v_whnfType_boxed_1304_: u8 = 0;
    let mut v_res_1305_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1303_ = (lean_unbox(v_cleanupAnnotations_1296_) as u8);
    v_whnfType_boxed_1304_ = (lean_unbox(v_whnfType_1297_) as u8);
    v_res_1305_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_type_1294_, v_k_1295_, v_cleanupAnnotations_boxed_1303_, v_whnfType_boxed_1304_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
    lean_dec(v___y_1301_);
    lean_dec_ref(v___y_1300_);
    lean_dec(v___y_1299_);
    lean_dec_ref(v___y_1298_);
    return v_res_1305_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1(
    mut v_00_u03b1_1306_: *mut LeanObject,
    mut v_type_1307_: *mut LeanObject,
    mut v_k_1308_: *mut LeanObject,
    mut v_cleanupAnnotations_1309_: u8,
    mut v_whnfType_1310_: u8,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_type_1307_, v_k_1308_, v_cleanupAnnotations_1309_, v_whnfType_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    return v___x_1316_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___boxed(
    mut v_00_u03b1_1317_: *mut LeanObject,
    mut v_type_1318_: *mut LeanObject,
    mut v_k_1319_: *mut LeanObject,
    mut v_cleanupAnnotations_1320_: *mut LeanObject,
    mut v_whnfType_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1327_: u8 = 0;
    let mut v_whnfType_boxed_1328_: u8 = 0;
    let mut v_res_1329_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1327_ = (lean_unbox(v_cleanupAnnotations_1320_) as u8);
    v_whnfType_boxed_1328_ = (lean_unbox(v_whnfType_1321_) as u8);
    v_res_1329_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1(
            v_00_u03b1_1317_,
            v_type_1318_,
            v_k_1319_,
            v_cleanupAnnotations_boxed_1327_,
            v_whnfType_boxed_1328_,
            v___y_1322_,
            v___y_1323_,
            v___y_1324_,
            v___y_1325_,
        );
    lean_dec(v___y_1325_);
    lean_dec_ref(v___y_1324_);
    lean_dec(v___y_1323_);
    lean_dec_ref(v___y_1322_);
    return v_res_1329_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0(
    mut v_xs_1330_: *mut LeanObject,
    mut v_x_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
        v_xs_1330_,
        v___y_1332_,
        v___y_1333_,
        v___y_1334_,
        v___y_1335_,
    );
    return v___x_1337_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0___boxed(
    mut v_xs_1338_: *mut LeanObject,
    mut v_x_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1345_: *mut LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0(
        v_xs_1338_,
        v_x_1339_,
        v___y_1340_,
        v___y_1341_,
        v___y_1342_,
        v___y_1343_,
    );
    lean_dec(v___y_1343_);
    lean_dec_ref(v___y_1342_);
    lean_dec(v___y_1341_);
    lean_dec_ref(v___y_1340_);
    lean_dec_ref(v_x_1339_);
    lean_dec_ref(v_xs_1338_);
    return v_res_1345_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_1348_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1348_, 0, v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_1350_ = lean_unsigned_to_nat(0);
    v___x_1351_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1351_, 0, v___x_1350_);
    lean_ctor_set(v___x_1351_, 1, v___x_1350_);
    lean_ctor_set(v___x_1351_, 2, v___x_1350_);
    lean_ctor_set(v___x_1351_, 3, v___x_1350_);
    lean_ctor_set(v___x_1351_, 4, v___x_1349_);
    lean_ctor_set(v___x_1351_, 5, v___x_1349_);
    lean_ctor_set(v___x_1351_, 6, v___x_1349_);
    lean_ctor_set(v___x_1351_, 7, v___x_1349_);
    lean_ctor_set(v___x_1351_, 8, v___x_1349_);
    lean_ctor_set(v___x_1351_, 9, v___x_1349_);
    return v___x_1351_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1352_ = lean_unsigned_to_nat(32);
    v___x_1353_ = lean_mk_empty_array_with_capacity(v___x_1352_);
    v___x_1354_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1354_, 0, v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ = 5usize;
    v___x_1356_ = lean_unsigned_to_nat(0);
    v___x_1357_ = lean_unsigned_to_nat(32);
    v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
    v___x_1359_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_1360_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    lean_ctor_set(v___x_1360_, 1, v___x_1358_);
    lean_ctor_set(v___x_1360_, 2, v___x_1356_);
    lean_ctor_set(v___x_1360_, 3, v___x_1356_);
    lean_ctor_set_usize(v___x_1360_, 4, v___x_1355_);
    return v___x_1360_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1361_ = lean_box(1);
    v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_1363_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_1364_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1364_, 0, v___x_1363_);
    lean_ctor_set(v___x_1364_, 1, v___x_1362_);
    lean_ctor_set(v___x_1364_, 2, v___x_1361_);
    return v___x_1364_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
    return v___x_1367_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
    return v___x_1373_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1378_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
    return v___x_1379_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
    return v___x_1382_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
    return v___x_1385_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_1386_: *mut LeanObject,
    mut v_declHint_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v_isExporting_1393_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_st_ref_get(v___y_1388_);
                v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
                lean_inc_ref(v_env_1391_);
                lean_dec(v___x_1390_);
                v___x_1392_ = l_Lean_Name_isAnonymous(v_declHint_1387_);
                if v___x_1392_ == 0 {
                    v_isExporting_1393_ = lean_ctor_get_uint8(
                        v_env_1391_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1393_ == 0 {
                        lean_dec_ref(v_env_1391_);
                        lean_dec(v_declHint_1387_);
                        v___x_1394_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1394_, 0, v_msg_1386_);
                        return v___x_1394_;
                    } else {
                        lean_inc_ref(v_env_1391_);
                        v___x_1395_ = l_Lean_Environment_setExporting(v_env_1391_, v___x_1392_);
                        lean_inc(v_declHint_1387_);
                        lean_inc_ref(v___x_1395_);
                        v___x_1396_ = l_Lean_Environment_contains(
                            v___x_1395_,
                            v_declHint_1387_,
                            v_isExporting_1393_,
                        );
                        if v___x_1396_ == 0 {
                            lean_dec_ref(v___x_1395_);
                            lean_dec_ref(v_env_1391_);
                            lean_dec(v_declHint_1387_);
                            v___x_1397_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1397_, 0, v_msg_1386_);
                            return v___x_1397_;
                        } else {
                            v___x_1398_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_1399_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_1400_ = l_Lean_Options_empty;
                            v___x_1401_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1401_, 0, v___x_1395_);
                            lean_ctor_set(v___x_1401_, 1, v___x_1398_);
                            lean_ctor_set(v___x_1401_, 2, v___x_1399_);
                            lean_ctor_set(v___x_1401_, 3, v___x_1400_);
                            lean_inc(v_declHint_1387_);
                            v___x_1402_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1387_, v___x_1392_);
                            v_c_1403_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1403_, 0, v___x_1401_);
                            lean_ctor_set(v_c_1403_, 1, v___x_1402_);
                            v___x_1404_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1391_,
                                v_declHint_1387_,
                            );
                            if lean_obj_tag(v___x_1404_) == 0 {
                                lean_dec_ref(v_env_1391_);
                                lean_dec(v_declHint_1387_);
                                v___x_1405_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_1406_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1406_, 0, v___x_1405_);
                                lean_ctor_set(v___x_1406_, 1, v_c_1403_);
                                v___x_1407_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_1408_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1408_, 0, v___x_1406_);
                                lean_ctor_set(v___x_1408_, 1, v___x_1407_);
                                v___x_1409_ = l_Lean_MessageData_note(v___x_1408_);
                                v___x_1410_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1410_, 0, v_msg_1386_);
                                lean_ctor_set(v___x_1410_, 1, v___x_1409_);
                                v___x_1411_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1411_, 0, v___x_1410_);
                                return v___x_1411_;
                            } else {
                                v_val_1412_ = lean_ctor_get(v___x_1404_, 0);
                                v_isSharedCheck_1447_ = (!lean_is_exclusive(v___x_1404_)) as u8;
                                if v_isSharedCheck_1447_ == 0 {
                                    v___x_1414_ = v___x_1404_;
                                    v_isShared_1415_ = v_isSharedCheck_1447_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1412_);
                                    lean_dec(v___x_1404_);
                                    v___x_1414_ = lean_box(0);
                                    v_isShared_1415_ = v_isSharedCheck_1447_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1391_);
                    lean_dec(v_declHint_1387_);
                    v___x_1448_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1448_, 0, v_msg_1386_);
                    return v___x_1448_;
                }
            }
            1 => {
                v___x_1416_ = lean_box(0);
                v___x_1417_ = l_Lean_Environment_header(v_env_1391_);
                lean_dec_ref(v_env_1391_);
                v___x_1418_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1417_);
                v_mod_1419_ = lean_array_get(v___x_1416_, v___x_1418_, v_val_1412_);
                lean_dec(v_val_1412_);
                lean_dec_ref(v___x_1418_);
                v___x_1420_ = l_Lean_isPrivateName(v_declHint_1387_);
                lean_dec(v_declHint_1387_);
                if v___x_1420_ == 0 {
                    v___x_1421_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_1422_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1422_, 0, v___x_1421_);
                    lean_ctor_set(v___x_1422_, 1, v_c_1403_);
                    v___x_1423_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_1424_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1424_, 0, v___x_1422_);
                    lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                    v___x_1425_ = l_Lean_MessageData_ofName(v_mod_1419_);
                    v___x_1426_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1426_, 0, v___x_1424_);
                    lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                    v___x_1427_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_1428_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1428_, 0, v___x_1426_);
                    lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                    v___x_1429_ = l_Lean_MessageData_note(v___x_1428_);
                    v___x_1430_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1430_, 0, v_msg_1386_);
                    lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                    if v_isShared_1415_ == 0 {
                        lean_ctor_set_tag(v___x_1414_, 0);
                        lean_ctor_set(v___x_1414_, 0, v___x_1430_);
                        v___x_1432_ = v___x_1414_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
                        v___x_1432_ = v_reuseFailAlloc_1433_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1434_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_1435_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                    lean_ctor_set(v___x_1435_, 1, v_c_1403_);
                    v___x_1436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_1437_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1437_, 0, v___x_1435_);
                    lean_ctor_set(v___x_1437_, 1, v___x_1436_);
                    v___x_1438_ = l_Lean_MessageData_ofName(v_mod_1419_);
                    v___x_1439_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1439_, 0, v___x_1437_);
                    lean_ctor_set(v___x_1439_, 1, v___x_1438_);
                    v___x_1440_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_1441_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1441_, 0, v___x_1439_);
                    lean_ctor_set(v___x_1441_, 1, v___x_1440_);
                    v___x_1442_ = l_Lean_MessageData_note(v___x_1441_);
                    v___x_1443_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1443_, 0, v_msg_1386_);
                    lean_ctor_set(v___x_1443_, 1, v___x_1442_);
                    if v_isShared_1415_ == 0 {
                        lean_ctor_set_tag(v___x_1414_, 0);
                        lean_ctor_set(v___x_1414_, 0, v___x_1443_);
                        v___x_1445_ = v___x_1414_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
                        v___x_1445_ = v_reuseFailAlloc_1446_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1432_;
            }
            3 => {
                return v___x_1445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_1449_: *mut LeanObject,
    mut v_declHint_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1453_: *mut LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1449_, v_declHint_1450_, v___y_1451_);
    lean_dec(v___y_1451_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_msg_1454_: *mut LeanObject,
    mut v_declHint_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1454_, v_declHint_1455_, v___y_1459_);
                v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
                v_isSharedCheck_1471_ = (!lean_is_exclusive(v___x_1461_)) as u8;
                if v_isSharedCheck_1471_ == 0 {
                    v___x_1464_ = v___x_1461_;
                    v_isShared_1465_ = v_isSharedCheck_1471_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1462_);
                    lean_dec(v___x_1461_);
                    v___x_1464_ = lean_box(0);
                    v_isShared_1465_ = v_isSharedCheck_1471_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1466_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1467_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1467_, 0, v___x_1466_);
                lean_ctor_set(v___x_1467_, 1, v_a_1462_);
                if v_isShared_1465_ == 0 {
                    lean_ctor_set(v___x_1464_, 0, v___x_1467_);
                    v___x_1469_ = v___x_1464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1472_: *mut LeanObject,
    mut v_declHint_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
    mut v___y_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1479_: *mut LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1472_, v_declHint_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
    lean_dec(v___y_1477_);
    lean_dec_ref(v___y_1476_);
    lean_dec(v___y_1475_);
    lean_dec_ref(v___y_1474_);
    return v_res_1479_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(
    mut v_msgData_1480_: *mut LeanObject,
    mut v___y_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v___x_1486_ = lean_st_ref_get(v___y_1484_);
    v_env_1487_ = lean_ctor_get(v___x_1486_, 0);
    lean_inc_ref(v_env_1487_);
    lean_dec(v___x_1486_);
    v___x_1488_ = lean_st_ref_get(v___y_1482_);
    v_mctx_1489_ = lean_ctor_get(v___x_1488_, 0);
    lean_inc_ref(v_mctx_1489_);
    lean_dec(v___x_1488_);
    v_lctx_1490_ = lean_ctor_get(v___y_1481_, 2);
    v_options_1491_ = lean_ctor_get(v___y_1483_, 2);
    lean_inc_ref(v_options_1491_);
    lean_inc_ref(v_lctx_1490_);
    v___x_1492_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1492_, 0, v_env_1487_);
    lean_ctor_set(v___x_1492_, 1, v_mctx_1489_);
    lean_ctor_set(v___x_1492_, 2, v_lctx_1490_);
    lean_ctor_set(v___x_1492_, 3, v_options_1491_);
    v___x_1493_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1493_, 0, v___x_1492_);
    lean_ctor_set(v___x_1493_, 1, v_msgData_1480_);
    v___x_1494_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1494_, 0, v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    lean_dec(v___y_1499_);
    lean_dec_ref(v___y_1498_);
    lean_dec(v___y_1497_);
    lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_1502_: *mut LeanObject,
    mut v___y_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
    mut v___y_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1508_ = lean_ctor_get(v___y_1505_, 5);
                v___x_1509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
                v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
                v_isSharedCheck_1518_ = (!lean_is_exclusive(v___x_1509_)) as u8;
                if v_isSharedCheck_1518_ == 0 {
                    v___x_1512_ = v___x_1509_;
                    v_isShared_1513_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1510_);
                    lean_dec(v___x_1509_);
                    v___x_1512_ = lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1508_);
                v___x_1514_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1514_, 0, v_ref_1508_);
                lean_ctor_set(v___x_1514_, 1, v_a_1510_);
                if v_isShared_1513_ == 0 {
                    lean_ctor_set_tag(v___x_1512_, 1);
                    lean_ctor_set(v___x_1512_, 0, v___x_1514_);
                    v___x_1516_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_1519_: *mut LeanObject,
    mut v___y_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
    lean_dec(v___y_1523_);
    lean_dec_ref(v___y_1522_);
    lean_dec(v___y_1521_);
    lean_dec_ref(v___y_1520_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_ref_1526_: *mut LeanObject,
    mut v_msg_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1545_: u8 = 0;
    let mut v_cancelTk_x3f_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1547_: u8 = 0;
    let mut v_inheritedTraceOptions_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1533_ = lean_ctor_get(v___y_1530_, 0);
    v_fileMap_1534_ = lean_ctor_get(v___y_1530_, 1);
    v_options_1535_ = lean_ctor_get(v___y_1530_, 2);
    v_currRecDepth_1536_ = lean_ctor_get(v___y_1530_, 3);
    v_maxRecDepth_1537_ = lean_ctor_get(v___y_1530_, 4);
    v_ref_1538_ = lean_ctor_get(v___y_1530_, 5);
    v_currNamespace_1539_ = lean_ctor_get(v___y_1530_, 6);
    v_openDecls_1540_ = lean_ctor_get(v___y_1530_, 7);
    v_initHeartbeats_1541_ = lean_ctor_get(v___y_1530_, 8);
    v_maxHeartbeats_1542_ = lean_ctor_get(v___y_1530_, 9);
    v_quotContext_1543_ = lean_ctor_get(v___y_1530_, 10);
    v_currMacroScope_1544_ = lean_ctor_get(v___y_1530_, 11);
    v_diag_1545_ = lean_ctor_get_uint8(
        v___y_1530_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1546_ = lean_ctor_get(v___y_1530_, 12);
    v_suppressElabErrors_1547_ = lean_ctor_get_uint8(
        v___y_1530_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1548_ = lean_ctor_get(v___y_1530_, 13);
    v_ref_1549_ = l_Lean_replaceRef(v_ref_1526_, v_ref_1538_);
    lean_inc_ref(v_inheritedTraceOptions_1548_);
    lean_inc(v_cancelTk_x3f_1546_);
    lean_inc(v_currMacroScope_1544_);
    lean_inc(v_quotContext_1543_);
    lean_inc(v_maxHeartbeats_1542_);
    lean_inc(v_initHeartbeats_1541_);
    lean_inc(v_openDecls_1540_);
    lean_inc(v_currNamespace_1539_);
    lean_inc(v_maxRecDepth_1537_);
    lean_inc(v_currRecDepth_1536_);
    lean_inc_ref(v_options_1535_);
    lean_inc_ref(v_fileMap_1534_);
    lean_inc_ref(v_fileName_1533_);
    v___x_1550_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1550_, 0, v_fileName_1533_);
    lean_ctor_set(v___x_1550_, 1, v_fileMap_1534_);
    lean_ctor_set(v___x_1550_, 2, v_options_1535_);
    lean_ctor_set(v___x_1550_, 3, v_currRecDepth_1536_);
    lean_ctor_set(v___x_1550_, 4, v_maxRecDepth_1537_);
    lean_ctor_set(v___x_1550_, 5, v_ref_1549_);
    lean_ctor_set(v___x_1550_, 6, v_currNamespace_1539_);
    lean_ctor_set(v___x_1550_, 7, v_openDecls_1540_);
    lean_ctor_set(v___x_1550_, 8, v_initHeartbeats_1541_);
    lean_ctor_set(v___x_1550_, 9, v_maxHeartbeats_1542_);
    lean_ctor_set(v___x_1550_, 10, v_quotContext_1543_);
    lean_ctor_set(v___x_1550_, 11, v_currMacroScope_1544_);
    lean_ctor_set(v___x_1550_, 12, v_cancelTk_x3f_1546_);
    lean_ctor_set(v___x_1550_, 13, v_inheritedTraceOptions_1548_);
    lean_ctor_set_uint8(
        v___x_1550_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1545_,
    );
    lean_ctor_set_uint8(
        v___x_1550_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1547_,
    );
    v___x_1551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1527_, v___y_1528_, v___y_1529_, v___x_1550_, v___y_1531_);
    lean_dec_ref_known(v___x_1550_, 14);
    return v___x_1551_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_1552_: *mut LeanObject,
    mut v_msg_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1559_: *mut LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1552_, v_msg_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
    lean_dec(v___y_1557_);
    lean_dec_ref(v___y_1556_);
    lean_dec(v___y_1555_);
    lean_dec_ref(v___y_1554_);
    lean_dec(v_ref_1552_);
    return v_res_1559_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_ref_1560_: *mut LeanObject,
    mut v_msg_1561_: *mut LeanObject,
    mut v_declHint_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1561_, v_declHint_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
    v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
    lean_inc(v_a_1569_);
    lean_dec_ref(v___x_1568_);
    v___x_1570_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1560_, v_a_1569_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ref_1571_: *mut LeanObject,
    mut v_msg_1572_: *mut LeanObject,
    mut v_declHint_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1579_: *mut LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1571_, v_msg_1572_, v_declHint_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
    lean_dec(v___y_1577_);
    lean_dec_ref(v___y_1576_);
    lean_dec(v___y_1575_);
    lean_dec_ref(v___y_1574_);
    lean_dec(v_ref_1571_);
    return v_res_1579_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    v___x_1581_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_ref_1586_: *mut LeanObject,
    mut v_constName_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1594_ = 0;
    lean_inc(v_constName_1587_);
    v___x_1595_ = l_Lean_MessageData_ofConstName(v_constName_1587_, v___x_1594_);
    v___x_1596_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1596_, 0, v___x_1593_);
    lean_ctor_set(v___x_1596_, 1, v___x_1595_);
    v___x_1597_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_1598_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1598_, 0, v___x_1596_);
    lean_ctor_set(v___x_1598_, 1, v___x_1597_);
    v___x_1599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1586_, v___x_1598_, v_constName_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_1600_: *mut LeanObject,
    mut v_constName_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1607_: *mut LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1600_, v_constName_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
    lean_dec(v___y_1605_);
    lean_dec_ref(v___y_1604_);
    lean_dec(v___y_1603_);
    lean_dec_ref(v___y_1602_);
    lean_dec(v_ref_1600_);
    return v_res_1607_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1614_ = lean_ctor_get(v___y_1611_, 5);
    v___x_1615_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1614_, v_constName_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1622_: *mut LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
    lean_dec(v___y_1620_);
    lean_dec_ref(v___y_1619_);
    lean_dec(v___y_1618_);
    lean_dec_ref(v___y_1617_);
    return v_res_1622_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
    mut v_constName_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1629_ = lean_st_ref_get(v___y_1627_);
                v_env_1630_ = lean_ctor_get(v___x_1629_, 0);
                lean_inc_ref(v_env_1630_);
                lean_dec(v___x_1629_);
                v___x_1631_ = 0;
                lean_inc(v_constName_1623_);
                v___x_1632_ =
                    l_Lean_Environment_find_x3f(v_env_1630_, v_constName_1623_, v___x_1631_);
                if lean_obj_tag(v___x_1632_) == 0 {
                    v___x_1633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
                    return v___x_1633_;
                } else {
                    lean_dec(v_constName_1623_);
                    v_val_1634_ = lean_ctor_get(v___x_1632_, 0);
                    v_isSharedCheck_1641_ = (!lean_is_exclusive(v___x_1632_)) as u8;
                    if v_isSharedCheck_1641_ == 0 {
                        v___x_1636_ = v___x_1632_;
                        v_isShared_1637_ = v_isSharedCheck_1641_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1634_);
                        lean_dec(v___x_1632_);
                        v___x_1636_ = lean_box(0);
                        v_isShared_1637_ = v_isSharedCheck_1641_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1637_ == 0 {
                    lean_ctor_set_tag(v___x_1636_, 0);
                    v___x_1639_ = v___x_1636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_val_1634_);
                    v___x_1639_ = v_reuseFailAlloc_1640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0___boxed(
    mut v_constName_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
        v_constName_1642_,
        v___y_1643_,
        v___y_1644_,
        v___y_1645_,
        v___y_1646_,
    );
    lean_dec(v___y_1646_);
    lean_dec_ref(v___y_1645_);
    lean_dec(v___y_1644_);
    lean_dec_ref(v___y_1643_);
    return v_res_1648_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f(
    mut v_declName_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v_a_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1675_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1656_ =
                    l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
                        v_declName_1650_,
                        v_a_1651_,
                        v_a_1652_,
                        v_a_1653_,
                        v_a_1654_,
                    );
                if lean_obj_tag(v___x_1656_) == 0 {
                    v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
                    lean_inc(v_a_1657_);
                    lean_dec_ref_known(v___x_1656_, 1);
                    v___x_1658_ = l_Lean_ConstantInfo_type(v_a_1657_);
                    lean_dec(v_a_1657_);
                    v___x_1659_ = l_Lean_Meta_Sym_preprocessType(
                        v___x_1658_,
                        v_a_1651_,
                        v_a_1652_,
                        v_a_1653_,
                        v_a_1654_,
                    );
                    if lean_obj_tag(v___x_1659_) == 0 {
                        v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
                        lean_inc(v_a_1660_);
                        lean_dec_ref_known(v___x_1659_, 1);
                        v___f_1661_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0;
                        v___x_1662_ = 0;
                        v___x_1663_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_a_1660_, v___f_1661_, v___x_1662_, v___x_1662_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
                        return v___x_1663_;
                    } else {
                        v_a_1664_ = lean_ctor_get(v___x_1659_, 0);
                        v_isSharedCheck_1671_ = (!lean_is_exclusive(v___x_1659_)) as u8;
                        if v_isSharedCheck_1671_ == 0 {
                            v___x_1666_ = v___x_1659_;
                            v_isShared_1667_ = v_isSharedCheck_1671_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1664_);
                            lean_dec(v___x_1659_);
                            v___x_1666_ = lean_box(0);
                            v_isShared_1667_ = v_isSharedCheck_1671_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1672_ = lean_ctor_get(v___x_1656_, 0);
                    v_isSharedCheck_1679_ = (!lean_is_exclusive(v___x_1656_)) as u8;
                    if v_isSharedCheck_1679_ == 0 {
                        v___x_1674_ = v___x_1656_;
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1672_);
                        lean_dec(v___x_1656_);
                        v___x_1674_ = lean_box(0);
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1667_ == 0 {
                    v___x_1669_ = v___x_1666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
                    v___x_1669_ = v_reuseFailAlloc_1670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1669_;
            }
            3 => {
                if v_isShared_1675_ == 0 {
                    v___x_1677_ = v___x_1674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
                    v___x_1677_ = v_reuseFailAlloc_1678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___boxed(
    mut v_declName_1680_: *mut LeanObject,
    mut v_a_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
    mut v_a_1683_: *mut LeanObject,
    mut v_a_1684_: *mut LeanObject,
    mut v_a_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1686_: *mut LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f(
        v_declName_1680_,
        v_a_1681_,
        v_a_1682_,
        v_a_1683_,
        v_a_1684_,
    );
    lean_dec(v_a_1684_);
    lean_dec_ref(v_a_1683_);
    lean_dec(v_a_1682_);
    lean_dec_ref(v_a_1681_);
    return v_res_1686_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_1687_: *mut LeanObject,
    mut v_constName_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1695_: *mut LeanObject,
    mut v_constName_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0(v_00_u03b1_1695_, v_constName_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
    lean_dec(v___y_1700_);
    lean_dec_ref(v___y_1699_);
    lean_dec(v___y_1698_);
    lean_dec_ref(v___y_1697_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b1_1703_: *mut LeanObject,
    mut v_ref_1704_: *mut LeanObject,
    mut v_constName_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1704_, v_constName_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_1712_: *mut LeanObject,
    mut v_ref_1713_: *mut LeanObject,
    mut v_constName_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2(v_00_u03b1_1712_, v_ref_1713_, v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    lean_dec(v___y_1718_);
    lean_dec_ref(v___y_1717_);
    lean_dec(v___y_1716_);
    lean_dec_ref(v___y_1715_);
    lean_dec(v_ref_1713_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b1_1721_: *mut LeanObject,
    mut v_ref_1722_: *mut LeanObject,
    mut v_msg_1723_: *mut LeanObject,
    mut v_declHint_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1722_, v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    return v___x_1730_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b1_1731_: *mut LeanObject,
    mut v_ref_1732_: *mut LeanObject,
    mut v_msg_1733_: *mut LeanObject,
    mut v_declHint_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
    mut v___y_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1740_: *mut LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1731_, v_ref_1732_, v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
    lean_dec(v___y_1738_);
    lean_dec_ref(v___y_1737_);
    lean_dec(v___y_1736_);
    lean_dec_ref(v___y_1735_);
    lean_dec(v_ref_1732_);
    return v_res_1740_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_1741_: *mut LeanObject,
    mut v_declHint_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1741_, v_declHint_1742_, v___y_1746_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_1749_: *mut LeanObject,
    mut v_declHint_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1756_: *mut LeanObject = core::ptr::null_mut();
    v_res_1756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1749_, v_declHint_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
    lean_dec(v___y_1754_);
    lean_dec_ref(v___y_1753_);
    lean_dec(v___y_1752_);
    lean_dec_ref(v___y_1751_);
    return v_res_1756_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b1_1757_: *mut LeanObject,
    mut v_ref_1758_: *mut LeanObject,
    mut v_msg_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1758_, v_msg_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
    return v___x_1765_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_1766_: *mut LeanObject,
    mut v_ref_1767_: *mut LeanObject,
    mut v_msg_1768_: *mut LeanObject,
    mut v___y_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1766_, v_ref_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
    lean_dec(v___y_1772_);
    lean_dec_ref(v___y_1771_);
    lean_dec(v___y_1770_);
    lean_dec_ref(v___y_1769_);
    lean_dec(v_ref_1767_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_msg_1776_: *mut LeanObject,
    mut v___y_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    v___x_1782_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_1783_: *mut LeanObject,
    mut v_msg_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1790_: *mut LeanObject = core::ptr::null_mut();
    v_res_1790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1783_, v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
    lean_dec(v___y_1788_);
    lean_dec_ref(v___y_1787_);
    lean_dec(v___y_1786_);
    lean_dec_ref(v___y_1785_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1791_: *mut LeanObject,
    mut v_vals_1792_: *mut LeanObject,
    mut v_i_1793_: *mut LeanObject,
    mut v_k_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_array_get_size(v_keys_1791_);
                v___x_1796_ = lean_nat_dec_lt(v_i_1793_, v___x_1795_);
                if v___x_1796_ == 0 {
                    lean_dec(v_i_1793_);
                    v___x_1797_ = lean_box(0);
                    return v___x_1797_;
                } else {
                    v_k_x27_1798_ = lean_array_fget_borrowed(v_keys_1791_, v_i_1793_);
                    v___x_1799_ = lean_name_eq(v_k_1794_, v_k_x27_1798_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = lean_unsigned_to_nat(1);
                        v___x_1801_ = lean_nat_add(v_i_1793_, v___x_1800_);
                        lean_dec(v_i_1793_);
                        v_i_1793_ = v___x_1801_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1803_ = lean_array_fget_borrowed(v_vals_1792_, v_i_1793_);
                        lean_dec(v_i_1793_);
                        lean_inc(v___x_1803_);
                        v___x_1804_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                        return v___x_1804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1805_: *mut LeanObject,
    mut v_vals_1806_: *mut LeanObject,
    mut v_i_1807_: *mut LeanObject,
    mut v_k_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1809_: *mut LeanObject = core::ptr::null_mut();
    v_res_1809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1805_, v_vals_1806_, v_i_1807_, v_k_1808_);
    lean_dec(v_k_1808_);
    lean_dec_ref(v_vals_1806_);
    lean_dec_ref(v_keys_1805_);
    return v_res_1809_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1810_: usize = 0;
    let mut v___x_1811_: usize = 0;
    let mut v___x_1812_: usize = 0;
    v___x_1810_ = 5usize;
    v___x_1811_ = 1usize;
    v___x_1812_ = lean_usize_shift_left(v___x_1811_, v___x_1810_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: usize = 0;
    let mut v___x_1815_: usize = 0;
    v___x_1813_ = 1usize;
    v___x_1814_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_1815_ = lean_usize_sub(v___x_1814_, v___x_1813_);
    return v___x_1815_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(
    mut v_x_1816_: *mut LeanObject,
    mut v_x_1817_: usize,
    mut v_x_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: usize = 0;
    let mut v___x_1822_: usize = 0;
    let mut v___x_1823_: usize = 0;
    let mut v_j_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: usize = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1816_) == 0 {
                    v_es_1819_ = lean_ctor_get(v_x_1816_, 0);
                    v___x_1820_ = lean_box(2);
                    v___x_1821_ = 5usize;
                    v___x_1822_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1823_ = lean_usize_land(v_x_1817_, v___x_1822_);
                    v_j_1824_ = lean_usize_to_nat(v___x_1823_);
                    v___x_1825_ = lean_array_get_borrowed(v___x_1820_, v_es_1819_, v_j_1824_);
                    lean_dec(v_j_1824_);
                    match lean_obj_tag(v___x_1825_) {
                        0 => {
                            v_key_1826_ = lean_ctor_get(v___x_1825_, 0);
                            v_val_1827_ = lean_ctor_get(v___x_1825_, 1);
                            v___x_1828_ = lean_name_eq(v_x_1818_, v_key_1826_);
                            if v___x_1828_ == 0 {
                                v___x_1829_ = lean_box(0);
                                return v___x_1829_;
                            } else {
                                lean_inc(v_val_1827_);
                                v___x_1830_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1830_, 0, v_val_1827_);
                                return v___x_1830_;
                            }
                        }
                        1 => {
                            v_node_1831_ = lean_ctor_get(v___x_1825_, 0);
                            v___x_1832_ = lean_usize_shift_right(v_x_1817_, v___x_1821_);
                            v_x_1816_ = v_node_1831_;
                            v_x_1817_ = v___x_1832_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1834_ = lean_box(0);
                            return v___x_1834_;
                        }
                    }
                } else {
                    v_ks_1835_ = lean_ctor_get(v_x_1816_, 0);
                    v_vs_1836_ = lean_ctor_get(v_x_1816_, 1);
                    v___x_1837_ = lean_unsigned_to_nat(0);
                    v___x_1838_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1835_, v_vs_1836_, v___x_1837_, v_x_1818_);
                    return v___x_1838_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1839_: *mut LeanObject,
    mut v_x_1840_: *mut LeanObject,
    mut v_x_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2415__boxed_1842_: usize = 0;
    let mut v_res_1843_: *mut LeanObject = core::ptr::null_mut();
    v_x_2415__boxed_1842_ = lean_unbox_usize(v_x_1840_);
    lean_dec(v_x_1840_);
    v_res_1843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_1839_, v_x_2415__boxed_1842_, v_x_1841_);
    lean_dec(v_x_1841_);
    lean_dec_ref(v_x_1839_);
    return v_res_1843_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u64 = 0;
    v___x_1844_ = lean_unsigned_to_nat(1723);
    v___x_1845_ = lean_uint64_of_nat(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(
    mut v_x_1846_: *mut LeanObject,
    mut v_x_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1849_: u64 = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u64 = 0;
    let mut v_hash_1853_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1847_) == 0 {
                    v___x_1852_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                    v___y_1849_ = v___x_1852_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1853_ = lean_ctor_get_uint64(
                        v_x_1847_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1849_ = v_hash_1853_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1850_ = lean_uint64_to_usize(v___y_1849_);
                v___x_1851_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_1846_, v___x_1850_, v_x_1847_);
                return v___x_1851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___boxed(
    mut v_x_1854_: *mut LeanObject,
    mut v_x_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_x_1854_, v_x_1855_);
    lean_dec(v_x_1855_);
    lean_dec_ref(v_x_1854_);
    return v_res_1856_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1857_: *mut LeanObject,
    mut v_x_1858_: *mut LeanObject,
    mut v_x_1859_: *mut LeanObject,
    mut v_x_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1861_ = lean_ctor_get(v_x_1857_, 0);
                v_vs_1862_ = lean_ctor_get(v_x_1857_, 1);
                v_isSharedCheck_1886_ = (!lean_is_exclusive(v_x_1857_)) as u8;
                if v_isSharedCheck_1886_ == 0 {
                    v___x_1864_ = v_x_1857_;
                    v_isShared_1865_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1862_);
                    lean_inc(v_ks_1861_);
                    lean_dec(v_x_1857_);
                    v___x_1864_ = lean_box(0);
                    v_isShared_1865_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1866_ = lean_array_get_size(v_ks_1861_);
                v___x_1867_ = lean_nat_dec_lt(v_x_1858_, v___x_1866_);
                if v___x_1867_ == 0 {
                    lean_dec(v_x_1858_);
                    v___x_1868_ = lean_array_push(v_ks_1861_, v_x_1859_);
                    v___x_1869_ = lean_array_push(v_vs_1862_, v_x_1860_);
                    if v_isShared_1865_ == 0 {
                        lean_ctor_set(v___x_1864_, 1, v___x_1869_);
                        lean_ctor_set(v___x_1864_, 0, v___x_1868_);
                        v___x_1871_ = v___x_1864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1868_);
                        lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
                        v___x_1871_ = v_reuseFailAlloc_1872_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1873_ = lean_array_fget_borrowed(v_ks_1861_, v_x_1858_);
                    v___x_1874_ = lean_name_eq(v_x_1859_, v_k_x27_1873_);
                    if v___x_1874_ == 0 {
                        if v_isShared_1865_ == 0 {
                            v___x_1876_ = v___x_1864_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_ks_1861_);
                            lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_vs_1862_);
                            v___x_1876_ = v_reuseFailAlloc_1880_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1881_ = lean_array_fset(v_ks_1861_, v_x_1858_, v_x_1859_);
                        v___x_1882_ = lean_array_fset(v_vs_1862_, v_x_1858_, v_x_1860_);
                        lean_dec(v_x_1858_);
                        if v_isShared_1865_ == 0 {
                            lean_ctor_set(v___x_1864_, 1, v___x_1882_);
                            lean_ctor_set(v___x_1864_, 0, v___x_1881_);
                            v___x_1884_ = v___x_1864_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
                            lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1882_);
                            v___x_1884_ = v_reuseFailAlloc_1885_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1871_;
            }
            3 => {
                v___x_1877_ = lean_unsigned_to_nat(1);
                v___x_1878_ = lean_nat_add(v_x_1858_, v___x_1877_);
                lean_dec(v_x_1858_);
                v_x_1857_ = v___x_1876_;
                v_x_1858_ = v___x_1878_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_1887_: *mut LeanObject,
    mut v_k_1888_: *mut LeanObject,
    mut v_v_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    v___x_1890_ = lean_unsigned_to_nat(0);
    v___x_1891_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1887_, v___x_1890_, v_k_1888_, v_v_1889_);
    return v___x_1891_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1892_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(
    mut v_x_1893_: *mut LeanObject,
    mut v_x_1894_: usize,
    mut v_x_1895_: usize,
    mut v_x_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v_j_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v_v_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_node_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1934_: usize = 0;
    let mut v___x_1935_: usize = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_unused_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1953_: u8 = 0;
    let mut v_ks_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1893_) == 0 {
                    v_es_1898_ = lean_ctor_get(v_x_1893_, 0);
                    v___x_1899_ = 5usize;
                    v___x_1900_ = 1usize;
                    v___x_1901_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1902_ = lean_usize_land(v_x_1894_, v___x_1901_);
                    v_j_1903_ = lean_usize_to_nat(v___x_1902_);
                    v___x_1904_ = lean_array_get_size(v_es_1898_);
                    v___x_1905_ = lean_nat_dec_lt(v_j_1903_, v___x_1904_);
                    if v___x_1905_ == 0 {
                        lean_dec(v_j_1903_);
                        lean_dec(v_x_1897_);
                        lean_dec(v_x_1896_);
                        return v_x_1893_;
                    } else {
                        lean_inc_ref(v_es_1898_);
                        v_isSharedCheck_1942_ = (!lean_is_exclusive(v_x_1893_)) as u8;
                        if v_isSharedCheck_1942_ == 0 {
                            v_unused_1943_ = lean_ctor_get(v_x_1893_, 0);
                            lean_dec(v_unused_1943_);
                            v___x_1907_ = v_x_1893_;
                            v_isShared_1908_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1893_);
                            v___x_1907_ = lean_box(0);
                            v_isShared_1908_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1944_ = lean_ctor_get(v_x_1893_, 0);
                    v_vs_1945_ = lean_ctor_get(v_x_1893_, 1);
                    v_isSharedCheck_1965_ = (!lean_is_exclusive(v_x_1893_)) as u8;
                    if v_isSharedCheck_1965_ == 0 {
                        v___x_1947_ = v_x_1893_;
                        v_isShared_1948_ = v_isSharedCheck_1965_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1945_);
                        lean_inc(v_ks_1944_);
                        lean_dec(v_x_1893_);
                        v___x_1947_ = lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1965_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1909_ = lean_array_fget(v_es_1898_, v_j_1903_);
                v___x_1910_ = lean_box(0);
                v_xs_x27_1911_ = lean_array_fset(v_es_1898_, v_j_1903_, v___x_1910_);
                match lean_obj_tag(v_v_1909_) {
                    0 => {
                        v_key_1918_ = lean_ctor_get(v_v_1909_, 0);
                        v_val_1919_ = lean_ctor_get(v_v_1909_, 1);
                        v_isSharedCheck_1929_ = (!lean_is_exclusive(v_v_1909_)) as u8;
                        if v_isSharedCheck_1929_ == 0 {
                            v___x_1921_ = v_v_1909_;
                            v_isShared_1922_ = v_isSharedCheck_1929_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1919_);
                            lean_inc(v_key_1918_);
                            lean_dec(v_v_1909_);
                            v___x_1921_ = lean_box(0);
                            v_isShared_1922_ = v_isSharedCheck_1929_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1930_ = lean_ctor_get(v_v_1909_, 0);
                        v_isSharedCheck_1940_ = (!lean_is_exclusive(v_v_1909_)) as u8;
                        if v_isSharedCheck_1940_ == 0 {
                            v___x_1932_ = v_v_1909_;
                            v_isShared_1933_ = v_isSharedCheck_1940_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1930_);
                            lean_dec(v_v_1909_);
                            v___x_1932_ = lean_box(0);
                            v_isShared_1933_ = v_isSharedCheck_1940_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1941_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1941_, 0, v_x_1896_);
                        lean_ctor_set(v___x_1941_, 1, v_x_1897_);
                        v___y_1913_ = v___x_1941_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1914_ = lean_array_fset(v_xs_x27_1911_, v_j_1903_, v___y_1913_);
                lean_dec(v_j_1903_);
                if v_isShared_1908_ == 0 {
                    lean_ctor_set(v___x_1907_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1916_;
            }
            4 => {
                v___x_1923_ = lean_name_eq(v_x_1896_, v_key_1918_);
                if v___x_1923_ == 0 {
                    lean_del_object(v___x_1921_);
                    v___x_1924_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1918_,
                        v_val_1919_,
                        v_x_1896_,
                        v_x_1897_,
                    );
                    v___x_1925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                    v___y_1913_ = v___x_1925_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1919_);
                    lean_dec(v_key_1918_);
                    if v_isShared_1922_ == 0 {
                        lean_ctor_set(v___x_1921_, 1, v_x_1897_);
                        lean_ctor_set(v___x_1921_, 0, v_x_1896_);
                        v___x_1927_ = v___x_1921_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_x_1896_);
                        lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_x_1897_);
                        v___x_1927_ = v_reuseFailAlloc_1928_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1913_ = v___x_1927_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1934_ = lean_usize_shift_right(v_x_1894_, v___x_1899_);
                v___x_1935_ = lean_usize_add(v_x_1895_, v___x_1900_);
                v___x_1936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_node_1930_, v___x_1934_, v___x_1935_, v_x_1896_, v_x_1897_);
                if v_isShared_1933_ == 0 {
                    lean_ctor_set(v___x_1932_, 0, v___x_1936_);
                    v___x_1938_ = v___x_1932_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1913_ = v___x_1938_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_ks_1944_);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_vs_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1951_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(v___x_1950_, v_x_1896_, v_x_1897_);
                v___x_1959_ = 7usize;
                v___x_1960_ = lean_usize_dec_le(v___x_1959_, v_x_1895_);
                if v___x_1960_ == 0 {
                    v___x_1961_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1951_);
                    v___x_1962_ = lean_unsigned_to_nat(4);
                    v___x_1963_ = lean_nat_dec_lt(v___x_1961_, v___x_1962_);
                    lean_dec(v___x_1961_);
                    v___y_1953_ = v___x_1963_;
                    state = 10;
                    continue;
                } else {
                    v___y_1953_ = v___x_1960_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1953_ == 0 {
                    v_ks_1954_ = lean_ctor_get(v_newNode_1951_, 0);
                    lean_inc_ref(v_ks_1954_);
                    v_vs_1955_ = lean_ctor_get(v_newNode_1951_, 1);
                    lean_inc_ref(v_vs_1955_);
                    lean_dec_ref(v_newNode_1951_);
                    v___x_1956_ = lean_unsigned_to_nat(0);
                    v___x_1957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0);
                    v___x_1958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_x_1895_, v_ks_1954_, v_vs_1955_, v___x_1956_, v___x_1957_);
                    lean_dec_ref(v_vs_1955_);
                    lean_dec_ref(v_ks_1954_);
                    return v___x_1958_;
                } else {
                    return v_newNode_1951_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1966_: usize,
    mut v_keys_1967_: *mut LeanObject,
    mut v_vals_1968_: *mut LeanObject,
    mut v_i_1969_: *mut LeanObject,
    mut v_entries_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut v_k_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: u64 = 0;
    let mut v_h_1977_: usize = 0;
    let mut v___x_1978_: usize = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: usize = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v_h_1983_: usize = 0;
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u64 = 0;
    let mut v_hash_1988_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1971_ = lean_array_get_size(v_keys_1967_);
                v___x_1972_ = lean_nat_dec_lt(v_i_1969_, v___x_1971_);
                if v___x_1972_ == 0 {
                    lean_dec(v_i_1969_);
                    return v_entries_1970_;
                } else {
                    v_k_1973_ = lean_array_fget_borrowed(v_keys_1967_, v_i_1969_);
                    v_v_1974_ = lean_array_fget_borrowed(v_vals_1968_, v_i_1969_);
                    if lean_obj_tag(v_k_1973_) == 0 {
                        v___x_1987_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                        v___y_1976_ = v___x_1987_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1988_ = lean_ctor_get_uint64(
                            v_k_1973_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_1976_ = v_hash_1988_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_1977_ = lean_uint64_to_usize(v___y_1976_);
                v___x_1978_ = 5usize;
                v___x_1979_ = lean_unsigned_to_nat(1);
                v___x_1980_ = 1usize;
                v___x_1981_ = lean_usize_sub(v_depth_1966_, v___x_1980_);
                v___x_1982_ = lean_usize_mul(v___x_1978_, v___x_1981_);
                v_h_1983_ = lean_usize_shift_right(v_h_1977_, v___x_1982_);
                v___x_1984_ = lean_nat_add(v_i_1969_, v___x_1979_);
                lean_dec(v_i_1969_);
                lean_inc(v_v_1974_);
                lean_inc(v_k_1973_);
                v___x_1985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_entries_1970_, v_h_1983_, v_depth_1966_, v_k_1973_, v_v_1974_);
                v_i_1969_ = v___x_1984_;
                v_entries_1970_ = v___x_1985_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1989_: *mut LeanObject,
    mut v_keys_1990_: *mut LeanObject,
    mut v_vals_1991_: *mut LeanObject,
    mut v_i_1992_: *mut LeanObject,
    mut v_entries_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1994_: usize = 0;
    let mut v_res_1995_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1994_ = lean_unbox_usize(v_depth_1989_);
    lean_dec(v_depth_1989_);
    v_res_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1994_, v_keys_1990_, v_vals_1991_, v_i_1992_, v_entries_1993_);
    lean_dec_ref(v_vals_1991_);
    lean_dec_ref(v_keys_1990_);
    return v_res_1995_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_1996_: *mut LeanObject,
    mut v_x_1997_: *mut LeanObject,
    mut v_x_1998_: *mut LeanObject,
    mut v_x_1999_: *mut LeanObject,
    mut v_x_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2577__boxed_2001_: usize = 0;
    let mut v_x_2578__boxed_2002_: usize = 0;
    let mut v_res_2003_: *mut LeanObject = core::ptr::null_mut();
    v_x_2577__boxed_2001_ = lean_unbox_usize(v_x_1997_);
    lean_dec(v_x_1997_);
    v_x_2578__boxed_2002_ = lean_unbox_usize(v_x_1998_);
    lean_dec(v_x_1998_);
    v_res_2003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_1996_, v_x_2577__boxed_2001_, v_x_2578__boxed_2002_, v_x_1999_, v_x_2000_);
    return v_res_2003_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(
    mut v_x_2004_: *mut LeanObject,
    mut v_x_2005_: *mut LeanObject,
    mut v_x_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2008_: u64 = 0;
    let mut v___x_2009_: usize = 0;
    let mut v___x_2010_: usize = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u64 = 0;
    let mut v_hash_2013_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2005_) == 0 {
                    v___x_2012_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                    v___y_2008_ = v___x_2012_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2013_ = lean_ctor_get_uint64(
                        v_x_2005_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2008_ = v_hash_2013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2009_ = lean_uint64_to_usize(v___y_2008_);
                v___x_2010_ = 1usize;
                v___x_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_2004_, v___x_2009_, v___x_2010_, v_x_2005_, v_x_2006_);
                return v___x_2011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
    mut v_declName_2014_: *mut LeanObject,
    mut v_a_2015_: *mut LeanObject,
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2060_: u8 = 0;
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ = lean_st_ref_get(v_a_2015_);
                v_proofInstInfo_2022_ = lean_ctor_get(v___x_2021_, 2);
                lean_inc_ref(v_proofInstInfo_2022_);
                lean_dec(v___x_2021_);
                v___x_2023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_proofInstInfo_2022_, v_declName_2014_);
                lean_dec_ref(v_proofInstInfo_2022_);
                if lean_obj_tag(v___x_2023_) == 1 {
                    lean_dec(v_declName_2014_);
                    v_val_2024_ = lean_ctor_get(v___x_2023_, 0);
                    v_isSharedCheck_2031_ = (!lean_is_exclusive(v___x_2023_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v___x_2026_ = v___x_2023_;
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2024_);
                        lean_dec(v___x_2023_);
                        v___x_2026_ = lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2023_);
                    lean_inc(v_declName_2014_);
                    v___x_2032_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f(
                        v_declName_2014_,
                        v_a_2016_,
                        v_a_2017_,
                        v_a_2018_,
                        v_a_2019_,
                    );
                    if lean_obj_tag(v___x_2032_) == 0 {
                        v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
                        v_isSharedCheck_2061_ = (!lean_is_exclusive(v___x_2032_)) as u8;
                        if v_isSharedCheck_2061_ == 0 {
                            v___x_2035_ = v___x_2032_;
                            v_isShared_2036_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2033_);
                            lean_dec(v___x_2032_);
                            v___x_2035_ = lean_box(0);
                            v_isShared_2036_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_2014_);
                        return v___x_2032_;
                    }
                }
            }
            1 => {
                if v_isShared_2027_ == 0 {
                    lean_ctor_set_tag(v___x_2026_, 0);
                    v___x_2029_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2024_);
                    v___x_2029_ = v_reuseFailAlloc_2030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2029_;
            }
            3 => {
                v___x_2037_ = lean_st_ref_take(v_a_2015_);
                v_share_2038_ = lean_ctor_get(v___x_2037_, 0);
                v_maxFVar_2039_ = lean_ctor_get(v___x_2037_, 1);
                v_proofInstInfo_2040_ = lean_ctor_get(v___x_2037_, 2);
                v_inferType_2041_ = lean_ctor_get(v___x_2037_, 3);
                v_getLevel_2042_ = lean_ctor_get(v___x_2037_, 4);
                v_congrInfo_2043_ = lean_ctor_get(v___x_2037_, 5);
                v_defEqI_2044_ = lean_ctor_get(v___x_2037_, 6);
                v_extensions_2045_ = lean_ctor_get(v___x_2037_, 7);
                v_issues_2046_ = lean_ctor_get(v___x_2037_, 8);
                v_canon_2047_ = lean_ctor_get(v___x_2037_, 9);
                v_debug_2048_ = lean_ctor_get_uint8(
                    v___x_2037_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2060_ = (!lean_is_exclusive(v___x_2037_)) as u8;
                if v_isSharedCheck_2060_ == 0 {
                    v___x_2050_ = v___x_2037_;
                    v_isShared_2051_ = v_isSharedCheck_2060_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_2047_);
                    lean_inc(v_issues_2046_);
                    lean_inc(v_extensions_2045_);
                    lean_inc(v_defEqI_2044_);
                    lean_inc(v_congrInfo_2043_);
                    lean_inc(v_getLevel_2042_);
                    lean_inc(v_inferType_2041_);
                    lean_inc(v_proofInstInfo_2040_);
                    lean_inc(v_maxFVar_2039_);
                    lean_inc(v_share_2038_);
                    lean_dec(v___x_2037_);
                    v___x_2050_ = lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_2033_);
                v___x_2052_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(v_proofInstInfo_2040_, v_declName_2014_, v_a_2033_);
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 2, v___x_2052_);
                    v___x_2054_ = v___x_2050_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_share_2038_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_maxFVar_2039_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 2, v___x_2052_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_inferType_2041_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_getLevel_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 5, v_congrInfo_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 6, v_defEqI_2044_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 7, v_extensions_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 8, v_issues_2046_);
                    lean_ctor_set(v_reuseFailAlloc_2059_, 9, v_canon_2047_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2059_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2048_,
                    );
                    v___x_2054_ = v_reuseFailAlloc_2059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2055_ = lean_st_ref_set(v_a_2015_, v___x_2054_);
                if v_isShared_2036_ == 0 {
                    v___x_2057_ = v___x_2035_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2033_);
                    v___x_2057_ = v_reuseFailAlloc_2058_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg___boxed(
    mut v_declName_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
        v_declName_2062_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
        v_a_2067_,
    );
    lean_dec(v_a_2067_);
    lean_dec_ref(v_a_2066_);
    lean_dec(v_a_2065_);
    lean_dec_ref(v_a_2064_);
    lean_dec(v_a_2063_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f(
    mut v_declName_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2078_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
        v_declName_2070_,
        v_a_2072_,
        v_a_2073_,
        v_a_2074_,
        v_a_2075_,
        v_a_2076_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___boxed(
    mut v_declName_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Lean_Meta_Sym_getProofInstInfo_x3f(
        v_declName_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
    );
    lean_dec(v_a_2085_);
    lean_dec_ref(v_a_2084_);
    lean_dec(v_a_2083_);
    lean_dec_ref(v_a_2082_);
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    return v_res_2087_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0(
    mut v_00_u03b2_2088_: *mut LeanObject,
    mut v_x_2089_: *mut LeanObject,
    mut v_x_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    v___x_2091_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_x_2089_, v_x_2090_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___boxed(
    mut v_00_u03b2_2092_: *mut LeanObject,
    mut v_x_2093_: *mut LeanObject,
    mut v_x_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2095_: *mut LeanObject = core::ptr::null_mut();
    v_res_2095_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0(
            v_00_u03b2_2092_,
            v_x_2093_,
            v_x_2094_,
        );
    lean_dec(v_x_2094_);
    lean_dec_ref(v_x_2093_);
    return v_res_2095_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1(
    mut v_00_u03b2_2096_: *mut LeanObject,
    mut v_x_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
    mut v_x_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    v___x_2100_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(v_x_2097_, v_x_2098_, v_x_2099_);
    return v___x_2100_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0(
    mut v_00_u03b2_2101_: *mut LeanObject,
    mut v_x_2102_: *mut LeanObject,
    mut v_x_2103_: usize,
    mut v_x_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_2102_, v_x_2103_, v_x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
    mut v_x_2108_: *mut LeanObject,
    mut v_x_2109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2839__boxed_2110_: usize = 0;
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_x_2839__boxed_2110_ = lean_unbox_usize(v_x_2108_);
    lean_dec(v_x_2108_);
    v_res_2111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0(v_00_u03b2_2106_, v_x_2107_, v_x_2839__boxed_2110_, v_x_2109_);
    lean_dec(v_x_2109_);
    lean_dec_ref(v_x_2107_);
    return v_res_2111_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2(
    mut v_00_u03b2_2112_: *mut LeanObject,
    mut v_x_2113_: *mut LeanObject,
    mut v_x_2114_: usize,
    mut v_x_2115_: usize,
    mut v_x_2116_: *mut LeanObject,
    mut v_x_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_2113_, v_x_2114_, v_x_2115_, v_x_2116_, v_x_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2119_: *mut LeanObject,
    mut v_x_2120_: *mut LeanObject,
    mut v_x_2121_: *mut LeanObject,
    mut v_x_2122_: *mut LeanObject,
    mut v_x_2123_: *mut LeanObject,
    mut v_x_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2850__boxed_2125_: usize = 0;
    let mut v_x_2851__boxed_2126_: usize = 0;
    let mut v_res_2127_: *mut LeanObject = core::ptr::null_mut();
    v_x_2850__boxed_2125_ = lean_unbox_usize(v_x_2121_);
    lean_dec(v_x_2121_);
    v_x_2851__boxed_2126_ = lean_unbox_usize(v_x_2122_);
    lean_dec(v_x_2122_);
    v_res_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2(v_00_u03b2_2119_, v_x_2120_, v_x_2850__boxed_2125_, v_x_2851__boxed_2126_, v_x_2123_, v_x_2124_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2128_: *mut LeanObject,
    mut v_keys_2129_: *mut LeanObject,
    mut v_vals_2130_: *mut LeanObject,
    mut v_heq_2131_: *mut LeanObject,
    mut v_i_2132_: *mut LeanObject,
    mut v_k_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2129_, v_vals_2130_, v_i_2132_, v_k_2133_);
    return v___x_2134_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2135_: *mut LeanObject,
    mut v_keys_2136_: *mut LeanObject,
    mut v_vals_2137_: *mut LeanObject,
    mut v_heq_2138_: *mut LeanObject,
    mut v_i_2139_: *mut LeanObject,
    mut v_k_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2135_, v_keys_2136_, v_vals_2137_, v_heq_2138_, v_i_2139_, v_k_2140_);
    lean_dec(v_k_2140_);
    lean_dec_ref(v_vals_2137_);
    lean_dec_ref(v_keys_2136_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2142_: *mut LeanObject,
    mut v_n_2143_: *mut LeanObject,
    mut v_k_2144_: *mut LeanObject,
    mut v_v_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(v_n_2143_, v_k_2144_, v_v_2145_);
    return v___x_2146_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2147_: *mut LeanObject,
    mut v_depth_2148_: usize,
    mut v_keys_2149_: *mut LeanObject,
    mut v_vals_2150_: *mut LeanObject,
    mut v_heq_2151_: *mut LeanObject,
    mut v_i_2152_: *mut LeanObject,
    mut v_entries_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    v___x_2154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2148_, v_keys_2149_, v_vals_2150_, v_i_2152_, v_entries_2153_);
    return v___x_2154_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2155_: *mut LeanObject,
    mut v_depth_2156_: *mut LeanObject,
    mut v_keys_2157_: *mut LeanObject,
    mut v_vals_2158_: *mut LeanObject,
    mut v_heq_2159_: *mut LeanObject,
    mut v_i_2160_: *mut LeanObject,
    mut v_entries_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2162_: usize = 0;
    let mut v_res_2163_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2162_ = lean_unbox_usize(v_depth_2156_);
    lean_dec(v_depth_2156_);
    v_res_2163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2155_, v_depth_boxed_2162_, v_keys_2157_, v_vals_2158_, v_heq_2159_, v_i_2160_, v_entries_2161_);
    lean_dec_ref(v_vals_2158_);
    lean_dec_ref(v_keys_2157_);
    return v_res_2163_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2164_: *mut LeanObject,
    mut v_x_2165_: *mut LeanObject,
    mut v_x_2166_: *mut LeanObject,
    mut v_x_2167_: *mut LeanObject,
    mut v_x_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2165_, v_x_2166_, v_x_2167_, v_x_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
    mut v_e_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2170_) == 4 {
        let mut v_declName_2177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
        v_declName_2177_ = lean_ctor_get(v_e_2170_, 0);
        lean_inc(v_declName_2177_);
        lean_dec_ref_known(v_e_2170_, 2);
        v___x_2178_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
            v_declName_2177_,
            v_a_2171_,
            v_a_2172_,
            v_a_2173_,
            v_a_2174_,
            v_a_2175_,
        );
        return v___x_2178_;
    } else {
        let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_2170_);
        v___x_2179_ = lean_box(0);
        v___x_2180_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2180_, 0, v___x_2179_);
        return v___x_2180_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg___boxed(
    mut v_e_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
    mut v_a_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2188_: *mut LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
        v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_,
    );
    lean_dec(v_a_2186_);
    lean_dec_ref(v_a_2185_);
    lean_dec(v_a_2184_);
    lean_dec_ref(v_a_2183_);
    lean_dec(v_a_2182_);
    return v_res_2188_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(
    mut v_e_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
        v_e_2189_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_,
    );
    return v___x_2197_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___boxed(
    mut v_e_2198_: *mut LeanObject,
    mut v_a_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2206_: *mut LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(
        v_e_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_,
    );
    lean_dec(v_a_2204_);
    lean_dec_ref(v_a_2203_);
    lean_dec(v_a_2202_);
    lean_dec_ref(v_a_2201_);
    lean_dec(v_a_2200_);
    lean_dec_ref(v_a_2199_);
    return v_res_2206_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_ProofInstInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_ProofInstInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
}
