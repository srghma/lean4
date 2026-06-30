// Lean compiler output
// Module: Lean.ParserCompiler.Attribute
// Imports: Lean.Compiler.InitAttr Lean.ExtraModUses
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_has_compile_error, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_mkAtom,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_getIdent, l_Lean_instInhabitedAttributeImpl_default,
    l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConst___redArg, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_header, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default, l_Lean_instInhabitedEnvExtension_default,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0]};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_ParserCompiler_instInhabitedCombinatorAttribute:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value
        ) as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value
        ) as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value
        ) as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value
        ) as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value
        ) as *mut leanh::LeanObject,
        7677164612348466033 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
    ],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        110, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97,
        116, 116, 114, 105, 98, 117, 116, 101, 32, 91, 0,
    ],
};
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        93, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0(
    mut v_x_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1;
    v___x_1053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1053_, 0, v___x_1052_);
    return v___x_1053_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___boxed(
    mut v_x_1054_: *mut leanh::LeanObject,
    mut v___y_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0(
        v_x_1054_,
        v___y_1055_,
    );
    leanh::lean_dec_ref(v___y_1055_);
    leanh::lean_dec_ref(v_x_1054_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1(
    mut v_s_1058_: *mut leanh::LeanObject,
    mut v_x_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_s_1058_);
    return v_s_1058_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1___boxed(
    mut v_s_1060_: *mut leanh::LeanObject,
    mut v_x_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1(
        v_s_1060_, v_x_1061_,
    );
    leanh::lean_dec_ref(v_x_1061_);
    leanh::lean_dec_ref(v_s_1060_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2(
    mut v_x_1067_: *mut leanh::LeanObject,
    mut v_x_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ =
        l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1;
    return v___x_1069_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___boxed(
    mut v_x_1070_: *mut leanh::LeanObject,
    mut v_x_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2(
        v_x_1070_, v_x_1071_,
    );
    leanh::lean_dec_ref(v_x_1071_);
    leanh::lean_dec_ref(v_x_1070_);
    return v_res_1072_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3(
    mut v_x_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_box(0);
    return v___x_1074_;
}
pub unsafe fn l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3___boxed(
    mut v_x_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1076_ =
        l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3(v_x_1075_);
    leanh::lean_dec_ref(v_x_1075_);
    return v_res_1076_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_instInhabitedEnvExtension_default(leanh::lean_box(0));
    return v___x_1081_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___f_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1082_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3;
    v___f_1083_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2;
    v___f_1084_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1;
    v___f_1085_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0;
    v___x_1086_ = leanh::lean_box(0);
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4_once
        ),
        _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4,
    );
    v___x_1088_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1088_, 0, v___x_1087_);
    leanh::lean_ctor_set(v___x_1088_, 1, v___x_1086_);
    leanh::lean_ctor_set(v___x_1088_, 2, v___f_1085_);
    leanh::lean_ctor_set(v___x_1088_, 3, v___f_1084_);
    leanh::lean_ctor_set(v___x_1088_, 4, v___f_1083_);
    leanh::lean_ctor_set(v___x_1088_, 5, v___f_1082_);
    return v___x_1088_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5_once
        ),
        _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5,
    );
    v___x_1090_ = l_Lean_instInhabitedAttributeImpl_default;
    v___x_1091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    leanh::lean_ctor_set(v___x_1091_, 1, v___x_1089_);
    return v___x_1091_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default()
-> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6_once
        ),
        _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6,
    );
    return v___x_1092_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute()
-> *mut leanh::LeanObject {
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default;
    return v___x_1093_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10;
    v___x_1121_ = l_Lean_mkAtom(v___x_1120_);
    return v___x_1121_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12,
    );
    v___x_1123_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5;
    v___x_1124_ = lean_array_push(v___x_1123_, v___x_1122_);
    return v___x_1124_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17;
    v___x_1134_ = l_Lean_mkAtom(v___x_1133_);
    return v___x_1134_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18,
    );
    v___x_1136_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5;
    v___x_1137_ = lean_array_push(v___x_1136_, v___x_1135_);
    return v___x_1137_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19,
    );
    v___x_1139_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16;
    v___x_1140_ = leanh::lean_box(2);
    v___x_1141_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1141_, 0, v___x_1140_);
    leanh::lean_ctor_set(v___x_1141_, 1, v___x_1139_);
    leanh::lean_ctor_set(v___x_1141_, 2, v___x_1138_);
    return v___x_1141_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20,
    );
    v___x_1143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13,
    );
    v___x_1144_ = lean_array_push(v___x_1143_, v___x_1142_);
    return v___x_1144_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21,
    );
    v___x_1146_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11;
    v___x_1147_ = leanh::lean_box(2);
    v___x_1148_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1148_, 0, v___x_1147_);
    leanh::lean_ctor_set(v___x_1148_, 1, v___x_1146_);
    leanh::lean_ctor_set(v___x_1148_, 2, v___x_1145_);
    return v___x_1148_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1149_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22,
    );
    v___x_1150_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5;
    v___x_1151_ = lean_array_push(v___x_1150_, v___x_1149_);
    return v___x_1151_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23,
    );
    v___x_1153_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9;
    v___x_1154_ = leanh::lean_box(2);
    v___x_1155_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1155_, 0, v___x_1154_);
    leanh::lean_ctor_set(v___x_1155_, 1, v___x_1153_);
    leanh::lean_ctor_set(v___x_1155_, 2, v___x_1152_);
    return v___x_1155_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24,
    );
    v___x_1157_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5;
    v___x_1158_ = lean_array_push(v___x_1157_, v___x_1156_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25,
    );
    v___x_1160_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7;
    v___x_1161_ = leanh::lean_box(2);
    v___x_1162_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
    leanh::lean_ctor_set(v___x_1162_, 1, v___x_1160_);
    leanh::lean_ctor_set(v___x_1162_, 2, v___x_1159_);
    return v___x_1162_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26,
    );
    v___x_1164_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5;
    v___x_1165_ = lean_array_push(v___x_1164_, v___x_1163_);
    return v___x_1165_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27,
    );
    v___x_1167_ = l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4;
    v___x_1168_ = leanh::lean_box(2);
    v___x_1169_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1169_, 0, v___x_1168_);
    leanh::lean_ctor_set(v___x_1169_, 1, v___x_1167_);
    leanh::lean_ctor_set(v___x_1169_, 2, v___x_1166_);
    return v___x_1169_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1()
-> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28,
    );
    return v___x_1170_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1171_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0);
    v___x_1173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1);
    v___x_1175_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1175_, 0, v___x_1174_);
    leanh::lean_ctor_set(v___x_1175_, 1, v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(
    mut v_env_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1189_: u8 = 0;
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_unused_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1179_ = lean_st_ref_take(v___y_1177_);
                v_nextMacroScope_1180_ = leanh::lean_ctor_get(v___x_1179_, 1);
                v_ngen_1181_ = leanh::lean_ctor_get(v___x_1179_, 2);
                v_auxDeclNGen_1182_ = leanh::lean_ctor_get(v___x_1179_, 3);
                v_traceState_1183_ = leanh::lean_ctor_get(v___x_1179_, 4);
                v_messages_1184_ = leanh::lean_ctor_get(v___x_1179_, 6);
                v_infoState_1185_ = leanh::lean_ctor_get(v___x_1179_, 7);
                v_snapshotTasks_1186_ = leanh::lean_ctor_get(v___x_1179_, 8);
                v_isSharedCheck_1197_ = (!leanh::lean_is_exclusive(v___x_1179_)) as u8;
                if v_isSharedCheck_1197_ == 0 {
                    v_unused_1198_ = leanh::lean_ctor_get(v___x_1179_, 5);
                    leanh::lean_dec(v_unused_1198_);
                    v_unused_1199_ = leanh::lean_ctor_get(v___x_1179_, 0);
                    leanh::lean_dec(v_unused_1199_);
                    v___x_1188_ = v___x_1179_;
                    v_isShared_1189_ = v_isSharedCheck_1197_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1186_);
                    leanh::lean_inc(v_infoState_1185_);
                    leanh::lean_inc(v_messages_1184_);
                    leanh::lean_inc(v_traceState_1183_);
                    leanh::lean_inc(v_auxDeclNGen_1182_);
                    leanh::lean_inc(v_ngen_1181_);
                    leanh::lean_inc(v_nextMacroScope_1180_);
                    leanh::lean_dec(v___x_1179_);
                    v___x_1188_ = leanh::lean_box(0);
                    v_isShared_1189_ = v_isSharedCheck_1197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1190_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
                if v_isShared_1189_ == 0 {
                    leanh::lean_ctor_set(v___x_1188_, 5, v___x_1190_);
                    leanh::lean_ctor_set(v___x_1188_, 0, v_env_1176_);
                    v___x_1192_ = v___x_1188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_env_1176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_nextMacroScope_1180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_ngen_1181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_auxDeclNGen_1182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_traceState_1183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 5, v___x_1190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 6, v_messages_1184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 7, v_infoState_1185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 8, v_snapshotTasks_1186_);
                    v___x_1192_ = v_reuseFailAlloc_1196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1193_ = lean_st_ref_set(v___y_1177_, v___x_1192_);
                v___x_1194_ = leanh::lean_box(0);
                v___x_1195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1195_, 0, v___x_1194_);
                return v___x_1195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___boxed(
    mut v_env_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ =
        l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(
            v_env_1200_,
            v___y_1201_,
        );
    leanh::lean_dec(v___y_1201_);
    return v_res_1203_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(
    mut v_env_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ =
        l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(
            v_env_1204_,
            v___y_1206_,
        );
    return v___x_1208_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___boxed(
    mut v_env_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1213_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(
        v_env_1209_,
        v___y_1210_,
        v___y_1211_,
    );
    leanh::lean_dec(v___y_1211_);
    leanh::lean_dec_ref(v___y_1210_);
    return v_res_1213_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(
    mut v_es_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = lean_array_mk(v_es_1214_);
    return v___x_1215_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1(
    mut v_s_1216_: *mut leanh::LeanObject,
    mut v_p_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1218_ = leanh::lean_ctor_get(v_p_1217_, 0);
    leanh::lean_inc(v_fst_1218_);
    v_snd_1219_ = leanh::lean_ctor_get(v_p_1217_, 1);
    leanh::lean_inc(v_snd_1219_);
    leanh::lean_dec_ref(v_p_1217_);
    v___x_1220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_1218_,
        v_snd_1219_,
        v_s_1216_,
    );
    return v___x_1220_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1221_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0);
    v___x_1223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
    return v___x_1223_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1);
    v___x_1225_ = leanh::lean_unsigned_to_nat(0);
    v___x_1226_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1225_);
    leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
    leanh::lean_ctor_set(v___x_1226_, 2, v___x_1225_);
    leanh::lean_ctor_set(v___x_1226_, 3, v___x_1225_);
    leanh::lean_ctor_set(v___x_1226_, 4, v___x_1224_);
    leanh::lean_ctor_set(v___x_1226_, 5, v___x_1224_);
    leanh::lean_ctor_set(v___x_1226_, 6, v___x_1224_);
    leanh::lean_ctor_set(v___x_1226_, 7, v___x_1224_);
    leanh::lean_ctor_set(v___x_1226_, 8, v___x_1224_);
    leanh::lean_ctor_set(v___x_1226_, 9, v___x_1224_);
    return v___x_1226_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = leanh::lean_unsigned_to_nat(32);
    v___x_1228_ = lean_mk_empty_array_with_capacity(v___x_1227_);
    v___x_1229_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1229_, 0, v___x_1228_);
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1230_: usize = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = 5usize;
    v___x_1231_ = leanh::lean_unsigned_to_nat(0);
    v___x_1232_ = leanh::lean_unsigned_to_nat(32);
    v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
    v___x_1234_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3);
    v___x_1235_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1235_, 0, v___x_1234_);
    leanh::lean_ctor_set(v___x_1235_, 1, v___x_1233_);
    leanh::lean_ctor_set(v___x_1235_, 2, v___x_1231_);
    leanh::lean_ctor_set(v___x_1235_, 3, v___x_1231_);
    leanh::lean_ctor_set_usize(v___x_1235_, 4, v___x_1230_);
    return v___x_1235_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = leanh::lean_box(1);
    v___x_1237_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4);
    v___x_1238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1);
    v___x_1239_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    leanh::lean_ctor_set(v___x_1239_, 1, v___x_1237_);
    leanh::lean_ctor_set(v___x_1239_, 2, v___x_1236_);
    return v___x_1239_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(
    mut v_msgData_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1244_ = lean_st_ref_get(v___y_1242_);
    v_env_1245_ = leanh::lean_ctor_get(v___x_1244_, 0);
    leanh::lean_inc_ref(v_env_1245_);
    leanh::lean_dec(v___x_1244_);
    v_options_1246_ = leanh::lean_ctor_get(v___y_1241_, 2);
    v___x_1247_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2);
    v___x_1248_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_1246_);
    v___x_1249_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1249_, 0, v_env_1245_);
    leanh::lean_ctor_set(v___x_1249_, 1, v___x_1247_);
    leanh::lean_ctor_set(v___x_1249_, 2, v___x_1248_);
    leanh::lean_ctor_set(v___x_1249_, 3, v_options_1246_);
    v___x_1250_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    leanh::lean_ctor_set(v___x_1250_, 1, v_msgData_1240_);
    v___x_1251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___boxed(
    mut v_msgData_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msgData_1252_, v___y_1253_, v___y_1254_);
    leanh::lean_dec(v___y_1254_);
    leanh::lean_dec_ref(v___y_1253_);
    return v_res_1256_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(
    mut v_msg_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1261_ = leanh::lean_ctor_get(v___y_1258_, 5);
                v___x_1262_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_1257_, v___y_1258_, v___y_1259_);
                v_a_1263_ = leanh::lean_ctor_get(v___x_1262_, 0);
                v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v___x_1262_)) as u8;
                if v_isSharedCheck_1271_ == 0 {
                    v___x_1265_ = v___x_1262_;
                    v_isShared_1266_ = v_isSharedCheck_1271_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1263_);
                    leanh::lean_dec(v___x_1262_);
                    v___x_1265_ = leanh::lean_box(0);
                    v_isShared_1266_ = v_isSharedCheck_1271_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1261_);
                v___x_1267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1267_, 0, v_ref_1261_);
                leanh::lean_ctor_set(v___x_1267_, 1, v_a_1263_);
                if v_isShared_1266_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1265_, 1);
                    leanh::lean_ctor_set(v___x_1265_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg___boxed(
    mut v_msg_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ =
        l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(
            v_msg_1272_,
            v___y_1273_,
            v___y_1274_,
        );
    leanh::lean_dec(v___y_1274_);
    leanh::lean_dec_ref(v___y_1273_);
    return v_res_1276_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0;
    v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2;
    v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(
    mut v_name_1283_: *mut leanh::LeanObject,
    mut v_decl_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1,
    );
    v___x_1289_ = l_Lean_MessageData_ofName(v_name_1283_);
    v___x_1290_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1290_, 0, v___x_1288_);
    leanh::lean_ctor_set(v___x_1290_, 1, v___x_1289_);
    v___x_1291_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3_once
        ),
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3,
    );
    v___x_1292_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1292_, 0, v___x_1290_);
    leanh::lean_ctor_set(v___x_1292_, 1, v___x_1291_);
    v___x_1293_ =
        l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(
            v___x_1292_,
            v___y_1285_,
            v___y_1286_,
        );
    return v___x_1293_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___boxed(
    mut v_name_1294_: *mut leanh::LeanObject,
    mut v_decl_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(
        v_name_1294_,
        v_decl_1295_,
        v___y_1296_,
        v___y_1297_,
    );
    leanh::lean_dec(v___y_1297_);
    leanh::lean_dec_ref(v___y_1296_);
    leanh::lean_dec(v_decl_1295_);
    return v_res_1299_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0()
-> f64 {
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: f64 = 0.0;
    v___x_1300_ = leanh::lean_unsigned_to_nat(0);
    v___x_1301_ = lean_float_of_nat(v___x_1300_);
    return v___x_1301_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(
    mut v_cls_1305_: *mut leanh::LeanObject,
    mut v_msg_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v_tid_1329_: u64 = 0;
    let mut v_traces_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: f64 = 0.0;
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1310_ = leanh::lean_ctor_get(v___y_1307_, 5);
                v___x_1311_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_1306_, v___y_1307_, v___y_1308_);
                v_a_1312_ = leanh::lean_ctor_get(v___x_1311_, 0);
                v_isSharedCheck_1356_ = (!leanh::lean_is_exclusive(v___x_1311_)) as u8;
                if v_isSharedCheck_1356_ == 0 {
                    v___x_1314_ = v___x_1311_;
                    v_isShared_1315_ = v_isSharedCheck_1356_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1312_);
                    leanh::lean_dec(v___x_1311_);
                    v___x_1314_ = leanh::lean_box(0);
                    v_isShared_1315_ = v_isSharedCheck_1356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1316_ = lean_st_ref_take(v___y_1308_);
                v_traceState_1317_ = leanh::lean_ctor_get(v___x_1316_, 4);
                v_env_1318_ = leanh::lean_ctor_get(v___x_1316_, 0);
                v_nextMacroScope_1319_ = leanh::lean_ctor_get(v___x_1316_, 1);
                v_ngen_1320_ = leanh::lean_ctor_get(v___x_1316_, 2);
                v_auxDeclNGen_1321_ = leanh::lean_ctor_get(v___x_1316_, 3);
                v_cache_1322_ = leanh::lean_ctor_get(v___x_1316_, 5);
                v_messages_1323_ = leanh::lean_ctor_get(v___x_1316_, 6);
                v_infoState_1324_ = leanh::lean_ctor_get(v___x_1316_, 7);
                v_snapshotTasks_1325_ = leanh::lean_ctor_get(v___x_1316_, 8);
                v_isSharedCheck_1355_ = (!leanh::lean_is_exclusive(v___x_1316_)) as u8;
                if v_isSharedCheck_1355_ == 0 {
                    v___x_1327_ = v___x_1316_;
                    v_isShared_1328_ = v_isSharedCheck_1355_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1325_);
                    leanh::lean_inc(v_infoState_1324_);
                    leanh::lean_inc(v_messages_1323_);
                    leanh::lean_inc(v_cache_1322_);
                    leanh::lean_inc(v_traceState_1317_);
                    leanh::lean_inc(v_auxDeclNGen_1321_);
                    leanh::lean_inc(v_ngen_1320_);
                    leanh::lean_inc(v_nextMacroScope_1319_);
                    leanh::lean_inc(v_env_1318_);
                    leanh::lean_dec(v___x_1316_);
                    v___x_1327_ = leanh::lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1329_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1330_ = leanh::lean_ctor_get(v_traceState_1317_, 0);
                v_isSharedCheck_1354_ =
                    (!leanh::lean_is_exclusive(v_traceState_1317_)) as u8;
                if v_isSharedCheck_1354_ == 0 {
                    v___x_1332_ = v_traceState_1317_;
                    v_isShared_1333_ = v_isSharedCheck_1354_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1330_);
                    leanh::lean_dec(v_traceState_1317_);
                    v___x_1332_ = leanh::lean_box(0);
                    v_isShared_1333_ = v_isSharedCheck_1354_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1334_ = leanh::lean_box(0);
                v___x_1335_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0);
                v___x_1336_ = 0;
                v___x_1337_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1;
                v___x_1338_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1338_, 0, v_cls_1305_);
                leanh::lean_ctor_set(v___x_1338_, 1, v___x_1334_);
                leanh::lean_ctor_set(v___x_1338_, 2, v___x_1337_);
                leanh::lean_ctor_set_float(
                    v___x_1338_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1335_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1338_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1335_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1338_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1336_,
                );
                v___x_1339_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2;
                v___x_1340_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1340_, 0, v___x_1338_);
                leanh::lean_ctor_set(v___x_1340_, 1, v_a_1312_);
                leanh::lean_ctor_set(v___x_1340_, 2, v___x_1339_);
                leanh::lean_inc(v_ref_1310_);
                v___x_1341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1341_, 0, v_ref_1310_);
                leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
                v___x_1342_ = l_Lean_PersistentArray_push___redArg(v_traces_1330_, v___x_1341_);
                if v_isShared_1333_ == 0 {
                    leanh::lean_ctor_set(v___x_1332_, 0, v___x_1342_);
                    v___x_1344_ = v___x_1332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1342_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1353_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1329_,
                    );
                    v___x_1344_ = v_reuseFailAlloc_1353_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1328_ == 0 {
                    leanh::lean_ctor_set(v___x_1327_, 4, v___x_1344_);
                    v___x_1346_ = v___x_1327_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_env_1318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_nextMacroScope_1319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_ngen_1320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_auxDeclNGen_1321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 4, v___x_1344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 5, v_cache_1322_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 6, v_messages_1323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 7, v_infoState_1324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 8, v_snapshotTasks_1325_);
                    v___x_1346_ = v_reuseFailAlloc_1352_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1347_ = lean_st_ref_set(v___y_1308_, v___x_1346_);
                v___x_1348_ = leanh::lean_box(0);
                if v_isShared_1315_ == 0 {
                    leanh::lean_ctor_set(v___x_1314_, 0, v___x_1348_);
                    v___x_1350_ = v___x_1314_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
                    v___x_1350_ = v_reuseFailAlloc_1351_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___boxed(
    mut v_cls_1357_: *mut leanh::LeanObject,
    mut v_msg_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_1357_, v_msg_1358_, v___y_1359_, v___y_1360_);
    leanh::lean_dec(v___y_1360_);
    leanh::lean_dec_ref(v___y_1359_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(
    mut v_keys_1363_: *mut leanh::LeanObject,
    mut v_i_1364_: *mut leanh::LeanObject,
    mut v_k_1365_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v_k_x27_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1366_ = lean_array_get_size(v_keys_1363_);
                v___x_1367_ = lean_nat_dec_lt(v_i_1364_, v___x_1366_);
                if v___x_1367_ == 0 {
                    leanh::lean_dec(v_i_1364_);
                    return v___x_1367_;
                } else {
                    v_k_x27_1368_ = lean_array_fget_borrowed(v_keys_1363_, v_i_1364_);
                    v___x_1369_ = l_Lean_instBEqExtraModUse_beq(v_k_1365_, v_k_x27_1368_);
                    if v___x_1369_ == 0 {
                        v___x_1370_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1371_ = lean_nat_add(v_i_1364_, v___x_1370_);
                        leanh::lean_dec(v_i_1364_);
                        v_i_1364_ = v___x_1371_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1364_);
                        return v___x_1369_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg___boxed(
    mut v_keys_1373_: *mut leanh::LeanObject,
    mut v_i_1374_: *mut leanh::LeanObject,
    mut v_k_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1376_: u8 = 0;
    let mut v_r_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_1373_, v_i_1374_, v_k_1375_);
    leanh::lean_dec_ref(v_k_1375_);
    leanh::lean_dec_ref(v_keys_1373_);
    v_r_1377_ = leanh::lean_box((v_res_1376_) as usize);
    return v_r_1377_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_1378_: usize = 0;
    let mut v___x_1379_: usize = 0;
    let mut v___x_1380_: usize = 0;
    v___x_1378_ = 5usize;
    v___x_1379_ = 1usize;
    v___x_1380_ = lean_usize_shift_left(v___x_1379_, v___x_1378_);
    return v___x_1380_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_1381_: usize = 0;
    let mut v___x_1382_: usize = 0;
    let mut v___x_1383_: usize = 0;
    v___x_1381_ = 1usize;
    v___x_1382_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__0);
    v___x_1383_ = lean_usize_sub(v___x_1382_, v___x_1381_);
    return v___x_1383_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(
    mut v_x_1384_: *mut leanh::LeanObject,
    mut v_x_1385_: usize,
    mut v_x_1386_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v_j_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut v_node_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: usize = 0;
    let mut v___x_1399_: u8 = 0;
    let mut v_ks_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1384_) == 0 {
                    v_es_1387_ = leanh::lean_ctor_get(v_x_1384_, 0);
                    v___x_1388_ = leanh::lean_box(2);
                    v___x_1389_ = 5usize;
                    v___x_1390_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___closed__1);
                    v___x_1391_ = lean_usize_land(v_x_1385_, v___x_1390_);
                    v_j_1392_ = lean_usize_to_nat(v___x_1391_);
                    v___x_1393_ = lean_array_get_borrowed(v___x_1388_, v_es_1387_, v_j_1392_);
                    leanh::lean_dec(v_j_1392_);
                    match leanh::lean_obj_tag(v___x_1393_) {
                        0 => {
                            v_key_1394_ = leanh::lean_ctor_get(v___x_1393_, 0);
                            v___x_1395_ = l_Lean_instBEqExtraModUse_beq(v_x_1386_, v_key_1394_);
                            return v___x_1395_;
                        }
                        1 => {
                            v_node_1396_ = leanh::lean_ctor_get(v___x_1393_, 0);
                            v___x_1397_ = lean_usize_shift_right(v_x_1385_, v___x_1389_);
                            v_x_1384_ = v_node_1396_;
                            v_x_1385_ = v___x_1397_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1399_ = 0;
                            return v___x_1399_;
                        }
                    }
                } else {
                    v_ks_1400_ = leanh::lean_ctor_get(v_x_1384_, 0);
                    v___x_1401_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1402_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_ks_1400_, v___x_1401_, v_x_1386_);
                    return v___x_1402_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___boxed(
    mut v_x_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
    mut v_x_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5226__boxed_1406_: usize = 0;
    let mut v_res_1407_: u8 = 0;
    let mut v_r_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5226__boxed_1406_ = leanh::lean_unbox_usize(v_x_1404_);
    leanh::lean_dec(v_x_1404_);
    v_res_1407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_1403_, v_x_5226__boxed_1406_, v_x_1405_);
    leanh::lean_dec_ref(v_x_1405_);
    leanh::lean_dec_ref(v_x_1403_);
    v_r_1408_ = leanh::lean_box((v_res_1407_) as usize);
    return v_r_1408_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(
    mut v_x_1409_: *mut leanh::LeanObject,
    mut v_x_1410_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1411_: u64 = 0;
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: u8 = 0;
    v___x_1411_ = l_Lean_instHashableExtraModUse_hash(v_x_1410_);
    v___x_1412_ = lean_uint64_to_usize(v___x_1411_);
    v___x_1413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_1409_, v___x_1412_, v_x_1410_);
    return v___x_1413_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_x_1414_: *mut leanh::LeanObject,
    mut v_x_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1416_: u8 = 0;
    let mut v_r_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_1414_, v_x_1415_);
    leanh::lean_dec_ref(v_x_1415_);
    leanh::lean_dec_ref(v_x_1414_);
    v_r_1417_ = leanh::lean_box((v_res_1416_) as usize);
    return v_r_1417_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1;
    v___x_1421_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0;
    v___x_1422_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1421_,
        v___x_1420_,
    );
    return v___x_1422_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5;
    v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7;
    v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1;
    v___x_1433_ = l_Lean_stringToMessageData(v___x_1432_);
    return v___x_1433_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12()
-> *mut leanh::LeanObject {
    let mut v_cls_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_1437_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4;
    v___x_1438_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11;
    v___x_1439_ = l_Lean_Name_append(v___x_1438_, v_cls_1437_);
    return v___x_1439_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13;
    v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15;
    v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
    return v___x_1445_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(
    mut v_mod_1450_: *mut leanh::LeanObject,
    mut v_isMeta_1451_: u8,
    mut v_hint_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1458_: u8 = 0;
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v_asyncMode_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v_options_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1495_: u8 = 0;
    let mut v_inheritedTraceOptions_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_st_ref_get(v___y_1454_);
                v_env_1457_ = leanh::lean_ctor_get(v___x_1456_, 0);
                leanh::lean_inc_ref(v_env_1457_);
                leanh::lean_dec(v___x_1456_);
                v_isExporting_1458_ = leanh::lean_ctor_get_uint8(
                    v_env_1457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_1457_);
                v___x_1459_ = lean_st_ref_get(v___y_1454_);
                v_env_1460_ = leanh::lean_ctor_get(v___x_1459_, 0);
                leanh::lean_inc_ref(v_env_1460_);
                leanh::lean_dec(v___x_1459_);
                v___x_1461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2);
                leanh::lean_inc(v_mod_1450_);
                v_entry_1462_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_1462_, 0, v_mod_1450_);
                leanh::lean_ctor_set_uint8(
                    v_entry_1462_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_1458_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_1462_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_1451_,
                );
                v___x_1463_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_1464_ = leanh::lean_box(1);
                v___x_1465_ = leanh::lean_box(0);
                v___x_1492_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1461_,
                    v___x_1463_,
                    v_env_1460_,
                    v___x_1464_,
                    v___x_1465_,
                );
                v___x_1493_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v___x_1492_, v_entry_1462_);
                leanh::lean_dec(v___x_1492_);
                if v___x_1493_ == 0 {
                    v_options_1494_ = leanh::lean_ctor_get(v___y_1453_, 2);
                    v_hasTrace_1495_ = leanh::lean_ctor_get_uint8(
                        v_options_1494_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_1495_ == 0 {
                        leanh::lean_dec(v_hint_1452_);
                        leanh::lean_dec(v_mod_1450_);
                        v___y_1467_ = v___y_1454_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_1496_ =
                            leanh::lean_ctor_get(v___y_1453_, 13);
                        v_cls_1497_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4;
                        v___x_1517_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12);
                        v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1496_,
                            v_options_1494_,
                            v___x_1517_,
                        );
                        if v___x_1518_ == 0 {
                            leanh::lean_dec(v_hint_1452_);
                            leanh::lean_dec(v_mod_1450_);
                            v___y_1467_ = v___y_1454_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14);
                            if v_isExporting_1458_ == 0 {
                                v___x_1528_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19;
                                v___y_1521_ = v___x_1528_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1529_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20;
                                v___y_1521_ = v___x_1529_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_1462_, 1);
                    leanh::lean_dec(v_hint_1452_);
                    leanh::lean_dec(v_mod_1450_);
                    v___x_1530_ = leanh::lean_box(0);
                    v___x_1531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
                    return v___x_1531_;
                }
            }
            1 => {
                v___x_1468_ = lean_st_ref_take(v___y_1467_);
                v_toEnvExtension_1469_ = leanh::lean_ctor_get(v___x_1463_, 0);
                v_env_1470_ = leanh::lean_ctor_get(v___x_1468_, 0);
                v_nextMacroScope_1471_ = leanh::lean_ctor_get(v___x_1468_, 1);
                v_ngen_1472_ = leanh::lean_ctor_get(v___x_1468_, 2);
                v_auxDeclNGen_1473_ = leanh::lean_ctor_get(v___x_1468_, 3);
                v_traceState_1474_ = leanh::lean_ctor_get(v___x_1468_, 4);
                v_messages_1475_ = leanh::lean_ctor_get(v___x_1468_, 6);
                v_infoState_1476_ = leanh::lean_ctor_get(v___x_1468_, 7);
                v_snapshotTasks_1477_ = leanh::lean_ctor_get(v___x_1468_, 8);
                v_isSharedCheck_1490_ = (!leanh::lean_is_exclusive(v___x_1468_)) as u8;
                if v_isSharedCheck_1490_ == 0 {
                    v_unused_1491_ = leanh::lean_ctor_get(v___x_1468_, 5);
                    leanh::lean_dec(v_unused_1491_);
                    v___x_1479_ = v___x_1468_;
                    v_isShared_1480_ = v_isSharedCheck_1490_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1477_);
                    leanh::lean_inc(v_infoState_1476_);
                    leanh::lean_inc(v_messages_1475_);
                    leanh::lean_inc(v_traceState_1474_);
                    leanh::lean_inc(v_auxDeclNGen_1473_);
                    leanh::lean_inc(v_ngen_1472_);
                    leanh::lean_inc(v_nextMacroScope_1471_);
                    leanh::lean_inc(v_env_1470_);
                    leanh::lean_dec(v___x_1468_);
                    v___x_1479_ = leanh::lean_box(0);
                    v_isShared_1480_ = v_isSharedCheck_1490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_1481_ = leanh::lean_ctor_get(v_toEnvExtension_1469_, 2);
                v___x_1482_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_1463_,
                    v_env_1470_,
                    v_entry_1462_,
                    v_asyncMode_1481_,
                    v___x_1465_,
                );
                v___x_1483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
                if v_isShared_1480_ == 0 {
                    leanh::lean_ctor_set(v___x_1479_, 5, v___x_1483_);
                    leanh::lean_ctor_set(v___x_1479_, 0, v___x_1482_);
                    v___x_1485_ = v___x_1479_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_nextMacroScope_1471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_ngen_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_auxDeclNGen_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_traceState_1474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 5, v___x_1483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 6, v_messages_1475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 7, v_infoState_1476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 8, v_snapshotTasks_1477_);
                    v___x_1485_ = v_reuseFailAlloc_1489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1486_ = lean_st_ref_set(v___y_1467_, v___x_1485_);
                v___x_1487_ = leanh::lean_box(0);
                v___x_1488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                return v___x_1488_;
            }
            4 => {
                v___x_1501_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1501_, 0, v___y_1499_);
                leanh::lean_ctor_set(v___x_1501_, 1, v___y_1500_);
                v___x_1502_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_1497_, v___x_1501_, v___y_1453_, v___y_1454_);
                if leanh::lean_obj_tag(v___x_1502_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1502_, 1);
                    v___y_1467_ = v___y_1454_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_1462_, 1);
                    return v___x_1502_;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_1505_);
                v___x_1506_ = l_Lean_stringToMessageData(v___y_1505_);
                v___x_1507_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1507_, 0, v___y_1504_);
                leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
                v___x_1508_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6);
                v___x_1509_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1509_, 0, v___x_1507_);
                leanh::lean_ctor_set(v___x_1509_, 1, v___x_1508_);
                v___x_1510_ = l_Lean_MessageData_ofName(v_mod_1450_);
                v___x_1511_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1511_, 0, v___x_1509_);
                leanh::lean_ctor_set(v___x_1511_, 1, v___x_1510_);
                v___x_1512_ = l_Lean_Name_isAnonymous(v_hint_1452_);
                if v___x_1512_ == 0 {
                    v___x_1513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8);
                    v___x_1514_ = l_Lean_MessageData_ofName(v_hint_1452_);
                    v___x_1515_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1515_, 0, v___x_1513_);
                    leanh::lean_ctor_set(v___x_1515_, 1, v___x_1514_);
                    v___y_1499_ = v___x_1511_;
                    v___y_1500_ = v___x_1515_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_1452_);
                    v___x_1516_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9);
                    v___y_1499_ = v___x_1511_;
                    v___y_1500_ = v___x_1516_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_1521_);
                v___x_1522_ = l_Lean_stringToMessageData(v___y_1521_);
                v___x_1523_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1523_, 0, v___x_1519_);
                leanh::lean_ctor_set(v___x_1523_, 1, v___x_1522_);
                v___x_1524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16);
                v___x_1525_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1525_, 0, v___x_1523_);
                leanh::lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                if v_isMeta_1451_ == 0 {
                    v___x_1526_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17;
                    v___y_1504_ = v___x_1525_;
                    v___y_1505_ = v___x_1526_;
                    state = 5;
                    continue;
                } else {
                    v___x_1527_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18;
                    v___y_1504_ = v___x_1525_;
                    v___y_1505_ = v___x_1527_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___boxed(
    mut v_mod_1532_: *mut leanh::LeanObject,
    mut v_isMeta_1533_: *mut leanh::LeanObject,
    mut v_hint_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_1538_: u8 = 0;
    let mut v_res_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_1538_ = (leanh::lean_unbox(v_isMeta_1533_) as u8);
    v_res_1539_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_mod_1532_, v_isMeta_boxed_1538_, v_hint_1534_, v___y_1535_, v___y_1536_);
    leanh::lean_dec(v___y_1536_);
    leanh::lean_dec_ref(v___y_1535_);
    return v_res_1539_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(
    mut v___x_1540_: *mut leanh::LeanObject,
    mut v_declName_1541_: *mut leanh::LeanObject,
    mut v_as_1542_: *mut leanh::LeanObject,
    mut v_sz_1543_: usize,
    mut v_i_1544_: usize,
    mut v_b_1545_: *mut leanh::LeanObject,
    mut v___y_1546_: *mut leanh::LeanObject,
    mut v___y_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1549_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
                if v___x_1549_ == 0 {
                    leanh::lean_dec(v_declName_1541_);
                    v___x_1550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1550_, 0, v_b_1545_);
                    return v___x_1550_;
                } else {
                    v___x_1551_ = l_Lean_Environment_header(v___x_1540_);
                    v_modules_1552_ = leanh::lean_ctor_get(v___x_1551_, 3);
                    leanh::lean_inc_ref(v_modules_1552_);
                    leanh::lean_dec_ref(v___x_1551_);
                    v___x_1553_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_1554_ = lean_array_uget_borrowed(v_as_1542_, v_i_1544_);
                    v___x_1555_ = lean_array_get(v___x_1553_, v_modules_1552_, v_a_1554_);
                    leanh::lean_dec_ref(v_modules_1552_);
                    v_toImport_1556_ = leanh::lean_ctor_get(v___x_1555_, 0);
                    leanh::lean_inc_ref(v_toImport_1556_);
                    leanh::lean_dec(v___x_1555_);
                    v_module_1557_ = leanh::lean_ctor_get(v_toImport_1556_, 0);
                    leanh::lean_inc(v_module_1557_);
                    leanh::lean_dec_ref(v_toImport_1556_);
                    v___x_1558_ = 0;
                    leanh::lean_inc(v_declName_1541_);
                    v___x_1559_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_1557_, v___x_1558_, v_declName_1541_, v___y_1546_, v___y_1547_);
                    if leanh::lean_obj_tag(v___x_1559_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1559_, 1);
                        v___x_1560_ = leanh::lean_box(0);
                        v___x_1561_ = 1usize;
                        v___x_1562_ = lean_usize_add(v_i_1544_, v___x_1561_);
                        v_i_1544_ = v___x_1562_;
                        v_b_1545_ = v___x_1560_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_1541_);
                        return v___x_1559_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6___boxed(
    mut v___x_1564_: *mut leanh::LeanObject,
    mut v_declName_1565_: *mut leanh::LeanObject,
    mut v_as_1566_: *mut leanh::LeanObject,
    mut v_sz_1567_: *mut leanh::LeanObject,
    mut v_i_1568_: *mut leanh::LeanObject,
    mut v_b_1569_: *mut leanh::LeanObject,
    mut v___y_1570_: *mut leanh::LeanObject,
    mut v___y_1571_: *mut leanh::LeanObject,
    mut v___y_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1573_: usize = 0;
    let mut v_i_boxed_1574_: usize = 0;
    let mut v_res_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1573_ = leanh::lean_unbox_usize(v_sz_1567_);
    leanh::lean_dec(v_sz_1567_);
    v_i_boxed_1574_ = leanh::lean_unbox_usize(v_i_1568_);
    leanh::lean_dec(v_i_1568_);
    v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v___x_1564_, v_declName_1565_, v_as_1566_, v_sz_boxed_1573_, v_i_boxed_1574_, v_b_1569_, v___y_1570_, v___y_1571_);
    leanh::lean_dec(v___y_1571_);
    leanh::lean_dec_ref(v___y_1570_);
    leanh::lean_dec_ref(v_as_1566_);
    leanh::lean_dec_ref(v___x_1564_);
    return v_res_1575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(
    mut v_a_1576_: *mut leanh::LeanObject,
    mut v_x_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1577_) == 0 {
                    v___x_1578_ = leanh::lean_box(0);
                    return v___x_1578_;
                } else {
                    v_key_1579_ = leanh::lean_ctor_get(v_x_1577_, 0);
                    v_value_1580_ = leanh::lean_ctor_get(v_x_1577_, 1);
                    v_tail_1581_ = leanh::lean_ctor_get(v_x_1577_, 2);
                    v___x_1582_ = lean_name_eq(v_key_1579_, v_a_1576_);
                    if v___x_1582_ == 0 {
                        v_x_1577_ = v_tail_1581_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1580_);
                        v___x_1584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1584_, 0, v_value_1580_);
                        return v___x_1584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg___boxed(
    mut v_a_1585_: *mut leanh::LeanObject,
    mut v_x_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_1585_, v_x_1586_);
    leanh::lean_dec(v_x_1586_);
    leanh::lean_dec(v_a_1585_);
    return v_res_1587_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: u64 = 0;
    v___x_1588_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1589_ = lean_uint64_of_nat(v___x_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(
    mut v_m_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: u64 = 0;
    let mut v___x_1596_: u64 = 0;
    let mut v___x_1597_: u64 = 0;
    let mut v_fold_1598_: u64 = 0;
    let mut v___x_1599_: u64 = 0;
    let mut v___x_1600_: u64 = 0;
    let mut v___x_1601_: u64 = 0;
    let mut v___x_1602_: usize = 0;
    let mut v___x_1603_: usize = 0;
    let mut v___x_1604_: usize = 0;
    let mut v___x_1605_: usize = 0;
    let mut v___x_1606_: usize = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: u64 = 0;
    let mut v_hash_1610_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1592_ = leanh::lean_ctor_get(v_m_1590_, 1);
                v___x_1593_ = lean_array_get_size(v_buckets_1592_);
                if leanh::lean_obj_tag(v_a_1591_) == 0 {
                    v___x_1609_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___closed__0);
                    v___y_1595_ = v___x_1609_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1610_ = leanh::lean_ctor_get_uint64(
                        v_a_1591_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1595_ = v_hash_1610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1596_ = 32u64;
                v___x_1597_ = lean_uint64_shift_right(v___y_1595_, v___x_1596_);
                v_fold_1598_ = lean_uint64_xor(v___y_1595_, v___x_1597_);
                v___x_1599_ = 16u64;
                v___x_1600_ = lean_uint64_shift_right(v_fold_1598_, v___x_1599_);
                v___x_1601_ = lean_uint64_xor(v_fold_1598_, v___x_1600_);
                v___x_1602_ = lean_uint64_to_usize(v___x_1601_);
                v___x_1603_ = lean_usize_of_nat(v___x_1593_);
                v___x_1604_ = 1usize;
                v___x_1605_ = lean_usize_sub(v___x_1603_, v___x_1604_);
                v___x_1606_ = lean_usize_land(v___x_1602_, v___x_1605_);
                v___x_1607_ = lean_array_uget_borrowed(v_buckets_1592_, v___x_1606_);
                v___x_1608_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_1591_, v___x_1607_);
                return v___x_1608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___boxed(
    mut v_m_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_1611_, v_a_1612_);
    leanh::lean_dec(v_a_1612_);
    leanh::lean_dec_ref(v_m_1611_);
    return v_res_1613_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1616_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1;
    v___x_1617_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0;
    v___x_1618_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1617_,
        v___x_1616_,
    );
    return v___x_1618_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(
    mut v_declName_1621_: *mut leanh::LeanObject,
    mut v_isMeta_1622_: u8,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1634_: usize = 0;
    let mut v___x_1635_: usize = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_unused_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: u8 = 0;
    let mut v_toImport_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = lean_st_ref_get(v___y_1624_);
                v_env_1630_ = leanh::lean_ctor_get(v___x_1626_, 0);
                leanh::lean_inc_ref(v_env_1630_);
                leanh::lean_dec(v___x_1626_);
                v___x_1645_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1630_, v_declName_1621_);
                if leanh::lean_obj_tag(v___x_1645_) == 0 {
                    leanh::lean_dec_ref(v_env_1630_);
                    leanh::lean_dec(v_declName_1621_);
                    state = 1;
                    continue;
                } else {
                    v_val_1646_ = leanh::lean_ctor_get(v___x_1645_, 0);
                    leanh::lean_inc(v_val_1646_);
                    leanh::lean_dec_ref_known(v___x_1645_, 1);
                    v___x_1647_ = l_Lean_Environment_header(v_env_1630_);
                    v_modules_1648_ = leanh::lean_ctor_get(v___x_1647_, 3);
                    leanh::lean_inc_ref(v_modules_1648_);
                    leanh::lean_dec_ref(v___x_1647_);
                    v___x_1649_ = lean_array_get_size(v_modules_1648_);
                    v___x_1650_ = lean_nat_dec_lt(v_val_1646_, v___x_1649_);
                    if v___x_1650_ == 0 {
                        leanh::lean_dec_ref(v_modules_1648_);
                        leanh::lean_dec(v_val_1646_);
                        leanh::lean_dec_ref(v_env_1630_);
                        leanh::lean_dec(v_declName_1621_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1651_ = lean_st_ref_get(v___y_1624_);
                        v_env_1652_ = leanh::lean_ctor_get(v___x_1651_, 0);
                        leanh::lean_inc_ref(v_env_1652_);
                        leanh::lean_dec(v___x_1651_);
                        v___x_1653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2);
                        v___x_1654_ = lean_array_fget(v_modules_1648_, v_val_1646_);
                        leanh::lean_dec(v_val_1646_);
                        leanh::lean_dec_ref(v_modules_1648_);
                        if v_isMeta_1622_ == 0 {
                            leanh::lean_dec_ref(v_env_1652_);
                            v___y_1656_ = v_isMeta_1622_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_1621_);
                            v___x_1667_ = l_Lean_isMarkedMeta(v_env_1652_, v_declName_1621_);
                            if v___x_1667_ == 0 {
                                v___y_1656_ = v_isMeta_1622_;
                                state = 5;
                                continue;
                            } else {
                                v___x_1668_ = 0;
                                v___y_1656_ = v___x_1668_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1628_ = leanh::lean_box(0);
                v___x_1629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1629_, 0, v___x_1628_);
                return v___x_1629_;
            }
            2 => {
                v___x_1633_ = leanh::lean_box(0);
                v_sz_1634_ = lean_array_size(v___y_1632_);
                v___x_1635_ = 0usize;
                v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v_env_1630_, v_declName_1621_, v___y_1632_, v_sz_1634_, v___x_1635_, v___x_1633_, v___y_1623_, v___y_1624_);
                leanh::lean_dec_ref(v___y_1632_);
                leanh::lean_dec_ref(v_env_1630_);
                if leanh::lean_obj_tag(v___x_1636_) == 0 {
                    v_isSharedCheck_1643_ = (!leanh::lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v_unused_1644_ = leanh::lean_ctor_get(v___x_1636_, 0);
                        leanh::lean_dec(v_unused_1644_);
                        v___x_1638_ = v___x_1636_;
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1636_);
                        v___x_1638_ = leanh::lean_box(0);
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_1636_;
                }
            }
            3 => {
                if v_isShared_1639_ == 0 {
                    leanh::lean_ctor_set(v___x_1638_, 0, v___x_1633_);
                    v___x_1641_ = v___x_1638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1633_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1641_;
            }
            5 => {
                v_toImport_1657_ = leanh::lean_ctor_get(v___x_1654_, 0);
                leanh::lean_inc_ref(v_toImport_1657_);
                leanh::lean_dec(v___x_1654_);
                v_module_1658_ = leanh::lean_ctor_get(v_toImport_1657_, 0);
                leanh::lean_inc(v_module_1658_);
                leanh::lean_dec_ref(v_toImport_1657_);
                leanh::lean_inc(v_declName_1621_);
                v___x_1659_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_1658_, v___y_1656_, v_declName_1621_, v___y_1623_, v___y_1624_);
                if leanh::lean_obj_tag(v___x_1659_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1659_, 1);
                    v___x_1660_ = l_Lean_indirectModUseExt;
                    v___x_1661_ = leanh::lean_box(1);
                    v___x_1662_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_1630_);
                    v___x_1663_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_1653_,
                        v___x_1660_,
                        v_env_1630_,
                        v___x_1661_,
                        v___x_1662_,
                    );
                    v___x_1664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v___x_1663_, v_declName_1621_);
                    leanh::lean_dec(v___x_1663_);
                    if leanh::lean_obj_tag(v___x_1664_) == 0 {
                        v___x_1665_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3;
                        v___y_1632_ = v___x_1665_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1666_ = leanh::lean_ctor_get(v___x_1664_, 0);
                        leanh::lean_inc(v_val_1666_);
                        leanh::lean_dec_ref_known(v___x_1664_, 1);
                        v___y_1632_ = v_val_1666_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1630_);
                    leanh::lean_dec(v_declName_1621_);
                    return v___x_1659_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___boxed(
    mut v_declName_1669_: *mut leanh::LeanObject,
    mut v_isMeta_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_1674_: u8 = 0;
    let mut v_res_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_1674_ = (leanh::lean_unbox(v_isMeta_1670_) as u8);
    v_res_1675_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_declName_1669_, v_isMeta_boxed_1674_, v___y_1671_, v___y_1672_);
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec_ref(v___y_1671_);
    return v_res_1675_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(
    mut v_a_1676_: *mut leanh::LeanObject,
    mut v_decl_1677_: *mut leanh::LeanObject,
    mut v_stx_1678_: *mut leanh::LeanObject,
    mut v_x_1679_: u8,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut v_a_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1683_ = lean_st_ref_get(v___y_1681_);
                v___x_1684_ =
                    l_Lean_Attribute_Builtin_getIdent(v_stx_1678_, v___y_1680_, v___y_1681_);
                if leanh::lean_obj_tag(v___x_1684_) == 0 {
                    v_a_1685_ = leanh::lean_ctor_get(v___x_1684_, 0);
                    leanh::lean_inc(v_a_1685_);
                    leanh::lean_dec_ref_known(v___x_1684_, 1);
                    v___x_1686_ = leanh::lean_box(0);
                    v___x_1687_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_a_1685_,
                        v___x_1686_,
                        v___y_1680_,
                        v___y_1681_,
                    );
                    if leanh::lean_obj_tag(v___x_1687_) == 0 {
                        v_a_1688_ = leanh::lean_ctor_get(v___x_1687_, 0);
                        leanh::lean_inc_n(v_a_1688_, 2);
                        leanh::lean_dec_ref_known(v___x_1687_, 1);
                        v___x_1689_ = 0;
                        v___x_1690_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_a_1688_, v___x_1689_, v___y_1680_, v___y_1681_);
                        if leanh::lean_obj_tag(v___x_1690_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1690_, 1);
                            v_toEnvExtension_1691_ = leanh::lean_ctor_get(v_a_1676_, 0);
                            v_env_1692_ = leanh::lean_ctor_get(v___x_1683_, 0);
                            leanh::lean_inc_ref(v_env_1692_);
                            leanh::lean_dec(v___x_1683_);
                            v_asyncMode_1693_ =
                                leanh::lean_ctor_get(v_toEnvExtension_1691_, 2);
                            leanh::lean_inc(v_asyncMode_1693_);
                            v___x_1694_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1694_, 0, v_a_1688_);
                            leanh::lean_ctor_set(v___x_1694_, 1, v_decl_1677_);
                            v___x_1695_ = leanh::lean_box(0);
                            v___x_1696_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                                v_a_1676_,
                                v_env_1692_,
                                v___x_1694_,
                                v_asyncMode_1693_,
                                v___x_1695_,
                            );
                            leanh::lean_dec(v_asyncMode_1693_);
                            v___x_1697_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v___x_1696_, v___y_1681_);
                            return v___x_1697_;
                        } else {
                            leanh::lean_dec(v_a_1688_);
                            leanh::lean_dec(v___x_1683_);
                            leanh::lean_dec(v_decl_1677_);
                            leanh::lean_dec_ref(v_a_1676_);
                            return v___x_1690_;
                        }
                    } else {
                        leanh::lean_dec(v___x_1683_);
                        leanh::lean_dec(v_decl_1677_);
                        leanh::lean_dec_ref(v_a_1676_);
                        v_a_1698_ = leanh::lean_ctor_get(v___x_1687_, 0);
                        v_isSharedCheck_1705_ =
                            (!leanh::lean_is_exclusive(v___x_1687_)) as u8;
                        if v_isSharedCheck_1705_ == 0 {
                            v___x_1700_ = v___x_1687_;
                            v_isShared_1701_ = v_isSharedCheck_1705_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1698_);
                            leanh::lean_dec(v___x_1687_);
                            v___x_1700_ = leanh::lean_box(0);
                            v_isShared_1701_ = v_isSharedCheck_1705_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1683_);
                    leanh::lean_dec(v_decl_1677_);
                    leanh::lean_dec_ref(v_a_1676_);
                    v_a_1706_ = leanh::lean_ctor_get(v___x_1684_, 0);
                    v_isSharedCheck_1713_ = (!leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v___x_1708_ = v___x_1684_;
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1706_);
                        leanh::lean_dec(v___x_1684_);
                        v___x_1708_ = leanh::lean_box(0);
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1701_ == 0 {
                    v___x_1703_ = v___x_1700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
                    v___x_1703_ = v_reuseFailAlloc_1704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1703_;
            }
            3 => {
                if v_isShared_1709_ == 0 {
                    v___x_1711_ = v___x_1708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3___boxed(
    mut v_a_1714_: *mut leanh::LeanObject,
    mut v_decl_1715_: *mut leanh::LeanObject,
    mut v_stx_1716_: *mut leanh::LeanObject,
    mut v_x_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5719__boxed_1721_: u8 = 0;
    let mut v_res_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5719__boxed_1721_ = (leanh::lean_unbox(v_x_1717_) as u8);
    v_res_1722_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(
        v_a_1714_,
        v_decl_1715_,
        v_stx_1716_,
        v_x_5719__boxed_1721_,
        v___y_1718_,
        v___y_1719_,
    );
    leanh::lean_dec(v___y_1719_);
    leanh::lean_dec_ref(v___y_1718_);
    return v_res_1722_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(
    mut v_as_1723_: *mut leanh::LeanObject,
    mut v_i_1724_: usize,
    mut v_stop_1725_: usize,
    mut v_b_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: usize = 0;
    let mut v___x_1733_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1727_ = lean_usize_dec_eq(v_i_1724_, v_stop_1725_);
                if v___x_1727_ == 0 {
                    v___x_1728_ = lean_array_uget_borrowed(v_as_1723_, v_i_1724_);
                    v_fst_1729_ = leanh::lean_ctor_get(v___x_1728_, 0);
                    v_snd_1730_ = leanh::lean_ctor_get(v___x_1728_, 1);
                    leanh::lean_inc(v_snd_1730_);
                    leanh::lean_inc(v_fst_1729_);
                    v___x_1731_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1729_, v_snd_1730_, v_b_1726_);
                    v___x_1732_ = 1usize;
                    v___x_1733_ = lean_usize_add(v_i_1724_, v___x_1732_);
                    v_i_1724_ = v___x_1733_;
                    v_b_1726_ = v___x_1731_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2___boxed(
    mut v_as_1735_: *mut leanh::LeanObject,
    mut v_i_1736_: *mut leanh::LeanObject,
    mut v_stop_1737_: *mut leanh::LeanObject,
    mut v_b_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1739_: usize = 0;
    let mut v_stop_boxed_1740_: usize = 0;
    let mut v_res_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1739_ = leanh::lean_unbox_usize(v_i_1736_);
    leanh::lean_dec(v_i_1736_);
    v_stop_boxed_1740_ = leanh::lean_unbox_usize(v_stop_1737_);
    leanh::lean_dec(v_stop_1737_);
    v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v_as_1735_, v_i_boxed_1739_, v_stop_boxed_1740_, v_b_1738_);
    leanh::lean_dec_ref(v_as_1735_);
    return v_res_1741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(
    mut v_as_1742_: *mut leanh::LeanObject,
    mut v_i_1743_: usize,
    mut v_stop_1744_: usize,
    mut v_b_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: u8 = 0;
    let mut v___x_1757_: usize = 0;
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: usize = 0;
    let mut v___x_1761_: usize = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1751_ = lean_usize_dec_eq(v_i_1743_, v_stop_1744_);
                if v___x_1751_ == 0 {
                    v___x_1752_ = lean_array_uget_borrowed(v_as_1742_, v_i_1743_);
                    v___x_1753_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1754_ = lean_array_get_size(v___x_1752_);
                    v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
                    if v___x_1755_ == 0 {
                        v___y_1747_ = v_b_1745_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1756_ = lean_nat_dec_le(v___x_1754_, v___x_1754_);
                        if v___x_1756_ == 0 {
                            if v___x_1755_ == 0 {
                                v___y_1747_ = v_b_1745_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1757_ = 0usize;
                                v___x_1758_ = lean_usize_of_nat(v___x_1754_);
                                v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v___x_1752_, v___x_1757_, v___x_1758_, v_b_1745_);
                                v___y_1747_ = v___x_1759_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1760_ = 0usize;
                            v___x_1761_ = lean_usize_of_nat(v___x_1754_);
                            v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v___x_1752_, v___x_1760_, v___x_1761_, v_b_1745_);
                            v___y_1747_ = v___x_1762_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1745_;
                }
            }
            1 => {
                v___x_1748_ = 1usize;
                v___x_1749_ = lean_usize_add(v_i_1743_, v___x_1748_);
                v_i_1743_ = v___x_1749_;
                v_b_1745_ = v___y_1747_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3___boxed(
    mut v_as_1763_: *mut leanh::LeanObject,
    mut v_i_1764_: *mut leanh::LeanObject,
    mut v_stop_1765_: *mut leanh::LeanObject,
    mut v_b_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1767_: usize = 0;
    let mut v_stop_boxed_1768_: usize = 0;
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1767_ = leanh::lean_unbox_usize(v_i_1764_);
    leanh::lean_dec(v_i_1764_);
    v_stop_boxed_1768_ = leanh::lean_unbox_usize(v_stop_1765_);
    leanh::lean_dec(v_stop_1765_);
    v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_1763_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1766_);
    leanh::lean_dec_ref(v_as_1763_);
    return v_res_1769_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(
    mut v_initState_1770_: *mut leanh::LeanObject,
    mut v_as_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    v___x_1772_ = leanh::lean_unsigned_to_nat(0);
    v___x_1773_ = lean_array_get_size(v_as_1771_);
    v___x_1774_ = lean_nat_dec_lt(v___x_1772_, v___x_1773_);
    if v___x_1774_ == 0 {
        return v_initState_1770_;
    } else {
        let mut v___x_1775_: u8 = 0;
        v___x_1775_ = lean_nat_dec_le(v___x_1773_, v___x_1773_);
        if v___x_1775_ == 0 {
            if v___x_1774_ == 0 {
                return v_initState_1770_;
            } else {
                let mut v___x_1776_: usize = 0;
                let mut v___x_1777_: usize = 0;
                let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1776_ = 0usize;
                v___x_1777_ = lean_usize_of_nat(v___x_1773_);
                v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_1771_, v___x_1776_, v___x_1777_, v_initState_1770_);
                return v___x_1778_;
            }
        } else {
            let mut v___x_1779_: usize = 0;
            let mut v___x_1780_: usize = 0;
            let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1779_ = 0usize;
            v___x_1780_ = lean_usize_of_nat(v___x_1773_);
            v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_1771_, v___x_1779_, v___x_1780_, v_initState_1770_);
            return v___x_1781_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed(
    mut v_initState_1782_: *mut leanh::LeanObject,
    mut v_as_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(v_initState_1782_, v_as_1783_);
    leanh::lean_dec_ref(v_as_1783_);
    return v_res_1784_;
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute(
    mut v_name_1789_: *mut leanh::LeanObject,
    mut v_descr_1790_: *mut leanh::LeanObject,
    mut v_ref_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_unused_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_a_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1793_ = l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0;
                v___f_1794_ = l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1;
                v___x_1795_ = l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2;
                v___x_1796_ = leanh::lean_box(0);
                v___x_1797_ = leanh::lean_box(2);
                leanh::lean_inc(v_ref_1791_);
                v___x_1798_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                leanh::lean_ctor_set(v___x_1798_, 0, v_ref_1791_);
                leanh::lean_ctor_set(v___x_1798_, 1, v___f_1794_);
                leanh::lean_ctor_set(v___x_1798_, 2, v___x_1795_);
                leanh::lean_ctor_set(v___x_1798_, 3, v___f_1793_);
                leanh::lean_ctor_set(v___x_1798_, 4, v___x_1796_);
                leanh::lean_ctor_set(v___x_1798_, 5, v___x_1797_);
                leanh::lean_ctor_set(v___x_1798_, 6, v___x_1796_);
                v___x_1799_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1798_);
                if leanh::lean_obj_tag(v___x_1799_) == 0 {
                    v_a_1800_ = leanh::lean_ctor_get(v___x_1799_, 0);
                    leanh::lean_inc_n(v_a_1800_, 2);
                    leanh::lean_dec_ref_known(v___x_1799_, 1);
                    leanh::lean_inc(v_name_1789_);
                    v___f_1801_ = leanh::lean_alloc_closure(
                        l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___boxed
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1801_, 0, v_name_1789_);
                    v___f_1802_ = leanh::lean_alloc_closure(
                        l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3___boxed
                            as *mut core::ffi::c_void,
                        7,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1802_, 0, v_a_1800_);
                    v___x_1803_ = 0;
                    v___x_1804_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v___x_1804_, 0, v_ref_1791_);
                    leanh::lean_ctor_set(v___x_1804_, 1, v_name_1789_);
                    leanh::lean_ctor_set(v___x_1804_, 2, v_descr_1790_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1804_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_1803_,
                    );
                    v___x_1805_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
                    leanh::lean_ctor_set(v___x_1805_, 1, v___f_1802_);
                    leanh::lean_ctor_set(v___x_1805_, 2, v___f_1801_);
                    leanh::lean_inc_ref(v___x_1805_);
                    v___x_1806_ = l_Lean_registerBuiltinAttribute(v___x_1805_);
                    if leanh::lean_obj_tag(v___x_1806_) == 0 {
                        v_isSharedCheck_1814_ =
                            (!leanh::lean_is_exclusive(v___x_1806_)) as u8;
                        if v_isSharedCheck_1814_ == 0 {
                            v_unused_1815_ = leanh::lean_ctor_get(v___x_1806_, 0);
                            leanh::lean_dec(v_unused_1815_);
                            v___x_1808_ = v___x_1806_;
                            v_isShared_1809_ = v_isSharedCheck_1814_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1806_);
                            v___x_1808_ = leanh::lean_box(0);
                            v_isShared_1809_ = v_isSharedCheck_1814_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_1805_, 3);
                        leanh::lean_dec(v_a_1800_);
                        v_a_1816_ = leanh::lean_ctor_get(v___x_1806_, 0);
                        v_isSharedCheck_1823_ =
                            (!leanh::lean_is_exclusive(v___x_1806_)) as u8;
                        if v_isSharedCheck_1823_ == 0 {
                            v___x_1818_ = v___x_1806_;
                            v_isShared_1819_ = v_isSharedCheck_1823_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1816_);
                            leanh::lean_dec(v___x_1806_);
                            v___x_1818_ = leanh::lean_box(0);
                            v_isShared_1819_ = v_isSharedCheck_1823_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_ref_1791_);
                    leanh::lean_dec_ref(v_descr_1790_);
                    leanh::lean_dec(v_name_1789_);
                    v_a_1824_ = leanh::lean_ctor_get(v___x_1799_, 0);
                    v_isSharedCheck_1831_ = (!leanh::lean_is_exclusive(v___x_1799_)) as u8;
                    if v_isSharedCheck_1831_ == 0 {
                        v___x_1826_ = v___x_1799_;
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1824_);
                        leanh::lean_dec(v___x_1799_);
                        v___x_1826_ = leanh::lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1810_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1810_, 0, v___x_1805_);
                leanh::lean_ctor_set(v___x_1810_, 1, v_a_1800_);
                if v_isShared_1809_ == 0 {
                    leanh::lean_ctor_set(v___x_1808_, 0, v___x_1810_);
                    v___x_1812_ = v___x_1808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1812_;
            }
            3 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1821_;
            }
            5 => {
                if v_isShared_1827_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_registerCombinatorAttribute___boxed(
    mut v_name_1832_: *mut leanh::LeanObject,
    mut v_descr_1833_: *mut leanh::LeanObject,
    mut v_ref_1834_: *mut leanh::LeanObject,
    mut v_a_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1836_ =
        l_Lean_ParserCompiler_registerCombinatorAttribute(v_name_1832_, v_descr_1833_, v_ref_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(
    mut v_00_u03b1_1837_: *mut leanh::LeanObject,
    mut v_msg_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ =
        l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(
            v_msg_1838_,
            v___y_1839_,
            v___y_1840_,
        );
    return v___x_1842_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___boxed(
    mut v_00_u03b1_1843_: *mut leanh::LeanObject,
    mut v_msg_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ =
        l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(
            v_00_u03b1_1843_,
            v_msg_1844_,
            v___y_1845_,
            v___y_1846_,
        );
    leanh::lean_dec(v___y_1846_);
    leanh::lean_dec_ref(v___y_1845_);
    return v_res_1848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(
    mut v_00_u03b2_1849_: *mut leanh::LeanObject,
    mut v_m_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_1850_, v_a_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___boxed(
    mut v_00_u03b2_1853_: *mut leanh::LeanObject,
    mut v_m_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(v_00_u03b2_1853_, v_m_1854_, v_a_1855_);
    leanh::lean_dec(v_a_1855_);
    leanh::lean_dec_ref(v_m_1854_);
    return v_res_1856_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(
    mut v_00_u03b2_1857_: *mut leanh::LeanObject,
    mut v_x_1858_: *mut leanh::LeanObject,
    mut v_x_1859_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1860_: u8 = 0;
    v___x_1860_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_1858_, v_x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b2_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
    mut v_x_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1864_: u8 = 0;
    let mut v_r_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(v_00_u03b2_1861_, v_x_1862_, v_x_1863_);
    leanh::lean_dec_ref(v_x_1863_);
    leanh::lean_dec_ref(v_x_1862_);
    v_r_1865_ = leanh::lean_box((v_res_1864_) as usize);
    return v_r_1865_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(
    mut v_00_u03b2_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_x_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_1867_, v_x_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___boxed(
    mut v_00_u03b2_1870_: *mut leanh::LeanObject,
    mut v_a_1871_: *mut leanh::LeanObject,
    mut v_x_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(v_00_u03b2_1870_, v_a_1871_, v_x_1872_);
    leanh::lean_dec(v_x_1872_);
    leanh::lean_dec(v_a_1871_);
    return v_res_1873_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(
    mut v_00_u03b2_1874_: *mut leanh::LeanObject,
    mut v_x_1875_: *mut leanh::LeanObject,
    mut v_x_1876_: usize,
    mut v_x_1877_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1878_: u8 = 0;
    v___x_1878_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_1875_, v_x_1876_, v_x_1877_);
    return v___x_1878_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___boxed(
    mut v_00_u03b2_1879_: *mut leanh::LeanObject,
    mut v_x_1880_: *mut leanh::LeanObject,
    mut v_x_1881_: *mut leanh::LeanObject,
    mut v_x_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5977__boxed_1883_: usize = 0;
    let mut v_res_1884_: u8 = 0;
    let mut v_r_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5977__boxed_1883_ = leanh::lean_unbox_usize(v_x_1881_);
    leanh::lean_dec(v_x_1881_);
    v_res_1884_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(v_00_u03b2_1879_, v_x_1880_, v_x_5977__boxed_1883_, v_x_1882_);
    leanh::lean_dec_ref(v_x_1882_);
    leanh::lean_dec_ref(v_x_1880_);
    v_r_1885_ = leanh::lean_box((v_res_1884_) as usize);
    return v_r_1885_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(
    mut v_00_u03b2_1886_: *mut leanh::LeanObject,
    mut v_keys_1887_: *mut leanh::LeanObject,
    mut v_vals_1888_: *mut leanh::LeanObject,
    mut v_heq_1889_: *mut leanh::LeanObject,
    mut v_i_1890_: *mut leanh::LeanObject,
    mut v_k_1891_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1892_: u8 = 0;
    v___x_1892_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_1887_, v_i_1890_, v_k_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___boxed(
    mut v_00_u03b2_1893_: *mut leanh::LeanObject,
    mut v_keys_1894_: *mut leanh::LeanObject,
    mut v_vals_1895_: *mut leanh::LeanObject,
    mut v_heq_1896_: *mut leanh::LeanObject,
    mut v_i_1897_: *mut leanh::LeanObject,
    mut v_k_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: u8 = 0;
    let mut v_r_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(v_00_u03b2_1893_, v_keys_1894_, v_vals_1895_, v_heq_1896_, v_i_1897_, v_k_1898_);
    leanh::lean_dec_ref(v_k_1898_);
    leanh::lean_dec_ref(v_vals_1895_);
    leanh::lean_dec_ref(v_keys_1894_);
    v_r_1900_ = leanh::lean_box((v_res_1899_) as usize);
    return v_r_1900_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(
    mut v_attr_1901_: *mut leanh::LeanObject,
    mut v_env_1902_: *mut leanh::LeanObject,
    mut v_parserDecl_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ext_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ext_1904_ = leanh::lean_ctor_get(v_attr_1901_, 1);
    v_toEnvExtension_1905_ = leanh::lean_ctor_get(v_ext_1904_, 0);
    v_asyncMode_1906_ = leanh::lean_ctor_get(v_toEnvExtension_1905_, 2);
    v___x_1907_ = leanh::lean_box(1);
    v___x_1908_ = leanh::lean_box(0);
    v___x_1909_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1907_,
        v_ext_1904_,
        v_env_1902_,
        v_asyncMode_1906_,
        v___x_1908_,
    );
    v___x_1910_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1909_,
            v_parserDecl_1903_,
        );
    leanh::lean_dec(v___x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f___boxed(
    mut v_attr_1911_: *mut leanh::LeanObject,
    mut v_env_1912_: *mut leanh::LeanObject,
    mut v_parserDecl_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(
        v_attr_1911_,
        v_env_1912_,
        v_parserDecl_1913_,
    );
    leanh::lean_dec(v_parserDecl_1913_);
    leanh::lean_dec_ref(v_attr_1911_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(
    mut v_attr_1915_: *mut leanh::LeanObject,
    mut v_env_1916_: *mut leanh::LeanObject,
    mut v_parserDecl_1917_: *mut leanh::LeanObject,
    mut v_decl_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ext_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_toEnvExtension_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_unused_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ext_1919_ = leanh::lean_ctor_get(v_attr_1915_, 1);
                v_isSharedCheck_1930_ = (!leanh::lean_is_exclusive(v_attr_1915_)) as u8;
                if v_isSharedCheck_1930_ == 0 {
                    v_unused_1931_ = leanh::lean_ctor_get(v_attr_1915_, 0);
                    leanh::lean_dec(v_unused_1931_);
                    v___x_1921_ = v_attr_1915_;
                    v_isShared_1922_ = v_isSharedCheck_1930_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ext_1919_);
                    leanh::lean_dec(v_attr_1915_);
                    v___x_1921_ = leanh::lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEnvExtension_1923_ = leanh::lean_ctor_get(v_ext_1919_, 0);
                v_asyncMode_1924_ = leanh::lean_ctor_get(v_toEnvExtension_1923_, 2);
                leanh::lean_inc(v_asyncMode_1924_);
                if v_isShared_1922_ == 0 {
                    leanh::lean_ctor_set(v___x_1921_, 1, v_decl_1918_);
                    leanh::lean_ctor_set(v___x_1921_, 0, v_parserDecl_1917_);
                    v___x_1926_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_parserDecl_1917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_decl_1918_);
                    v___x_1926_ = v_reuseFailAlloc_1929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1927_ = leanh::lean_box(0);
                v___x_1928_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_1919_,
                    v_env_1916_,
                    v___x_1926_,
                    v_asyncMode_1924_,
                    v___x_1927_,
                );
                leanh::lean_dec(v_asyncMode_1924_);
                return v___x_1928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(
    mut v_x_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1932_) == 0 {
                    v_a_1936_ = leanh::lean_ctor_get(v_x_1932_, 0);
                    leanh::lean_inc(v_a_1936_);
                    leanh::lean_dec_ref_known(v_x_1932_, 1);
                    v___x_1937_ = l_Lean_stringToMessageData(v_a_1936_);
                    v___x_1938_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_1937_, v___y_1933_, v___y_1934_);
                    return v___x_1938_;
                } else {
                    v_a_1939_ = leanh::lean_ctor_get(v_x_1932_, 0);
                    v_isSharedCheck_1946_ = (!leanh::lean_is_exclusive(v_x_1932_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1941_ = v_x_1932_;
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1939_);
                        leanh::lean_dec(v_x_1932_);
                        v___x_1941_ = leanh::lean_box(0);
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1942_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1941_, 0);
                    v___x_1944_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg___boxed(
    mut v_x_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_1947_, v___y_1948_, v___y_1949_);
    leanh::lean_dec(v___y_1949_);
    leanh::lean_dec_ref(v___y_1948_);
    return v_res_1951_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = leanh::lean_box(0);
    v___x_1953_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1954_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1954_, 0, v___x_1953_);
    leanh::lean_ctor_set(v___x_1954_, 1, v___x_1952_);
    return v___x_1954_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0);
    v___x_1957_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1957_, 0, v___x_1956_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___boxed(
    mut v___y_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
    return v_res_1959_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(
    mut v_constName_1960_: *mut leanh::LeanObject,
    mut v_checkMeta_1961_: u8,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1965_ = lean_st_ref_get(v___y_1963_);
                v_env_1966_ = leanh::lean_ctor_get(v___x_1965_, 0);
                leanh::lean_inc_ref(v_env_1966_);
                leanh::lean_dec(v___x_1965_);
                leanh::lean_inc(v_constName_1960_);
                v___x_1967_ = lean_has_compile_error(v_env_1966_, v_constName_1960_);
                if v___x_1967_ == 0 {
                    v___x_1968_ = lean_st_ref_get(v___y_1963_);
                    v_env_1969_ = leanh::lean_ctor_get(v___x_1968_, 0);
                    leanh::lean_inc_ref(v_env_1969_);
                    leanh::lean_dec(v___x_1968_);
                    v_options_1970_ = leanh::lean_ctor_get(v___y_1962_, 2);
                    v___x_1971_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1969_,
                        v_options_1970_,
                        v_constName_1960_,
                        v_checkMeta_1961_,
                    );
                    leanh::lean_dec(v_constName_1960_);
                    leanh::lean_dec_ref(v_env_1969_);
                    v___x_1972_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_1971_, v___y_1962_, v___y_1963_);
                    return v___x_1972_;
                } else {
                    v___x_1973_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
                    if leanh::lean_obj_tag(v___x_1973_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1973_, 1);
                        v___x_1974_ = lean_st_ref_get(v___y_1963_);
                        v_env_1975_ = leanh::lean_ctor_get(v___x_1974_, 0);
                        leanh::lean_inc_ref(v_env_1975_);
                        leanh::lean_dec(v___x_1974_);
                        v_options_1976_ = leanh::lean_ctor_get(v___y_1962_, 2);
                        v___x_1977_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1975_,
                            v_options_1976_,
                            v_constName_1960_,
                            v_checkMeta_1961_,
                        );
                        leanh::lean_dec(v_constName_1960_);
                        leanh::lean_dec_ref(v_env_1975_);
                        v___x_1978_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_1977_, v___y_1962_, v___y_1963_);
                        return v___x_1978_;
                    } else {
                        leanh::lean_dec(v_constName_1960_);
                        v_a_1979_ = leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1986_ =
                            (!leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1986_ == 0 {
                            v___x_1981_ = v___x_1973_;
                            v_isShared_1982_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1979_);
                            leanh::lean_dec(v___x_1973_);
                            v___x_1981_ = leanh::lean_box(0);
                            v_isShared_1982_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1982_ == 0 {
                    v___x_1984_ = v___x_1981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
                    v___x_1984_ = v_reuseFailAlloc_1985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg___boxed(
    mut v_constName_1987_: *mut leanh::LeanObject,
    mut v_checkMeta_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1992_: u8 = 0;
    let mut v_res_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1992_ = (leanh::lean_unbox(v_checkMeta_1988_) as u8);
    v_res_1993_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_1987_, v_checkMeta_boxed_1992_, v___y_1989_, v___y_1990_);
    leanh::lean_dec(v___y_1990_);
    leanh::lean_dec_ref(v___y_1989_);
    return v_res_1993_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0;
    v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
    return v___x_1996_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2;
    v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
    return v___x_1999_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4;
    v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
    mut v_attr_2003_: *mut leanh::LeanObject,
    mut v_parserDecl_2004_: *mut leanh::LeanObject,
    mut v_a_2005_: *mut leanh::LeanObject,
    mut v_a_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v_toAttributeImplCore_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut v_unused_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_st_ref_get(v_a_2006_);
                v_env_2009_ = leanh::lean_ctor_get(v___x_2008_, 0);
                leanh::lean_inc_ref(v_env_2009_);
                leanh::lean_dec(v___x_2008_);
                v___x_2010_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(
                    v_attr_2003_,
                    v_env_2009_,
                    v_parserDecl_2004_,
                );
                if leanh::lean_obj_tag(v___x_2010_) == 1 {
                    leanh::lean_dec(v_parserDecl_2004_);
                    leanh::lean_dec_ref(v_attr_2003_);
                    v_val_2011_ = leanh::lean_ctor_get(v___x_2010_, 0);
                    leanh::lean_inc(v_val_2011_);
                    leanh::lean_dec_ref_known(v___x_2010_, 1);
                    v___x_2012_ = 1;
                    v___x_2013_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_val_2011_, v___x_2012_, v_a_2005_, v_a_2006_);
                    return v___x_2013_;
                } else {
                    leanh::lean_dec(v___x_2010_);
                    v_impl_2014_ = leanh::lean_ctor_get(v_attr_2003_, 0);
                    v_isSharedCheck_2032_ = (!leanh::lean_is_exclusive(v_attr_2003_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v_unused_2033_ = leanh::lean_ctor_get(v_attr_2003_, 1);
                        leanh::lean_dec(v_unused_2033_);
                        v___x_2016_ = v_attr_2003_;
                        v_isShared_2017_ = v_isSharedCheck_2032_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_impl_2014_);
                        leanh::lean_dec(v_attr_2003_);
                        v___x_2016_ = leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2032_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toAttributeImplCore_2018_ = leanh::lean_ctor_get(v_impl_2014_, 0);
                leanh::lean_inc_ref(v_toAttributeImplCore_2018_);
                leanh::lean_dec_ref(v_impl_2014_);
                v_name_2019_ = leanh::lean_ctor_get(v_toAttributeImplCore_2018_, 1);
                leanh::lean_inc(v_name_2019_);
                leanh::lean_dec_ref(v_toAttributeImplCore_2018_);
                v___x_2020_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1_once), _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1);
                v___x_2021_ = l_Lean_MessageData_ofName(v_name_2019_);
                if v_isShared_2017_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2016_, 7);
                    leanh::lean_ctor_set(v___x_2016_, 1, v___x_2021_);
                    leanh::lean_ctor_set(v___x_2016_, 0, v___x_2020_);
                    v___x_2023_ = v___x_2016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2021_);
                    v___x_2023_ = v_reuseFailAlloc_2031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3_once), _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3);
                v___x_2025_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2025_, 0, v___x_2023_);
                leanh::lean_ctor_set(v___x_2025_, 1, v___x_2024_);
                v___x_2026_ = l_Lean_MessageData_ofName(v_parserDecl_2004_);
                v___x_2027_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2027_, 0, v___x_2025_);
                leanh::lean_ctor_set(v___x_2027_, 1, v___x_2026_);
                v___x_2028_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5_once), _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5);
                v___x_2029_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2029_, 0, v___x_2027_);
                leanh::lean_ctor_set(v___x_2029_, 1, v___x_2028_);
                v___x_2030_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_2029_, v_a_2005_, v_a_2006_);
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___boxed(
    mut v_attr_2034_: *mut leanh::LeanObject,
    mut v_parserDecl_2035_: *mut leanh::LeanObject,
    mut v_a_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
    mut v_a_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
        v_attr_2034_,
        v_parserDecl_2035_,
        v_a_2036_,
        v_a_2037_,
    );
    leanh::lean_dec(v_a_2037_);
    leanh::lean_dec_ref(v_a_2036_);
    return v_res_2039_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(
    mut v_00_u03b1_2040_: *mut leanh::LeanObject,
    mut v_attr_2041_: *mut leanh::LeanObject,
    mut v_parserDecl_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
        v_attr_2041_,
        v_parserDecl_2042_,
        v_a_2043_,
        v_a_2044_,
    );
    return v___x_2046_;
}
pub unsafe fn l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___boxed(
    mut v_00_u03b1_2047_: *mut leanh::LeanObject,
    mut v_attr_2048_: *mut leanh::LeanObject,
    mut v_parserDecl_2049_: *mut leanh::LeanObject,
    mut v_a_2050_: *mut leanh::LeanObject,
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(
        v_00_u03b1_2047_,
        v_attr_2048_,
        v_parserDecl_2049_,
        v_a_2050_,
        v_a_2051_,
    );
    leanh::lean_dec(v_a_2051_);
    leanh::lean_dec_ref(v_a_2050_);
    return v_res_2053_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(
    mut v_00_u03b1_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
    return v___x_2058_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___boxed(
    mut v_00_u03b1_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(v_00_u03b1_2059_, v___y_2060_, v___y_2061_);
    leanh::lean_dec(v___y_2061_);
    leanh::lean_dec_ref(v___y_2060_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(
    mut v_00_u03b1_2064_: *mut leanh::LeanObject,
    mut v_constName_2065_: *mut leanh::LeanObject,
    mut v_checkMeta_2066_: u8,
    mut v___y_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2070_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_2065_, v_checkMeta_2066_, v___y_2067_, v___y_2068_);
    return v___x_2070_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___boxed(
    mut v_00_u03b1_2071_: *mut leanh::LeanObject,
    mut v_constName_2072_: *mut leanh::LeanObject,
    mut v_checkMeta_2073_: *mut leanh::LeanObject,
    mut v___y_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2077_: u8 = 0;
    let mut v_res_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2077_ = (leanh::lean_unbox(v_checkMeta_2073_) as u8);
    v_res_2078_ =
        l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(
            v_00_u03b1_2071_,
            v_constName_2072_,
            v_checkMeta_boxed_2077_,
            v___y_2074_,
            v___y_2075_,
        );
    leanh::lean_dec(v___y_2075_);
    leanh::lean_dec_ref(v___y_2074_);
    return v_res_2078_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(
    mut v_00_u03b1_2079_: *mut leanh::LeanObject,
    mut v_x_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_2080_, v___y_2081_, v___y_2082_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___boxed(
    mut v_00_u03b1_2085_: *mut leanh::LeanObject,
    mut v_x_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(v_00_u03b1_2085_, v_x_2086_, v___y_2087_, v___y_2088_);
    leanh::lean_dec(v___y_2088_);
    leanh::lean_dec_ref(v___y_2087_);
    return v_res_2090_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ParserCompiler_Attribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default =
        _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default();
    leanh::lean_mark_persistent(
        l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default,
    );
    l_Lean_ParserCompiler_instInhabitedCombinatorAttribute =
        _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute();
    leanh::lean_mark_persistent(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ParserCompiler_Attribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1 =
        _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1();
    leanh::lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ParserCompiler_Attribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ParserCompiler_Attribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ParserCompiler_Attribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ParserCompiler_Attribute(builtin);
}