// Lean compiler output
// Module: Lean.Elab.DeprecatedArg
// Imports: Lean.EnvExtension Lean.Message Lean.Elab.Term
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_string_utf8_byte_size, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getId, l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_Expr_fvarId_x21;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData, runtime_initialize_Lean_Message,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getDecl___redArg,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13546154976408593379 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1968078384074148898 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<76> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 97, 110, 100, 32, 101, 114, 114, 111, 114, 115, 32, 102, 111, 114, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6273911876863363489 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12134614065342578556 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15915760593312485737 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_linter_deprecated_arg: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 114, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7421364113271725538 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_deprecatedArgExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 96, 0],
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [96, 32, 111, 102, 32, 96, 0],
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
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
        96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 0,
    ],
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value: crate::leanh::LeanStringObject<
    29,
> = crate::leanh::LeanStringObject {
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
        96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 44, 32, 117, 115, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [96, 32, 105, 110, 115, 116, 101, 97, 100, 0],
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<138> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 138, m_capacity: 138, m_length: 137, m_data: [96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 104, 111, 117, 108, 100, 32, 115, 112, 101, 99, 105, 102, 121, 32, 116, 104, 101, 32, 100, 97, 116, 101, 32, 111, 114, 32, 108, 105, 98, 114, 97, 114, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 97, 116, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 115, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 100, 44, 32, 117, 115, 105, 110, 103, 32, 96, 40, 115, 105, 110, 99, 101, 32, 58, 61, 32, 34, 46, 46, 46, 34, 41, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 59, 32, 114, 101, 110, 97, 109, 101, 32, 105, 116, 32, 116, 111, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [96, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 96, 64, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [96, 59, 32, 114, 101, 109, 111, 118, 101, 32, 105, 116, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 96, 64, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11531124740603029721 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8394106201925823804 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7342416184850389469 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6378049578484137067 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17236566213953443098 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4850288449286909715 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13121995851907617918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5210797880492880268 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7133939494800887925 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<6> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 6, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12512396870021461549 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [109, 97, 114, 107, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 97, 115, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(
    mut v_name_1407_: *mut crate::leanh::LeanObject,
    mut v_decl_1408_: *mut crate::leanh::LeanObject,
    mut v_ref_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut v_unused_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1411_ = crate::leanh::lean_ctor_get(v_decl_1408_, 0);
                v_descr_1412_ = crate::leanh::lean_ctor_get(v_decl_1408_, 1);
                v_deprecation_x3f_1413_ = crate::leanh::lean_ctor_get(v_decl_1408_, 2);
                v___x_1414_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1415_ = (crate::leanh::lean_unbox(v_defValue_1411_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_1414_, 0 as u32, v___x_1415_);
                crate::leanh::lean_inc(v_deprecation_x3f_1413_);
                crate::leanh::lean_inc_ref(v_descr_1412_);
                crate::leanh::lean_inc_n(v_name_1407_, 2);
                v___x_1416_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1416_, 0, v_name_1407_);
                crate::leanh::lean_ctor_set(v___x_1416_, 1, v_ref_1409_);
                crate::leanh::lean_ctor_set(v___x_1416_, 2, v___x_1414_);
                crate::leanh::lean_ctor_set(v___x_1416_, 3, v_descr_1412_);
                crate::leanh::lean_ctor_set(v___x_1416_, 4, v_deprecation_x3f_1413_);
                v___x_1417_ = lean_register_option(v_name_1407_, v___x_1416_);
                if crate::leanh::lean_obj_tag(v___x_1417_) == 0 {
                    v_isSharedCheck_1425_ = (!crate::leanh::lean_is_exclusive(v___x_1417_)) as u8;
                    if v_isSharedCheck_1425_ == 0 {
                        v_unused_1426_ = crate::leanh::lean_ctor_get(v___x_1417_, 0);
                        crate::leanh::lean_dec(v_unused_1426_);
                        v___x_1419_ = v___x_1417_;
                        v_isShared_1420_ = v_isSharedCheck_1425_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1417_);
                        v___x_1419_ = crate::leanh::lean_box(0);
                        v_isShared_1420_ = v_isSharedCheck_1425_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1407_);
                    v_a_1427_ = crate::leanh::lean_ctor_get(v___x_1417_, 0);
                    v_isSharedCheck_1434_ = (!crate::leanh::lean_is_exclusive(v___x_1417_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1429_ = v___x_1417_;
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1427_);
                        crate::leanh::lean_dec(v___x_1417_);
                        v___x_1429_ = crate::leanh::lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_1411_);
                v___x_1421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1421_, 0, v_name_1407_);
                crate::leanh::lean_ctor_set(v___x_1421_, 1, v_defValue_1411_);
                if v_isShared_1420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1419_, 0, v___x_1421_);
                    v___x_1423_ = v___x_1419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
                    v___x_1423_ = v_reuseFailAlloc_1424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1423_;
            }
            3 => {
                if v_isShared_1430_ == 0 {
                    v___x_1432_ = v___x_1429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1435_: *mut crate::leanh::LeanObject,
    mut v_decl_1436_: *mut crate::leanh::LeanObject,
    mut v_ref_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v_name_1435_, v_decl_1436_, v_ref_1437_);
    crate::leanh::lean_dec_ref(v_decl_1436_);
    return v_res_1439_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1463_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1464_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1465_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v___x_1462_, v___x_1463_, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(
    mut v_a_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
    return v_res_1467_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(
    mut v_s_1473_: *mut crate::leanh::LeanObject,
    mut v_e_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldArg_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_1475_ = crate::leanh::lean_ctor_get(v_e_1474_, 0);
                crate::leanh::lean_inc(v_declName_1475_);
                v_oldArg_1476_ = crate::leanh::lean_ctor_get(v_e_1474_, 1);
                crate::leanh::lean_inc(v_oldArg_1476_);
                v___x_1481_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1473_, v_declName_1475_);
                if crate::leanh::lean_obj_tag(v___x_1481_) == 0 {
                    v___x_1482_ = crate::leanh::lean_box(1);
                    v___y_1478_ = v___x_1482_;
                    state = 1;
                    continue;
                } else {
                    v_val_1483_ = crate::leanh::lean_ctor_get(v___x_1481_, 0);
                    crate::leanh::lean_inc(v_val_1483_);
                    crate::leanh::lean_dec_ref_known(v___x_1481_, 1);
                    v___y_1478_ = v_val_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inner_1479_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_oldArg_1476_, v_e_1474_, v___y_1478_);
                v___x_1480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_1475_, v_inner_1479_, v_s_1473_);
                return v___x_1480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(
    mut v_es_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = lean_array_mk(v_es_1484_);
    return v___x_1485_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_1486_: *mut crate::leanh::LeanObject,
    mut v_i_1487_: usize,
    mut v_stop_1488_: usize,
    mut v_b_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1490_ = lean_usize_dec_eq(v_i_1487_, v_stop_1488_);
                if v___x_1490_ == 0 {
                    v___x_1491_ = lean_array_uget_borrowed(v_as_1486_, v_i_1487_);
                    crate::leanh::lean_inc(v___x_1491_);
                    v___x_1492_ =
                        l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(
                            v_b_1489_,
                            v___x_1491_,
                        );
                    v___x_1493_ = 1usize;
                    v___x_1494_ = lean_usize_add(v_i_1487_, v___x_1493_);
                    v_i_1487_ = v___x_1494_;
                    v_b_1489_ = v___x_1492_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1489_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_1496_: *mut crate::leanh::LeanObject,
    mut v_i_1497_: *mut crate::leanh::LeanObject,
    mut v_stop_1498_: *mut crate::leanh::LeanObject,
    mut v_b_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1500_: usize = 0;
    let mut v_stop_boxed_1501_: usize = 0;
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1500_ = crate::leanh::lean_unbox_usize(v_i_1497_);
    crate::leanh::lean_dec(v_i_1497_);
    v_stop_boxed_1501_ = crate::leanh::lean_unbox_usize(v_stop_1498_);
    crate::leanh::lean_dec(v_stop_1498_);
    v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v_as_1496_, v_i_boxed_1500_, v_stop_boxed_1501_, v_b_1499_);
    crate::leanh::lean_dec_ref(v_as_1496_);
    return v_res_1502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_1503_: *mut crate::leanh::LeanObject,
    mut v_i_1504_: usize,
    mut v_stop_1505_: usize,
    mut v_b_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: usize = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1512_ = lean_usize_dec_eq(v_i_1504_, v_stop_1505_);
                if v___x_1512_ == 0 {
                    v___x_1513_ = lean_array_uget_borrowed(v_as_1503_, v_i_1504_);
                    v___x_1514_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1515_ = lean_array_get_size(v___x_1513_);
                    v___x_1516_ = lean_nat_dec_lt(v___x_1514_, v___x_1515_);
                    if v___x_1516_ == 0 {
                        v___y_1508_ = v_b_1506_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1517_ = lean_nat_dec_le(v___x_1515_, v___x_1515_);
                        if v___x_1517_ == 0 {
                            if v___x_1516_ == 0 {
                                v___y_1508_ = v_b_1506_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1518_ = 0usize;
                                v___x_1519_ = lean_usize_of_nat(v___x_1515_);
                                v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_1513_, v___x_1518_, v___x_1519_, v_b_1506_);
                                v___y_1508_ = v___x_1520_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1521_ = 0usize;
                            v___x_1522_ = lean_usize_of_nat(v___x_1515_);
                            v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_1513_, v___x_1521_, v___x_1522_, v_b_1506_);
                            v___y_1508_ = v___x_1523_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1506_;
                }
            }
            1 => {
                v___x_1509_ = 1usize;
                v___x_1510_ = lean_usize_add(v_i_1504_, v___x_1509_);
                v_i_1504_ = v___x_1510_;
                v_b_1506_ = v___y_1508_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_1524_: *mut crate::leanh::LeanObject,
    mut v_i_1525_: *mut crate::leanh::LeanObject,
    mut v_stop_1526_: *mut crate::leanh::LeanObject,
    mut v_b_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1528_: usize = 0;
    let mut v_stop_boxed_1529_: usize = 0;
    let mut v_res_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1528_ = crate::leanh::lean_unbox_usize(v_i_1525_);
    crate::leanh::lean_dec(v_i_1525_);
    v_stop_boxed_1529_ = crate::leanh::lean_unbox_usize(v_stop_1526_);
    crate::leanh::lean_dec(v_stop_1526_);
    v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1524_, v_i_boxed_1528_, v_stop_boxed_1529_, v_b_1527_);
    crate::leanh::lean_dec_ref(v_as_1524_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(
    mut v_initState_1531_: *mut crate::leanh::LeanObject,
    mut v_as_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    v___x_1533_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1534_ = lean_array_get_size(v_as_1532_);
    v___x_1535_ = lean_nat_dec_lt(v___x_1533_, v___x_1534_);
    if v___x_1535_ == 0 {
        return v_initState_1531_;
    } else {
        let mut v___x_1536_: u8 = 0;
        v___x_1536_ = lean_nat_dec_le(v___x_1534_, v___x_1534_);
        if v___x_1536_ == 0 {
            if v___x_1535_ == 0 {
                return v_initState_1531_;
            } else {
                let mut v___x_1537_: usize = 0;
                let mut v___x_1538_: usize = 0;
                let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1537_ = 0usize;
                v___x_1538_ = lean_usize_of_nat(v___x_1534_);
                v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1532_, v___x_1537_, v___x_1538_, v_initState_1531_);
                return v___x_1539_;
            }
        } else {
            let mut v___x_1540_: usize = 0;
            let mut v___x_1541_: usize = 0;
            let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1540_ = 0usize;
            v___x_1541_ = lean_usize_of_nat(v___x_1534_);
            v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1532_, v___x_1540_, v___x_1541_, v_initState_1531_);
            return v___x_1542_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_1543_: *mut crate::leanh::LeanObject,
    mut v_as_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_1543_, v_as_1544_);
    crate::leanh::lean_dec_ref(v_as_1544_);
    return v_res_1545_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_;
    v___x_1564_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1563_);
    return v___x_1564_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(
    mut v_a_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
    return v_res_1566_;
}
pub unsafe fn l_Lean_Elab_findDeprecatedArg_x3f(
    mut v_env_1567_: *mut crate::leanh::LeanObject,
    mut v_declName_1568_: *mut crate::leanh::LeanObject,
    mut v_argName_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_Elab_deprecatedArgExt;
    v_toEnvExtension_1571_ = crate::leanh::lean_ctor_get(v___x_1570_, 0);
    v_asyncMode_1572_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1571_, 2);
    v___x_1573_ = crate::leanh::lean_box(1);
    v___x_1574_ = crate::leanh::lean_box(0);
    v___x_1575_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1573_,
        v___x_1570_,
        v_env_1567_,
        v_asyncMode_1572_,
        v___x_1574_,
    );
    v___x_1576_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1575_,
            v_declName_1568_,
        );
    crate::leanh::lean_dec(v___x_1575_);
    if crate::leanh::lean_obj_tag(v___x_1576_) == 0 {
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1577_ = crate::leanh::lean_box(0);
        return v___x_1577_;
    } else {
        let mut v_val_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1578_ = crate::leanh::lean_ctor_get(v___x_1576_, 0);
        crate::leanh::lean_inc(v_val_1578_);
        crate::leanh::lean_dec_ref_known(v___x_1576_, 1);
        v___x_1579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_1578_, v_argName_1569_);
        crate::leanh::lean_dec(v_val_1578_);
        return v___x_1579_;
    }
}
pub unsafe fn l_Lean_Elab_findDeprecatedArg_x3f___boxed(
    mut v_env_1580_: *mut crate::leanh::LeanObject,
    mut v_declName_1581_: *mut crate::leanh::LeanObject,
    mut v_argName_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1583_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_1580_, v_declName_1581_, v_argName_1582_);
    crate::leanh::lean_dec(v_argName_1582_);
    crate::leanh::lean_dec(v_declName_1581_);
    return v_res_1583_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__0;
    v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__2;
    v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
    return v___x_1589_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__4;
    v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
    return v___x_1592_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__6;
    v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__8;
    v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__10;
    v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Lean_Elab_formatDeprecatedArgMsg(
    mut v_entry_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldArg_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArg_x3f_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_1603_ = crate::leanh::lean_ctor_get(v_entry_1602_, 0);
                crate::leanh::lean_inc(v_declName_1603_);
                v_oldArg_1604_ = crate::leanh::lean_ctor_get(v_entry_1602_, 1);
                crate::leanh::lean_inc(v_oldArg_1604_);
                v_newArg_x3f_1605_ = crate::leanh::lean_ctor_get(v_entry_1602_, 2);
                crate::leanh::lean_inc(v_newArg_x3f_1605_);
                v_text_x3f_1606_ = crate::leanh::lean_ctor_get(v_entry_1602_, 3);
                crate::leanh::lean_inc(v_text_x3f_1606_);
                crate::leanh::lean_dec_ref(v_entry_1602_);
                if crate::leanh::lean_obj_tag(v_newArg_x3f_1605_) == 0 {
                    v___x_1614_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3,
                    );
                    v___x_1615_ = l_Lean_MessageData_ofName(v_oldArg_1604_);
                    v___x_1616_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1616_, 0, v___x_1614_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 1, v___x_1615_);
                    v___x_1617_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5,
                    );
                    v___x_1618_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    crate::leanh::lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    v___x_1619_ = 0;
                    v___x_1620_ = l_Lean_MessageData_ofConstName(v_declName_1603_, v___x_1619_);
                    v___x_1621_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1621_, 0, v___x_1618_);
                    crate::leanh::lean_ctor_set(v___x_1621_, 1, v___x_1620_);
                    v___x_1622_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7,
                    );
                    v___x_1623_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1623_, 0, v___x_1621_);
                    crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                    v___y_1608_ = v___x_1623_;
                    state = 1;
                    continue;
                } else {
                    v_val_1624_ = crate::leanh::lean_ctor_get(v_newArg_x3f_1605_, 0);
                    crate::leanh::lean_inc(v_val_1624_);
                    crate::leanh::lean_dec_ref_known(v_newArg_x3f_1605_, 1);
                    v___x_1625_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3,
                    );
                    v___x_1626_ = l_Lean_MessageData_ofName(v_oldArg_1604_);
                    v___x_1627_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1627_, 0, v___x_1625_);
                    crate::leanh::lean_ctor_set(v___x_1627_, 1, v___x_1626_);
                    v___x_1628_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5,
                    );
                    v___x_1629_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1629_, 0, v___x_1627_);
                    crate::leanh::lean_ctor_set(v___x_1629_, 1, v___x_1628_);
                    v___x_1630_ = 0;
                    v___x_1631_ = l_Lean_MessageData_ofConstName(v_declName_1603_, v___x_1630_);
                    v___x_1632_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1632_, 0, v___x_1629_);
                    crate::leanh::lean_ctor_set(v___x_1632_, 1, v___x_1631_);
                    v___x_1633_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9,
                    );
                    v___x_1634_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                    crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = l_Lean_MessageData_ofName(v_val_1624_);
                    v___x_1636_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                    crate::leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                    v___x_1637_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11,
                    );
                    v___x_1638_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1638_, 0, v___x_1636_);
                    crate::leanh::lean_ctor_set(v___x_1638_, 1, v___x_1637_);
                    v___y_1608_ = v___x_1638_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_text_x3f_1606_) == 0 {
                    return v___y_1608_;
                } else {
                    v_val_1609_ = crate::leanh::lean_ctor_get(v_text_x3f_1606_, 0);
                    crate::leanh::lean_inc(v_val_1609_);
                    crate::leanh::lean_dec_ref_known(v_text_x3f_1606_, 1);
                    v___x_1610_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1,
                    );
                    v___x_1611_ = l_Lean_stringToMessageData(v_val_1609_);
                    v___x_1612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1610_);
                    crate::leanh::lean_ctor_set(v___x_1612_, 1, v___x_1611_);
                    v___x_1613_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1613_, 0, v___y_1608_);
                    crate::leanh::lean_ctor_set(v___x_1613_, 1, v___x_1612_);
                    return v___x_1613_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(
    mut v_k_1639_: *mut crate::leanh::LeanObject,
    mut v_b_1640_: *mut crate::leanh::LeanObject,
    mut v_c_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1645_);
    crate::leanh::lean_inc_ref(v___y_1644_);
    crate::leanh::lean_inc(v___y_1643_);
    crate::leanh::lean_inc_ref(v___y_1642_);
    v___x_1647_ = crate::leanh::lean_apply_7(
        v_k_1639_,
        v_b_1640_,
        v_c_1641_,
        v___y_1642_,
        v___y_1643_,
        v___y_1644_,
        v___y_1645_,
        crate::leanh::lean_box(0),
    );
    return v___x_1647_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(
    mut v_k_1648_: *mut crate::leanh::LeanObject,
    mut v_b_1649_: *mut crate::leanh::LeanObject,
    mut v_c_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1656_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(v_k_1648_, v_b_1649_, v_c_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
    crate::leanh::lean_dec(v___y_1654_);
    crate::leanh::lean_dec_ref(v___y_1653_);
    crate::leanh::lean_dec(v___y_1652_);
    crate::leanh::lean_dec_ref(v___y_1651_);
    return v_res_1656_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(
    mut v_type_1657_: *mut crate::leanh::LeanObject,
    mut v_k_1658_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1659_: u8,
    mut v_whnfType_1660_: u8,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1666_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1666_, 0, v_k_1658_);
                v___x_1667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1657_,
                    v___f_1666_,
                    v_cleanupAnnotations_1659_,
                    v_whnfType_1660_,
                    v___y_1661_,
                    v___y_1662_,
                    v___y_1663_,
                    v___y_1664_,
                );
                if crate::leanh::lean_obj_tag(v___x_1667_) == 0 {
                    v_a_1668_ = crate::leanh::lean_ctor_get(v___x_1667_, 0);
                    v_isSharedCheck_1675_ = (!crate::leanh::lean_is_exclusive(v___x_1667_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1667_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1668_);
                        crate::leanh::lean_dec(v___x_1667_);
                        v___x_1670_ = crate::leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1667_, 0);
                    v_isSharedCheck_1683_ = (!crate::leanh::lean_is_exclusive(v___x_1667_)) as u8;
                    if v_isSharedCheck_1683_ == 0 {
                        v___x_1678_ = v___x_1667_;
                        v_isShared_1679_ = v_isSharedCheck_1683_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1676_);
                        crate::leanh::lean_dec(v___x_1667_);
                        v___x_1678_ = crate::leanh::lean_box(0);
                        v_isShared_1679_ = v_isSharedCheck_1683_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1671_ == 0 {
                    v___x_1673_ = v___x_1670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
                    v___x_1673_ = v_reuseFailAlloc_1674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1673_;
            }
            3 => {
                if v_isShared_1679_ == 0 {
                    v___x_1681_ = v___x_1678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___boxed(
    mut v_type_1684_: *mut crate::leanh::LeanObject,
    mut v_k_1685_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1686_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1693_: u8 = 0;
    let mut v_whnfType_boxed_1694_: u8 = 0;
    let mut v_res_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1693_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1686_) as u8);
    v_whnfType_boxed_1694_ = (crate::leanh::lean_unbox(v_whnfType_1687_) as u8);
    v_res_1695_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_1684_, v_k_1685_, v_cleanupAnnotations_boxed_1693_, v_whnfType_boxed_1694_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    crate::leanh::lean_dec(v___y_1691_);
    crate::leanh::lean_dec_ref(v___y_1690_);
    crate::leanh::lean_dec(v___y_1689_);
    crate::leanh::lean_dec_ref(v___y_1688_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(
    mut v_00_u03b1_1696_: *mut crate::leanh::LeanObject,
    mut v_type_1697_: *mut crate::leanh::LeanObject,
    mut v_k_1698_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1699_: u8,
    mut v_whnfType_1700_: u8,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_1697_, v_k_1698_, v_cleanupAnnotations_1699_, v_whnfType_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___boxed(
    mut v_00_u03b1_1707_: *mut crate::leanh::LeanObject,
    mut v_type_1708_: *mut crate::leanh::LeanObject,
    mut v_k_1709_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1710_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1717_: u8 = 0;
    let mut v_whnfType_boxed_1718_: u8 = 0;
    let mut v_res_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1717_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1710_) as u8);
    v_whnfType_boxed_1718_ = (crate::leanh::lean_unbox(v_whnfType_1711_) as u8);
    v_res_1719_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(v_00_u03b1_1707_, v_type_1708_, v_k_1709_, v_cleanupAnnotations_boxed_1717_, v_whnfType_boxed_1718_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
    crate::leanh::lean_dec(v___y_1715_);
    crate::leanh::lean_dec_ref(v___y_1714_);
    crate::leanh::lean_dec(v___y_1713_);
    crate::leanh::lean_dec_ref(v___y_1712_);
    return v_res_1719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(
    mut v_sz_1720_: usize,
    mut v_i_1721_: usize,
    mut v_bs_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: usize = 0;
    let mut v___x_1737_: usize = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1727_ = lean_usize_dec_lt(v_i_1721_, v_sz_1720_);
                if v___x_1727_ == 0 {
                    v___x_1728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1728_, 0, v_bs_1722_);
                    return v___x_1728_;
                } else {
                    v_v_1729_ = lean_array_uget_borrowed(v_bs_1722_, v_i_1721_);
                    v___x_1730_ = l_Lean_Expr_fvarId_x21(v_v_1729_);
                    v___x_1731_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_1730_,
                        v___y_1723_,
                        v___y_1724_,
                        v___y_1725_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1731_) == 0 {
                        v_a_1732_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                        crate::leanh::lean_inc(v_a_1732_);
                        crate::leanh::lean_dec_ref_known(v___x_1731_, 1);
                        v___x_1733_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1734_ = lean_array_uset(v_bs_1722_, v_i_1721_, v___x_1733_);
                        v___x_1735_ = l_Lean_LocalDecl_userName(v_a_1732_);
                        crate::leanh::lean_dec(v_a_1732_);
                        v___x_1736_ = 1usize;
                        v___x_1737_ = lean_usize_add(v_i_1721_, v___x_1736_);
                        v___x_1738_ = lean_array_uset(v_bs_x27_1734_, v_i_1721_, v___x_1735_);
                        v_i_1721_ = v___x_1737_;
                        v_bs_1722_ = v___x_1738_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1722_);
                        v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                        v_isSharedCheck_1747_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                        if v_isSharedCheck_1747_ == 0 {
                            v___x_1742_ = v___x_1731_;
                            v_isShared_1743_ = v_isSharedCheck_1747_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1740_);
                            crate::leanh::lean_dec(v___x_1731_);
                            v___x_1742_ = crate::leanh::lean_box(0);
                            v_isShared_1743_ = v_isSharedCheck_1747_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1743_ == 0 {
                    v___x_1745_ = v___x_1742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg___boxed(
    mut v_sz_1748_: *mut crate::leanh::LeanObject,
    mut v_i_1749_: *mut crate::leanh::LeanObject,
    mut v_bs_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1755_: usize = 0;
    let mut v_i_boxed_1756_: usize = 0;
    let mut v_res_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1755_ = crate::leanh::lean_unbox_usize(v_sz_1748_);
    crate::leanh::lean_dec(v_sz_1748_);
    v_i_boxed_1756_ = crate::leanh::lean_unbox_usize(v_i_1749_);
    crate::leanh::lean_dec(v_i_1749_);
    v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_boxed_1755_, v_i_boxed_1756_, v_bs_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v___y_1752_);
    crate::leanh::lean_dec_ref(v___y_1751_);
    return v_res_1757_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v_xs_1758_: *mut crate::leanh::LeanObject,
    mut v_x_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1765_: usize = 0;
    let mut v___x_1766_: usize = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1765_ = lean_array_size(v_xs_1758_);
    v___x_1766_ = 0usize;
    v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_1765_, v___x_1766_, v_xs_1758_, v___y_1760_, v___y_1762_, v___y_1763_);
    return v___x_1767_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v_xs_1768_: *mut crate::leanh::LeanObject,
    mut v_x_1769_: *mut crate::leanh::LeanObject,
    mut v___y_1770_: *mut crate::leanh::LeanObject,
    mut v___y_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1775_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v_xs_1768_, v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
    crate::leanh::lean_dec(v___y_1773_);
    crate::leanh::lean_dec_ref(v___y_1772_);
    crate::leanh::lean_dec(v___y_1771_);
    crate::leanh::lean_dec_ref(v___y_1770_);
    crate::leanh::lean_dec_ref(v_x_1769_);
    return v_res_1775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(
    mut v_oldArg_1776_: *mut crate::leanh::LeanObject,
    mut v_as_1777_: *mut crate::leanh::LeanObject,
    mut v_i_1778_: usize,
    mut v_stop_1779_: usize,
) -> u8 {
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: usize = 0;
    let mut v___x_1784_: usize = 0;
    let mut v___x_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1780_ = lean_usize_dec_eq(v_i_1778_, v_stop_1779_);
                if v___x_1780_ == 0 {
                    v___x_1781_ = lean_array_uget_borrowed(v_as_1777_, v_i_1778_);
                    v___x_1782_ = lean_name_eq(v___x_1781_, v_oldArg_1776_);
                    if v___x_1782_ == 0 {
                        v___x_1783_ = 1usize;
                        v___x_1784_ = lean_usize_add(v_i_1778_, v___x_1783_);
                        v_i_1778_ = v___x_1784_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1782_;
                    }
                } else {
                    v___x_1786_ = 0;
                    return v___x_1786_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2___boxed(
    mut v_oldArg_1787_: *mut crate::leanh::LeanObject,
    mut v_as_1788_: *mut crate::leanh::LeanObject,
    mut v_i_1789_: *mut crate::leanh::LeanObject,
    mut v_stop_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1791_: usize = 0;
    let mut v_stop_boxed_1792_: usize = 0;
    let mut v_res_1793_: u8 = 0;
    let mut v_r_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1791_ = crate::leanh::lean_unbox_usize(v_i_1789_);
    crate::leanh::lean_dec(v_i_1789_);
    v_stop_boxed_1792_ = crate::leanh::lean_unbox_usize(v_stop_1790_);
    crate::leanh::lean_dec(v_stop_1790_);
    v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_oldArg_1787_, v_as_1788_, v_i_boxed_1791_, v_stop_boxed_1792_);
    crate::leanh::lean_dec_ref(v_as_1788_);
    crate::leanh::lean_dec(v_oldArg_1787_);
    v_r_1794_ = crate::leanh::lean_box((v_res_1793_) as usize);
    return v_r_1794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1795_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0);
    v___x_1797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_1799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1800_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1800_, 0, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1800_, 1, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1800_, 2, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1800_, 3, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1800_, 4, v___x_1798_);
    crate::leanh::lean_ctor_set(v___x_1800_, 5, v___x_1798_);
    crate::leanh::lean_ctor_set(v___x_1800_, 6, v___x_1798_);
    crate::leanh::lean_ctor_set(v___x_1800_, 7, v___x_1798_);
    crate::leanh::lean_ctor_set(v___x_1800_, 8, v___x_1798_);
    crate::leanh::lean_ctor_set(v___x_1800_, 9, v___x_1798_);
    return v___x_1800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1801_);
    v___x_1803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1804_: usize = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1804_ = 5usize;
    v___x_1805_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1806_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
    v___x_1808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
    v___x_1809_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    crate::leanh::lean_ctor_set(v___x_1809_, 1, v___x_1807_);
    crate::leanh::lean_ctor_set(v___x_1809_, 2, v___x_1805_);
    crate::leanh::lean_ctor_set(v___x_1809_, 3, v___x_1805_);
    crate::leanh::lean_ctor_set_usize(v___x_1809_, 4, v___x_1804_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = crate::leanh::lean_box(1);
    v___x_1811_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4);
    v___x_1812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1813_, 2, v___x_1810_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6;
    v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
    return v___x_1816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8;
    v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
    return v___x_1819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10;
    v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
    return v___x_1822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12;
    v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
    return v___x_1825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14;
    v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
    return v___x_1828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16;
    v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18;
    v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(
    mut v_msg_1835_: *mut crate::leanh::LeanObject,
    mut v_declHint_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v_isExporting_1842_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1839_ = lean_st_ref_get(v___y_1837_);
                v_env_1840_ = crate::leanh::lean_ctor_get(v___x_1839_, 0);
                crate::leanh::lean_inc_ref(v_env_1840_);
                crate::leanh::lean_dec(v___x_1839_);
                v___x_1841_ = l_Lean_Name_isAnonymous(v_declHint_1836_);
                if v___x_1841_ == 0 {
                    v_isExporting_1842_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1842_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1840_);
                        crate::leanh::lean_dec(v_declHint_1836_);
                        v___x_1843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1843_, 0, v_msg_1835_);
                        return v___x_1843_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1840_);
                        v___x_1844_ = l_Lean_Environment_setExporting(v_env_1840_, v___x_1841_);
                        crate::leanh::lean_inc(v_declHint_1836_);
                        crate::leanh::lean_inc_ref(v___x_1844_);
                        v___x_1845_ = l_Lean_Environment_contains(
                            v___x_1844_,
                            v_declHint_1836_,
                            v_isExporting_1842_,
                        );
                        if v___x_1845_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1844_);
                            crate::leanh::lean_dec_ref(v_env_1840_);
                            crate::leanh::lean_dec(v_declHint_1836_);
                            v___x_1846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1846_, 0, v_msg_1835_);
                            return v___x_1846_;
                        } else {
                            v___x_1847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
                            v___x_1848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
                            v___x_1849_ = l_Lean_Options_empty;
                            v___x_1850_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1850_, 0, v___x_1844_);
                            crate::leanh::lean_ctor_set(v___x_1850_, 1, v___x_1847_);
                            crate::leanh::lean_ctor_set(v___x_1850_, 2, v___x_1848_);
                            crate::leanh::lean_ctor_set(v___x_1850_, 3, v___x_1849_);
                            crate::leanh::lean_inc(v_declHint_1836_);
                            v___x_1851_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1836_, v___x_1841_);
                            v_c_1852_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1852_, 0, v___x_1850_);
                            crate::leanh::lean_ctor_set(v_c_1852_, 1, v___x_1851_);
                            v___x_1853_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1840_,
                                v_declHint_1836_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1853_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1840_);
                                crate::leanh::lean_dec(v_declHint_1836_);
                                v___x_1854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
                                v___x_1855_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                                crate::leanh::lean_ctor_set(v___x_1855_, 1, v_c_1852_);
                                v___x_1856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9);
                                v___x_1857_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1855_);
                                crate::leanh::lean_ctor_set(v___x_1857_, 1, v___x_1856_);
                                v___x_1858_ = l_Lean_MessageData_note(v___x_1857_);
                                v___x_1859_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1859_, 0, v_msg_1835_);
                                crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1858_);
                                v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
                                return v___x_1860_;
                            } else {
                                v_val_1861_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                                v_isSharedCheck_1896_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1853_)) as u8;
                                if v_isSharedCheck_1896_ == 0 {
                                    v___x_1863_ = v___x_1853_;
                                    v_isShared_1864_ = v_isSharedCheck_1896_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1861_);
                                    crate::leanh::lean_dec(v___x_1853_);
                                    v___x_1863_ = crate::leanh::lean_box(0);
                                    v_isShared_1864_ = v_isSharedCheck_1896_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1840_);
                    crate::leanh::lean_dec(v_declHint_1836_);
                    v___x_1897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1897_, 0, v_msg_1835_);
                    return v___x_1897_;
                }
            }
            1 => {
                v___x_1865_ = crate::leanh::lean_box(0);
                v___x_1866_ = l_Lean_Environment_header(v_env_1840_);
                crate::leanh::lean_dec_ref(v_env_1840_);
                v___x_1867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1866_);
                v_mod_1868_ = lean_array_get(v___x_1865_, v___x_1867_, v_val_1861_);
                crate::leanh::lean_dec(v_val_1861_);
                crate::leanh::lean_dec_ref(v___x_1867_);
                v___x_1869_ = l_Lean_isPrivateName(v_declHint_1836_);
                crate::leanh::lean_dec(v_declHint_1836_);
                if v___x_1869_ == 0 {
                    v___x_1870_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11);
                    v___x_1871_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1870_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_c_1852_);
                    v___x_1872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13);
                    v___x_1873_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1871_);
                    crate::leanh::lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                    v___x_1874_ = l_Lean_MessageData_ofName(v_mod_1868_);
                    v___x_1875_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                    crate::leanh::lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                    v___x_1876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15);
                    v___x_1877_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1877_, 0, v___x_1875_);
                    crate::leanh::lean_ctor_set(v___x_1877_, 1, v___x_1876_);
                    v___x_1878_ = l_Lean_MessageData_note(v___x_1877_);
                    v___x_1879_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1879_, 0, v_msg_1835_);
                    crate::leanh::lean_ctor_set(v___x_1879_, 1, v___x_1878_);
                    if v_isShared_1864_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1863_, 0);
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1879_);
                        v___x_1881_ = v___x_1863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    crate::leanh::lean_ctor_set(v___x_1884_, 1, v_c_1852_);
                    v___x_1885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17);
                    v___x_1886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1884_);
                    crate::leanh::lean_ctor_set(v___x_1886_, 1, v___x_1885_);
                    v___x_1887_ = l_Lean_MessageData_ofName(v_mod_1868_);
                    v___x_1888_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1886_);
                    crate::leanh::lean_ctor_set(v___x_1888_, 1, v___x_1887_);
                    v___x_1889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19);
                    v___x_1890_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1890_, 0, v___x_1888_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 1, v___x_1889_);
                    v___x_1891_ = l_Lean_MessageData_note(v___x_1890_);
                    v___x_1892_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1892_, 0, v_msg_1835_);
                    crate::leanh::lean_ctor_set(v___x_1892_, 1, v___x_1891_);
                    if v_isShared_1864_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1863_, 0);
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1892_);
                        v___x_1894_ = v___x_1863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
                        v___x_1894_ = v_reuseFailAlloc_1895_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1881_;
            }
            3 => {
                return v___x_1894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___boxed(
    mut v_msg_1898_: *mut crate::leanh::LeanObject,
    mut v_declHint_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1898_, v_declHint_1899_, v___y_1900_);
    crate::leanh::lean_dec(v___y_1900_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(
    mut v_msg_1903_: *mut crate::leanh::LeanObject,
    mut v_declHint_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1908_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1903_, v_declHint_1904_, v___y_1906_);
                v_a_1909_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                v_isSharedCheck_1918_ = (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                if v_isSharedCheck_1918_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    v_isShared_1912_ = v_isSharedCheck_1918_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1909_);
                    crate::leanh::lean_dec(v___x_1908_);
                    v___x_1911_ = crate::leanh::lean_box(0);
                    v_isShared_1912_ = v_isSharedCheck_1918_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1913_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1914_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                crate::leanh::lean_ctor_set(v___x_1914_, 1, v_a_1909_);
                if v_isShared_1912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1911_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12___boxed(
    mut v_msg_1919_: *mut crate::leanh::LeanObject,
    mut v_declHint_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_1919_, v_declHint_1920_, v___y_1921_, v___y_1922_);
    crate::leanh::lean_dec(v___y_1922_);
    crate::leanh::lean_dec_ref(v___y_1921_);
    return v_res_1924_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = lean_st_ref_get(v___y_1927_);
    v_env_1930_ = crate::leanh::lean_ctor_get(v___x_1929_, 0);
    crate::leanh::lean_inc_ref(v_env_1930_);
    crate::leanh::lean_dec(v___x_1929_);
    v_options_1931_ = crate::leanh::lean_ctor_get(v___y_1926_, 2);
    v___x_1932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
    v___x_1933_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
    crate::leanh::lean_dec_ref(v___x_1934_);
    v___x_1935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_1931_);
    v___x_1936_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1936_, 0, v_env_1930_);
    crate::leanh::lean_ctor_set(v___x_1936_, 1, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1936_, 2, v___x_1935_);
    crate::leanh::lean_ctor_set(v___x_1936_, 3, v_options_1931_);
    v___x_1937_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    crate::leanh::lean_ctor_set(v___x_1937_, 1, v_msgData_1925_);
    v___x_1938_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1938_, 0, v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1939_, v___y_1940_, v___y_1941_);
    crate::leanh::lean_dec(v___y_1941_);
    crate::leanh::lean_dec_ref(v___y_1940_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1948_ = crate::leanh::lean_ctor_get(v___y_1945_, 5);
                v___x_1949_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msg_1944_, v___y_1945_, v___y_1946_);
                v_a_1950_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                v_isSharedCheck_1958_ = (!crate::leanh::lean_is_exclusive(v___x_1949_)) as u8;
                if v_isSharedCheck_1958_ == 0 {
                    v___x_1952_ = v___x_1949_;
                    v_isShared_1953_ = v_isSharedCheck_1958_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1950_);
                    crate::leanh::lean_dec(v___x_1949_);
                    v___x_1952_ = crate::leanh::lean_box(0);
                    v_isShared_1953_ = v_isSharedCheck_1958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1948_);
                v___x_1954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1954_, 0, v_ref_1948_);
                crate::leanh::lean_ctor_set(v___x_1954_, 1, v_a_1950_);
                if v_isShared_1953_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1952_, 1);
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1954_);
                    v___x_1956_ = v___x_1952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
                    v___x_1956_ = v_reuseFailAlloc_1957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_1959_, v___y_1960_, v___y_1961_);
    crate::leanh::lean_dec(v___y_1961_);
    crate::leanh::lean_dec_ref(v___y_1960_);
    return v_res_1963_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(
    mut v_ref_1964_: *mut crate::leanh::LeanObject,
    mut v_msg_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1981_: u8 = 0;
    let mut v_cancelTk_x3f_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1983_: u8 = 0;
    let mut v_inheritedTraceOptions_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1969_ = crate::leanh::lean_ctor_get(v___y_1966_, 0);
    v_fileMap_1970_ = crate::leanh::lean_ctor_get(v___y_1966_, 1);
    v_options_1971_ = crate::leanh::lean_ctor_get(v___y_1966_, 2);
    v_currRecDepth_1972_ = crate::leanh::lean_ctor_get(v___y_1966_, 3);
    v_maxRecDepth_1973_ = crate::leanh::lean_ctor_get(v___y_1966_, 4);
    v_ref_1974_ = crate::leanh::lean_ctor_get(v___y_1966_, 5);
    v_currNamespace_1975_ = crate::leanh::lean_ctor_get(v___y_1966_, 6);
    v_openDecls_1976_ = crate::leanh::lean_ctor_get(v___y_1966_, 7);
    v_initHeartbeats_1977_ = crate::leanh::lean_ctor_get(v___y_1966_, 8);
    v_maxHeartbeats_1978_ = crate::leanh::lean_ctor_get(v___y_1966_, 9);
    v_quotContext_1979_ = crate::leanh::lean_ctor_get(v___y_1966_, 10);
    v_currMacroScope_1980_ = crate::leanh::lean_ctor_get(v___y_1966_, 11);
    v_diag_1981_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1966_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1982_ = crate::leanh::lean_ctor_get(v___y_1966_, 12);
    v_suppressElabErrors_1983_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1966_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1984_ = crate::leanh::lean_ctor_get(v___y_1966_, 13);
    v_ref_1985_ = l_Lean_replaceRef(v_ref_1964_, v_ref_1974_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1984_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1982_);
    crate::leanh::lean_inc(v_currMacroScope_1980_);
    crate::leanh::lean_inc(v_quotContext_1979_);
    crate::leanh::lean_inc(v_maxHeartbeats_1978_);
    crate::leanh::lean_inc(v_initHeartbeats_1977_);
    crate::leanh::lean_inc(v_openDecls_1976_);
    crate::leanh::lean_inc(v_currNamespace_1975_);
    crate::leanh::lean_inc(v_maxRecDepth_1973_);
    crate::leanh::lean_inc(v_currRecDepth_1972_);
    crate::leanh::lean_inc_ref(v_options_1971_);
    crate::leanh::lean_inc_ref(v_fileMap_1970_);
    crate::leanh::lean_inc_ref(v_fileName_1969_);
    v___x_1986_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1986_, 0, v_fileName_1969_);
    crate::leanh::lean_ctor_set(v___x_1986_, 1, v_fileMap_1970_);
    crate::leanh::lean_ctor_set(v___x_1986_, 2, v_options_1971_);
    crate::leanh::lean_ctor_set(v___x_1986_, 3, v_currRecDepth_1972_);
    crate::leanh::lean_ctor_set(v___x_1986_, 4, v_maxRecDepth_1973_);
    crate::leanh::lean_ctor_set(v___x_1986_, 5, v_ref_1985_);
    crate::leanh::lean_ctor_set(v___x_1986_, 6, v_currNamespace_1975_);
    crate::leanh::lean_ctor_set(v___x_1986_, 7, v_openDecls_1976_);
    crate::leanh::lean_ctor_set(v___x_1986_, 8, v_initHeartbeats_1977_);
    crate::leanh::lean_ctor_set(v___x_1986_, 9, v_maxHeartbeats_1978_);
    crate::leanh::lean_ctor_set(v___x_1986_, 10, v_quotContext_1979_);
    crate::leanh::lean_ctor_set(v___x_1986_, 11, v_currMacroScope_1980_);
    crate::leanh::lean_ctor_set(v___x_1986_, 12, v_cancelTk_x3f_1982_);
    crate::leanh::lean_ctor_set(v___x_1986_, 13, v_inheritedTraceOptions_1984_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1986_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1981_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1986_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1983_,
    );
    v___x_1987_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_1965_, v___x_1986_, v___y_1967_);
    crate::leanh::lean_dec_ref_known(v___x_1986_, 14);
    return v___x_1987_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(
    mut v_ref_1988_: *mut crate::leanh::LeanObject,
    mut v_msg_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1988_, v_msg_1989_, v___y_1990_, v___y_1991_);
    crate::leanh::lean_dec(v___y_1991_);
    crate::leanh::lean_dec_ref(v___y_1990_);
    crate::leanh::lean_dec(v_ref_1988_);
    return v_res_1993_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(
    mut v_ref_1994_: *mut crate::leanh::LeanObject,
    mut v_msg_1995_: *mut crate::leanh::LeanObject,
    mut v_declHint_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_1995_, v_declHint_1996_, v___y_1997_, v___y_1998_);
    v_a_2001_ = crate::leanh::lean_ctor_get(v___x_2000_, 0);
    crate::leanh::lean_inc(v_a_2001_);
    crate::leanh::lean_dec_ref(v___x_2000_);
    v___x_2002_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1994_, v_a_2001_, v___y_1997_, v___y_1998_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(
    mut v_ref_2003_: *mut crate::leanh::LeanObject,
    mut v_msg_2004_: *mut crate::leanh::LeanObject,
    mut v_declHint_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2003_, v_msg_2004_, v_declHint_2005_, v___y_2006_, v___y_2007_);
    crate::leanh::lean_dec(v___y_2007_);
    crate::leanh::lean_dec_ref(v___y_2006_);
    crate::leanh::lean_dec(v_ref_2003_);
    return v_res_2009_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0;
    v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
    return v___x_2012_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2;
    v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(
    mut v_ref_2016_: *mut crate::leanh::LeanObject,
    mut v_constName_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2021_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1);
    v___x_2022_ = 0;
    crate::leanh::lean_inc(v_constName_2017_);
    v___x_2023_ = l_Lean_MessageData_ofConstName(v_constName_2017_, v___x_2022_);
    v___x_2024_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2021_);
    crate::leanh::lean_ctor_set(v___x_2024_, 1, v___x_2023_);
    v___x_2025_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
    v___x_2026_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2026_, 0, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2025_);
    v___x_2027_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2016_, v___x_2026_, v_constName_2017_, v___y_2018_, v___y_2019_);
    return v___x_2027_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(
    mut v_ref_2028_: *mut crate::leanh::LeanObject,
    mut v_constName_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2028_, v_constName_2029_, v___y_2030_, v___y_2031_);
    crate::leanh::lean_dec(v___y_2031_);
    crate::leanh::lean_dec_ref(v___y_2030_);
    crate::leanh::lean_dec(v_ref_2028_);
    return v_res_2033_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(
    mut v_constName_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2038_ = crate::leanh::lean_ctor_get(v___y_2035_, 5);
    v___x_2039_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2038_, v_constName_2034_, v___y_2035_, v___y_2036_);
    return v___x_2039_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(
    mut v_constName_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2040_, v___y_2041_, v___y_2042_);
    crate::leanh::lean_dec(v___y_2042_);
    crate::leanh::lean_dec_ref(v___y_2041_);
    return v_res_2044_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(
    mut v_constName_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2049_ = lean_st_ref_get(v___y_2047_);
                v_env_2050_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                crate::leanh::lean_inc_ref(v_env_2050_);
                crate::leanh::lean_dec(v___x_2049_);
                v___x_2051_ = 0;
                crate::leanh::lean_inc(v_constName_2045_);
                v___x_2052_ =
                    l_Lean_Environment_find_x3f(v_env_2050_, v_constName_2045_, v___x_2051_);
                if crate::leanh::lean_obj_tag(v___x_2052_) == 0 {
                    v___x_2053_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2045_, v___y_2046_, v___y_2047_);
                    return v___x_2053_;
                } else {
                    crate::leanh::lean_dec(v_constName_2045_);
                    v_val_2054_ = crate::leanh::lean_ctor_get(v___x_2052_, 0);
                    v_isSharedCheck_2061_ = (!crate::leanh::lean_is_exclusive(v___x_2052_)) as u8;
                    if v_isSharedCheck_2061_ == 0 {
                        v___x_2056_ = v___x_2052_;
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2054_);
                        crate::leanh::lean_dec(v___x_2052_);
                        v___x_2056_ = crate::leanh::lean_box(0);
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2057_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2056_, 0);
                    v___x_2059_ = v___x_2056_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_val_2054_);
                    v___x_2059_ = v_reuseFailAlloc_2060_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3___boxed(
    mut v_constName_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_constName_2062_, v___y_2063_, v___y_2064_);
    crate::leanh::lean_dec(v___y_2064_);
    crate::leanh::lean_dec_ref(v___y_2063_);
    return v_res_2066_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(
    mut v___y_2074_: u8,
    mut v_suppressElabErrors_2075_: u8,
    mut v_x_2076_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2076_) == 1 {
        let mut v_pre_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2077_ = crate::leanh::lean_ctor_get(v_x_2076_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2077_) {
            1 => {
                let mut v_pre_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2078_ = crate::leanh::lean_ctor_get(v_pre_2077_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2078_) {
                    0 => {
                        let mut v_str_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2082_: u8 = 0;
                        v_str_2079_ = crate::leanh::lean_ctor_get(v_x_2076_, 1);
                        v_str_2080_ = crate::leanh::lean_ctor_get(v_pre_2077_, 1);
                        v___x_2081_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
                        v___x_2082_ = lean_string_dec_eq(v_str_2080_, v___x_2081_);
                        if v___x_2082_ == 0 {
                            let mut v___x_2083_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2084_: u8 = 0;
                            v___x_2083_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0;
                            v___x_2084_ = lean_string_dec_eq(v_str_2080_, v___x_2083_);
                            if v___x_2084_ == 0 {
                                return v___y_2074_;
                            } else {
                                let mut v___x_2085_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2086_: u8 = 0;
                                v___x_2085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1;
                                v___x_2086_ = lean_string_dec_eq(v_str_2079_, v___x_2085_);
                                if v___x_2086_ == 0 {
                                    return v___y_2074_;
                                } else {
                                    return v_suppressElabErrors_2075_;
                                }
                            }
                        } else {
                            let mut v___x_2087_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2088_: u8 = 0;
                            v___x_2087_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2;
                            v___x_2088_ = lean_string_dec_eq(v_str_2079_, v___x_2087_);
                            if v___x_2088_ == 0 {
                                return v___y_2074_;
                            } else {
                                return v_suppressElabErrors_2075_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2089_ = crate::leanh::lean_ctor_get(v_pre_2078_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2089_) == 0 {
                            let mut v_str_2090_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2091_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2092_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2093_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2094_: u8 = 0;
                            v_str_2090_ = crate::leanh::lean_ctor_get(v_x_2076_, 1);
                            v_str_2091_ = crate::leanh::lean_ctor_get(v_pre_2077_, 1);
                            v_str_2092_ = crate::leanh::lean_ctor_get(v_pre_2078_, 1);
                            v___x_2093_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3;
                            v___x_2094_ = lean_string_dec_eq(v_str_2092_, v___x_2093_);
                            if v___x_2094_ == 0 {
                                return v___y_2074_;
                            } else {
                                let mut v___x_2095_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2096_: u8 = 0;
                                v___x_2095_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4;
                                v___x_2096_ = lean_string_dec_eq(v_str_2091_, v___x_2095_);
                                if v___x_2096_ == 0 {
                                    return v___y_2074_;
                                } else {
                                    let mut v___x_2097_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2098_: u8 = 0;
                                    v___x_2097_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5;
                                    v___x_2098_ = lean_string_dec_eq(v_str_2090_, v___x_2097_);
                                    if v___x_2098_ == 0 {
                                        return v___y_2074_;
                                    } else {
                                        return v_suppressElabErrors_2075_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2074_;
                        }
                    }
                    _ => {
                        return v___y_2074_;
                    }
                }
            }
            0 => {
                let mut v_str_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2101_: u8 = 0;
                v_str_2099_ = crate::leanh::lean_ctor_get(v_x_2076_, 1);
                v___x_2100_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6;
                v___x_2101_ = lean_string_dec_eq(v_str_2099_, v___x_2100_);
                if v___x_2101_ == 0 {
                    return v___y_2074_;
                } else {
                    return v_suppressElabErrors_2075_;
                }
            }
            _ => {
                return v___y_2074_;
            }
        }
    } else {
        return v___y_2074_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_10682__boxed_2105_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2106_: u8 = 0;
    let mut v_res_2107_: u8 = 0;
    let mut v_r_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_10682__boxed_2105_ = (crate::leanh::lean_unbox(v___y_2102_) as u8);
    v_suppressElabErrors_boxed_2106_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2103_) as u8);
    v_res_2107_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_10682__boxed_2105_, v_suppressElabErrors_boxed_2106_, v_x_2104_);
    crate::leanh::lean_dec(v_x_2104_);
    v_r_2108_ = crate::leanh::lean_box((v_res_2107_) as usize);
    return v_r_2108_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(
    mut v_opts_2109_: *mut crate::leanh::LeanObject,
    mut v_opt_2110_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2111_ = crate::leanh::lean_ctor_get(v_opt_2110_, 0);
    v_defValue_2112_ = crate::leanh::lean_ctor_get(v_opt_2110_, 1);
    v_map_2113_ = crate::leanh::lean_ctor_get(v_opts_2109_, 0);
    v___x_2114_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2113_,
            v_name_2111_,
        );
    if crate::leanh::lean_obj_tag(v___x_2114_) == 0 {
        let mut v___x_2115_: u8 = 0;
        v___x_2115_ = (crate::leanh::lean_unbox(v_defValue_2112_) as u8);
        return v___x_2115_;
    } else {
        let mut v_val_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2116_ = crate::leanh::lean_ctor_get(v___x_2114_, 0);
        crate::leanh::lean_inc(v_val_2116_);
        crate::leanh::lean_dec_ref_known(v___x_2114_, 1);
        if crate::leanh::lean_obj_tag(v_val_2116_) == 1 {
            let mut v_v_2117_: u8 = 0;
            v_v_2117_ = crate::leanh::lean_ctor_get_uint8(v_val_2116_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2116_, 0);
            return v_v_2117_;
        } else {
            let mut v___x_2118_: u8 = 0;
            crate::leanh::lean_dec(v_val_2116_);
            v___x_2118_ = (crate::leanh::lean_unbox(v_defValue_2112_) as u8);
            return v___x_2118_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(
    mut v_opts_2119_: *mut crate::leanh::LeanObject,
    mut v_opt_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2121_: u8 = 0;
    let mut v_r_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_opts_2119_, v_opt_2120_);
    crate::leanh::lean_dec_ref(v_opt_2120_);
    crate::leanh::lean_dec_ref(v_opts_2119_);
    v_r_2122_ = crate::leanh::lean_box((v_res_2121_) as usize);
    return v_r_2122_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(
    mut v_ref_2124_: *mut crate::leanh::LeanObject,
    mut v_msgData_2125_: *mut crate::leanh::LeanObject,
    mut v_severity_2126_: u8,
    mut v_isSilent_2127_: u8,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: u8 = 0;
    let mut v___y_2138_: u8 = 0;
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v___y_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: u8 = 0;
    let mut v___y_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: u8 = 0;
    let mut v___y_2174_: u8 = 0;
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v___y_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: u8 = 0;
    let mut v___y_2197_: u8 = 0;
    let mut v___y_2198_: u8 = 0;
    let mut v___y_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: u8 = 0;
    let mut v___y_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2209_: u8 = 0;
    let mut v___y_2210_: u8 = 0;
    let mut v_ref_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___y_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: u8 = 0;
    let mut v___y_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: u8 = 0;
    let mut v___y_2223_: u8 = 0;
    let mut v___y_2225_: u8 = 0;
    let mut v_fileName_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2230_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = 2;
                v___x_2240_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2126_, v___x_2215_);
                if v___x_2240_ == 0 {
                    v___y_2225_ = v___x_2240_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2125_);
                    v___x_2241_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2125_);
                    v___y_2225_ = v___x_2241_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2141_ = lean_st_ref_take(v___y_2140_);
                v_currNamespace_2142_ = crate::leanh::lean_ctor_get(v___y_2139_, 6);
                v_openDecls_2143_ = crate::leanh::lean_ctor_get(v___y_2139_, 7);
                v_env_2144_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                v_nextMacroScope_2145_ = crate::leanh::lean_ctor_get(v___x_2141_, 1);
                v_ngen_2146_ = crate::leanh::lean_ctor_get(v___x_2141_, 2);
                v_auxDeclNGen_2147_ = crate::leanh::lean_ctor_get(v___x_2141_, 3);
                v_traceState_2148_ = crate::leanh::lean_ctor_get(v___x_2141_, 4);
                v_cache_2149_ = crate::leanh::lean_ctor_get(v___x_2141_, 5);
                v_messages_2150_ = crate::leanh::lean_ctor_get(v___x_2141_, 6);
                v_infoState_2151_ = crate::leanh::lean_ctor_get(v___x_2141_, 7);
                v_snapshotTasks_2152_ = crate::leanh::lean_ctor_get(v___x_2141_, 8);
                v_isSharedCheck_2166_ = (!crate::leanh::lean_is_exclusive(v___x_2141_)) as u8;
                if v_isSharedCheck_2166_ == 0 {
                    v___x_2154_ = v___x_2141_;
                    v_isShared_2155_ = v_isSharedCheck_2166_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2152_);
                    crate::leanh::lean_inc(v_infoState_2151_);
                    crate::leanh::lean_inc(v_messages_2150_);
                    crate::leanh::lean_inc(v_cache_2149_);
                    crate::leanh::lean_inc(v_traceState_2148_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2147_);
                    crate::leanh::lean_inc(v_ngen_2146_);
                    crate::leanh::lean_inc(v_nextMacroScope_2145_);
                    crate::leanh::lean_inc(v_env_2144_);
                    crate::leanh::lean_dec(v___x_2141_);
                    v___x_2154_ = crate::leanh::lean_box(0);
                    v_isShared_2155_ = v_isSharedCheck_2166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_2143_);
                crate::leanh::lean_inc(v_currNamespace_2142_);
                v___x_2156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2156_, 0, v_currNamespace_2142_);
                crate::leanh::lean_ctor_set(v___x_2156_, 1, v_openDecls_2143_);
                v___x_2157_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                crate::leanh::lean_ctor_set(v___x_2157_, 1, v___y_2135_);
                crate::leanh::lean_inc_ref(v___y_2136_);
                crate::leanh::lean_inc_ref(v___y_2133_);
                v___x_2158_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2158_, 0, v___y_2133_);
                crate::leanh::lean_ctor_set(v___x_2158_, 1, v___y_2134_);
                crate::leanh::lean_ctor_set(v___x_2158_, 2, v___y_2132_);
                crate::leanh::lean_ctor_set(v___x_2158_, 3, v___y_2136_);
                crate::leanh::lean_ctor_set(v___x_2158_, 4, v___x_2157_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2138_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2137_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2127_,
                );
                v___x_2159_ = l_Lean_MessageLog_add(v___x_2158_, v_messages_2150_);
                if v_isShared_2155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2154_, 6, v___x_2159_);
                    v___x_2161_ = v___x_2154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_env_2144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_nextMacroScope_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_ngen_2146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_auxDeclNGen_2147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_traceState_2148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 5, v_cache_2149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 6, v___x_2159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 7, v_infoState_2151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 8, v_snapshotTasks_2152_);
                    v___x_2161_ = v_reuseFailAlloc_2165_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2162_ = lean_st_ref_set(v___y_2140_, v___x_2161_);
                v___x_2163_ = crate::leanh::lean_box(0);
                v___x_2164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
                return v___x_2164_;
            }
            4 => {
                v___x_2176_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2125_,
                    );
                v___x_2177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v___x_2176_, v___y_2128_, v___y_2129_);
                v_a_2178_ = crate::leanh::lean_ctor_get(v___x_2177_, 0);
                v_isSharedCheck_2191_ = (!crate::leanh::lean_is_exclusive(v___x_2177_)) as u8;
                if v_isSharedCheck_2191_ == 0 {
                    v___x_2180_ = v___x_2177_;
                    v_isShared_2181_ = v_isSharedCheck_2191_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2178_);
                    crate::leanh::lean_dec(v___x_2177_);
                    v___x_2180_ = crate::leanh::lean_box(0);
                    v_isShared_2181_ = v_isSharedCheck_2191_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_2169_, 2);
                v___x_2182_ = l_Lean_FileMap_toPosition(v___y_2169_, v___y_2172_);
                crate::leanh::lean_dec(v___y_2172_);
                v___x_2183_ = l_Lean_FileMap_toPosition(v___y_2169_, v___y_2175_);
                crate::leanh::lean_dec(v___y_2175_);
                v___x_2184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                v___x_2185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0;
                if v___y_2171_ == 0 {
                    crate::leanh::lean_del_object(v___x_2180_);
                    crate::leanh::lean_dec_ref(v___y_2168_);
                    v___y_2132_ = v___x_2184_;
                    v___y_2133_ = v___y_2170_;
                    v___y_2134_ = v___x_2182_;
                    v___y_2135_ = v_a_2178_;
                    v___y_2136_ = v___x_2185_;
                    v___y_2137_ = v___y_2173_;
                    v___y_2138_ = v___y_2174_;
                    v___y_2139_ = v___y_2128_;
                    v___y_2140_ = v___y_2129_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2178_);
                    v___x_2186_ = l_Lean_MessageData_hasTag(v___y_2168_, v_a_2178_);
                    if v___x_2186_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2184_, 1);
                        crate::leanh::lean_dec_ref(v___x_2182_);
                        crate::leanh::lean_dec(v_a_2178_);
                        v___x_2187_ = crate::leanh::lean_box(0);
                        if v_isShared_2181_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2187_);
                            v___x_2189_ = v___x_2180_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2190_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
                            v___x_2189_ = v_reuseFailAlloc_2190_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2180_);
                        v___y_2132_ = v___x_2184_;
                        v___y_2133_ = v___y_2170_;
                        v___y_2134_ = v___x_2182_;
                        v___y_2135_ = v_a_2178_;
                        v___y_2136_ = v___x_2185_;
                        v___y_2137_ = v___y_2173_;
                        v___y_2138_ = v___y_2174_;
                        v___y_2139_ = v___y_2128_;
                        v___y_2140_ = v___y_2129_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2189_;
            }
            7 => {
                v___x_2201_ = l_Lean_Syntax_getTailPos_x3f(v___y_2199_, v___y_2198_);
                crate::leanh::lean_dec(v___y_2199_);
                if crate::leanh::lean_obj_tag(v___x_2201_) == 0 {
                    crate::leanh::lean_inc(v___y_2200_);
                    v___y_2168_ = v___y_2193_;
                    v___y_2169_ = v___y_2194_;
                    v___y_2170_ = v___y_2195_;
                    v___y_2171_ = v___y_2196_;
                    v___y_2172_ = v___y_2200_;
                    v___y_2173_ = v___y_2197_;
                    v___y_2174_ = v___y_2198_;
                    v___y_2175_ = v___y_2200_;
                    state = 4;
                    continue;
                } else {
                    v_val_2202_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                    crate::leanh::lean_inc(v_val_2202_);
                    crate::leanh::lean_dec_ref_known(v___x_2201_, 1);
                    v___y_2168_ = v___y_2193_;
                    v___y_2169_ = v___y_2194_;
                    v___y_2170_ = v___y_2195_;
                    v___y_2171_ = v___y_2196_;
                    v___y_2172_ = v___y_2200_;
                    v___y_2173_ = v___y_2197_;
                    v___y_2174_ = v___y_2198_;
                    v___y_2175_ = v_val_2202_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2211_ = l_Lean_replaceRef(v_ref_2124_, v___y_2208_);
                v___x_2212_ = l_Lean_Syntax_getPos_x3f(v_ref_2211_, v___y_2209_);
                if crate::leanh::lean_obj_tag(v___x_2212_) == 0 {
                    v___x_2213_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2193_ = v___y_2204_;
                    v___y_2194_ = v___y_2205_;
                    v___y_2195_ = v___y_2206_;
                    v___y_2196_ = v___y_2207_;
                    v___y_2197_ = v___y_2210_;
                    v___y_2198_ = v___y_2209_;
                    v___y_2199_ = v_ref_2211_;
                    v___y_2200_ = v___x_2213_;
                    state = 7;
                    continue;
                } else {
                    v_val_2214_ = crate::leanh::lean_ctor_get(v___x_2212_, 0);
                    crate::leanh::lean_inc(v_val_2214_);
                    crate::leanh::lean_dec_ref_known(v___x_2212_, 1);
                    v___y_2193_ = v___y_2204_;
                    v___y_2194_ = v___y_2205_;
                    v___y_2195_ = v___y_2206_;
                    v___y_2196_ = v___y_2207_;
                    v___y_2197_ = v___y_2210_;
                    v___y_2198_ = v___y_2209_;
                    v___y_2199_ = v_ref_2211_;
                    v___y_2200_ = v_val_2214_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2223_ == 0 {
                    v___y_2204_ = v___y_2221_;
                    v___y_2205_ = v___y_2217_;
                    v___y_2206_ = v___y_2218_;
                    v___y_2207_ = v___y_2219_;
                    v___y_2208_ = v___y_2220_;
                    v___y_2209_ = v___y_2222_;
                    v___y_2210_ = v_severity_2126_;
                    state = 8;
                    continue;
                } else {
                    v___y_2204_ = v___y_2221_;
                    v___y_2205_ = v___y_2217_;
                    v___y_2206_ = v___y_2218_;
                    v___y_2207_ = v___y_2219_;
                    v___y_2208_ = v___y_2220_;
                    v___y_2209_ = v___y_2222_;
                    v___y_2210_ = v___x_2215_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2225_ == 0 {
                    v_fileName_2226_ = crate::leanh::lean_ctor_get(v___y_2128_, 0);
                    v_fileMap_2227_ = crate::leanh::lean_ctor_get(v___y_2128_, 1);
                    v_options_2228_ = crate::leanh::lean_ctor_get(v___y_2128_, 2);
                    v_ref_2229_ = crate::leanh::lean_ctor_get(v___y_2128_, 5);
                    v_suppressElabErrors_2230_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2231_ = crate::leanh::lean_box((v___y_2225_) as usize);
                    v___x_2232_ = crate::leanh::lean_box((v_suppressElabErrors_2230_) as usize);
                    v___f_2233_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2233_, 0, v___x_2231_);
                    crate::leanh::lean_closure_set(v___f_2233_, 1, v___x_2232_);
                    v___x_2234_ = 1;
                    v___x_2235_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2126_, v___x_2234_);
                    if v___x_2235_ == 0 {
                        v___y_2217_ = v_fileMap_2227_;
                        v___y_2218_ = v_fileName_2226_;
                        v___y_2219_ = v_suppressElabErrors_2230_;
                        v___y_2220_ = v_ref_2229_;
                        v___y_2221_ = v___f_2233_;
                        v___y_2222_ = v___y_2225_;
                        v___y_2223_ = v___x_2235_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2236_ = l_Lean_warningAsError;
                        v___x_2237_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_2228_, v___x_2236_);
                        v___y_2217_ = v_fileMap_2227_;
                        v___y_2218_ = v_fileName_2226_;
                        v___y_2219_ = v_suppressElabErrors_2230_;
                        v___y_2220_ = v_ref_2229_;
                        v___y_2221_ = v___f_2233_;
                        v___y_2222_ = v___y_2225_;
                        v___y_2223_ = v___x_2237_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2125_);
                    v___x_2238_ = crate::leanh::lean_box(0);
                    v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                    return v___x_2239_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(
    mut v_ref_2242_: *mut crate::leanh::LeanObject,
    mut v_msgData_2243_: *mut crate::leanh::LeanObject,
    mut v_severity_2244_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2249_: u8 = 0;
    let mut v_isSilent_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2249_ = (crate::leanh::lean_unbox(v_severity_2244_) as u8);
    v_isSilent_boxed_2250_ = (crate::leanh::lean_unbox(v_isSilent_2245_) as u8);
    v_res_2251_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_2242_, v_msgData_2243_, v_severity_boxed_2249_, v_isSilent_boxed_2250_, v___y_2246_, v___y_2247_);
    crate::leanh::lean_dec(v___y_2247_);
    crate::leanh::lean_dec_ref(v___y_2246_);
    crate::leanh::lean_dec(v_ref_2242_);
    return v_res_2251_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_2252_: *mut crate::leanh::LeanObject,
    mut v_severity_2253_: u8,
    mut v_isSilent_2254_: u8,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2258_ = crate::leanh::lean_ctor_get(v___y_2255_, 5);
    v___x_2259_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_2258_, v_msgData_2252_, v_severity_2253_, v_isSilent_2254_, v___y_2255_, v___y_2256_);
    return v___x_2259_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_2260_: *mut crate::leanh::LeanObject,
    mut v_severity_2261_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2266_: u8 = 0;
    let mut v_isSilent_boxed_2267_: u8 = 0;
    let mut v_res_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2266_ = (crate::leanh::lean_unbox(v_severity_2261_) as u8);
    v_isSilent_boxed_2267_ = (crate::leanh::lean_unbox(v_isSilent_2262_) as u8);
    v_res_2268_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2260_, v_severity_boxed_2266_, v_isSilent_boxed_2267_, v___y_2263_, v___y_2264_);
    crate::leanh::lean_dec(v___y_2264_);
    crate::leanh::lean_dec_ref(v___y_2263_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(
    mut v_msgData_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: u8 = 0;
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = 1;
    v___x_2274_ = 0;
    v___x_2275_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2269_, v___x_2273_, v___x_2274_, v___y_2270_, v___y_2271_);
    return v___x_2275_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(
    mut v_msgData_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v_msgData_2276_, v___y_2277_, v___y_2278_);
    crate::leanh::lean_dec(v___y_2278_);
    crate::leanh::lean_dec_ref(v___y_2277_);
    return v_res_2280_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2281_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
    crate::leanh::lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2290_ = l_Lean_MessageData_ofFormat(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
    return v___x_2296_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2306_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2308_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    return v___x_2308_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2310_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 1, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 2, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 3, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 4, v___x_2309_);
    crate::leanh::lean_ctor_set(v___x_2310_, 5, v___x_2309_);
    return v___x_2310_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2312_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    crate::leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
    crate::leanh::lean_ctor_set(v___x_2312_, 2, v___x_2311_);
    crate::leanh::lean_ctor_set(v___x_2312_, 3, v___x_2311_);
    crate::leanh::lean_ctor_set(v___x_2312_, 4, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v___x_2316_: *mut crate::leanh::LeanObject,
    mut v___x_2317_: *mut crate::leanh::LeanObject,
    mut v___x_2318_: *mut crate::leanh::LeanObject,
    mut v___x_2319_: *mut crate::leanh::LeanObject,
    mut v___f_2320_: *mut crate::leanh::LeanObject,
    mut v___x_2321_: *mut crate::leanh::LeanObject,
    mut v_declName_2322_: *mut crate::leanh::LeanObject,
    mut v_stx_2323_: *mut crate::leanh::LeanObject,
    mut v___kind_2324_: u8,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_unused_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___y_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: usize = 0;
    let mut v___x_2429_: usize = 0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: usize = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u64 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v_a_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v___y_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldId_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldArg_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut v___y_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newId_x3f_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: u8 = 0;
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newId_x3f_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2360_ = l_Lean_Name_mkStr2(v___x_2316_, v___x_2317_);
                crate::leanh::lean_inc(v_stx_2323_);
                v___x_2361_ = l_Lean_Syntax_isOfKind(v_stx_2323_, v___x_2360_);
                crate::leanh::lean_dec(v___x_2360_);
                if v___x_2361_ == 0 {
                    crate::leanh::lean_dec(v_stx_2323_);
                    crate::leanh::lean_dec(v_declName_2322_);
                    crate::leanh::lean_dec_ref(v___f_2320_);
                    crate::leanh::lean_dec(v___x_2319_);
                    crate::leanh::lean_dec(v___x_2318_);
                    v___x_2536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2537_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2536_, v___y_2325_, v___y_2326_);
                    return v___x_2537_;
                } else {
                    v___x_2538_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_oldId_2539_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2538_);
                    v___x_2586_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2321_);
                    v___x_2587_ = l_Lean_Syntax_isNone(v___x_2586_);
                    if v___x_2587_ == 0 {
                        crate::leanh::lean_inc(v___x_2586_);
                        v___x_2588_ = l_Lean_Syntax_matchesNull(v___x_2586_, v___x_2538_);
                        if v___x_2588_ == 0 {
                            crate::leanh::lean_dec(v___x_2586_);
                            crate::leanh::lean_dec(v_oldId_2539_);
                            crate::leanh::lean_dec(v_stx_2323_);
                            crate::leanh::lean_dec(v_declName_2322_);
                            crate::leanh::lean_dec_ref(v___f_2320_);
                            crate::leanh::lean_dec(v___x_2319_);
                            crate::leanh::lean_dec(v___x_2318_);
                            v___x_2589_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2590_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2589_, v___y_2325_, v___y_2326_);
                            return v___x_2590_;
                        } else {
                            v_newId_x3f_2591_ = l_Lean_Syntax_getArg(v___x_2586_, v___x_2319_);
                            crate::leanh::lean_dec(v___x_2586_);
                            v___x_2592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2592_, 0, v_newId_x3f_2591_);
                            v_newId_x3f_2574_ = v___x_2592_;
                            v___y_2575_ = v___y_2325_;
                            v___y_2576_ = v___y_2326_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2586_);
                        v___x_2593_ = crate::leanh::lean_box(0);
                        v_newId_x3f_2574_ = v___x_2593_;
                        v___y_2575_ = v___y_2325_;
                        v___y_2576_ = v___y_2326_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2334_ = lean_st_ref_take(v___y_2333_);
                v_env_2335_ = crate::leanh::lean_ctor_get(v___x_2334_, 0);
                v_nextMacroScope_2336_ = crate::leanh::lean_ctor_get(v___x_2334_, 1);
                v_ngen_2337_ = crate::leanh::lean_ctor_get(v___x_2334_, 2);
                v_auxDeclNGen_2338_ = crate::leanh::lean_ctor_get(v___x_2334_, 3);
                v_traceState_2339_ = crate::leanh::lean_ctor_get(v___x_2334_, 4);
                v_messages_2340_ = crate::leanh::lean_ctor_get(v___x_2334_, 6);
                v_infoState_2341_ = crate::leanh::lean_ctor_get(v___x_2334_, 7);
                v_snapshotTasks_2342_ = crate::leanh::lean_ctor_get(v___x_2334_, 8);
                v_isSharedCheck_2358_ = (!crate::leanh::lean_is_exclusive(v___x_2334_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v_unused_2359_ = crate::leanh::lean_ctor_get(v___x_2334_, 5);
                    crate::leanh::lean_dec(v_unused_2359_);
                    v___x_2344_ = v___x_2334_;
                    v_isShared_2345_ = v_isSharedCheck_2358_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2342_);
                    crate::leanh::lean_inc(v_infoState_2341_);
                    crate::leanh::lean_inc(v_messages_2340_);
                    crate::leanh::lean_inc(v_traceState_2339_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2338_);
                    crate::leanh::lean_inc(v_ngen_2337_);
                    crate::leanh::lean_inc(v_nextMacroScope_2336_);
                    crate::leanh::lean_inc(v_env_2335_);
                    crate::leanh::lean_dec(v___x_2334_);
                    v___x_2344_ = crate::leanh::lean_box(0);
                    v_isShared_2345_ = v_isSharedCheck_2358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2346_ = l_Lean_Elab_deprecatedArgExt;
                v_toEnvExtension_2347_ = crate::leanh::lean_ctor_get(v___x_2346_, 0);
                v_asyncMode_2348_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2347_, 2);
                v___x_2349_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2349_, 0, v_declName_2322_);
                crate::leanh::lean_ctor_set(v___x_2349_, 1, v___y_2331_);
                crate::leanh::lean_ctor_set(v___x_2349_, 2, v___y_2332_);
                crate::leanh::lean_ctor_set(v___x_2349_, 3, v___y_2330_);
                crate::leanh::lean_ctor_set(v___x_2349_, 4, v___y_2329_);
                v___x_2350_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2346_,
                    v_env_2335_,
                    v___x_2349_,
                    v_asyncMode_2348_,
                    v___x_2318_,
                );
                v___x_2351_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                if v_isShared_2345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2344_, 5, v___x_2351_);
                    crate::leanh::lean_ctor_set(v___x_2344_, 0, v___x_2350_);
                    v___x_2353_ = v___x_2344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_nextMacroScope_2336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_ngen_2337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_auxDeclNGen_2338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_traceState_2339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 5, v___x_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 6, v_messages_2340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 7, v_infoState_2341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 8, v_snapshotTasks_2342_);
                    v___x_2353_ = v_reuseFailAlloc_2357_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2354_ = lean_st_ref_set(v___y_2333_, v___x_2353_);
                v___x_2355_ = crate::leanh::lean_box(0);
                v___x_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
                return v___x_2356_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_2363_) == 0 {
                    if v___x_2361_ == 0 {
                        v___y_2329_ = v___y_2363_;
                        v___y_2330_ = v___y_2364_;
                        v___y_2331_ = v___y_2365_;
                        v___y_2332_ = v___y_2366_;
                        v___y_2333_ = v___y_2368_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2370_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v___x_2369_, v___y_2367_, v___y_2368_);
                        if crate::leanh::lean_obj_tag(v___x_2370_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2370_, 1);
                            v___y_2329_ = v___y_2363_;
                            v___y_2330_ = v___y_2364_;
                            v___y_2331_ = v___y_2365_;
                            v___y_2332_ = v___y_2366_;
                            v___y_2333_ = v___y_2368_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_2366_);
                            crate::leanh::lean_dec(v___y_2365_);
                            crate::leanh::lean_dec(v___y_2364_);
                            crate::leanh::lean_dec(v_declName_2322_);
                            crate::leanh::lean_dec(v___x_2318_);
                            return v___x_2370_;
                        }
                    }
                } else {
                    v___y_2329_ = v___y_2363_;
                    v___y_2330_ = v___y_2364_;
                    v___y_2331_ = v___y_2365_;
                    v___y_2332_ = v___y_2366_;
                    v___y_2333_ = v___y_2368_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_2380_ = lean_array_get_size(v___y_2372_);
                v___x_2381_ = lean_nat_dec_lt(v___x_2319_, v___x_2380_);
                crate::leanh::lean_dec(v___x_2319_);
                if v___x_2381_ == 0 {
                    crate::leanh::lean_dec(v___y_2375_);
                    crate::leanh::lean_dec_ref(v___y_2372_);
                    v___y_2363_ = v___y_2373_;
                    v___y_2364_ = v___y_2374_;
                    v___y_2365_ = v___y_2376_;
                    v___y_2366_ = v___y_2377_;
                    v___y_2367_ = v___y_2378_;
                    v___y_2368_ = v___y_2379_;
                    state = 4;
                    continue;
                } else {
                    if v___x_2381_ == 0 {
                        crate::leanh::lean_dec(v___y_2375_);
                        crate::leanh::lean_dec_ref(v___y_2372_);
                        v___y_2363_ = v___y_2373_;
                        v___y_2364_ = v___y_2374_;
                        v___y_2365_ = v___y_2376_;
                        v___y_2366_ = v___y_2377_;
                        v___y_2367_ = v___y_2378_;
                        v___y_2368_ = v___y_2379_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2382_ = 0usize;
                        v___x_2383_ = lean_usize_of_nat(v___x_2380_);
                        v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v___y_2376_, v___y_2372_, v___x_2382_, v___x_2383_);
                        crate::leanh::lean_dec_ref(v___y_2372_);
                        if v___x_2384_ == 0 {
                            crate::leanh::lean_dec(v___y_2375_);
                            v___y_2363_ = v___y_2373_;
                            v___y_2364_ = v___y_2374_;
                            v___y_2365_ = v___y_2376_;
                            v___y_2366_ = v___y_2377_;
                            v___y_2367_ = v___y_2378_;
                            v___y_2368_ = v___y_2379_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_2377_);
                            crate::leanh::lean_dec(v___y_2374_);
                            crate::leanh::lean_dec(v___y_2373_);
                            crate::leanh::lean_dec(v___x_2318_);
                            v___x_2385_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                            v___x_2386_ = l_Lean_MessageData_ofName(v___y_2376_);
                            v___x_2387_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2385_);
                            crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                            v___x_2388_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2389_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2389_, 0, v___x_2387_);
                            crate::leanh::lean_ctor_set(v___x_2389_, 1, v___x_2388_);
                            v___x_2390_ = l_Lean_MessageData_ofName(v_declName_2322_);
                            v___x_2391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2389_);
                            crate::leanh::lean_ctor_set(v___x_2391_, 1, v___x_2390_);
                            v___x_2392_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2393_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2391_);
                            crate::leanh::lean_ctor_set(v___x_2393_, 1, v___x_2392_);
                            v___x_2394_ = l_Lean_MessageData_ofName(v___y_2375_);
                            v___x_2395_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2395_, 0, v___x_2393_);
                            crate::leanh::lean_ctor_set(v___x_2395_, 1, v___x_2394_);
                            v___x_2396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2397_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2397_, 0, v___x_2395_);
                            crate::leanh::lean_ctor_set(v___x_2397_, 1, v___x_2396_);
                            v___x_2398_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2397_, v___y_2378_, v___y_2379_);
                            return v___x_2398_;
                        }
                    }
                }
            }
            6 => {
                crate::leanh::lean_dec(v___y_2405_);
                crate::leanh::lean_dec(v___y_2404_);
                crate::leanh::lean_dec(v___y_2402_);
                crate::leanh::lean_dec(v___y_2401_);
                crate::leanh::lean_dec_ref(v___y_2400_);
                v___x_2408_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                v___x_2409_ = l_Lean_MessageData_ofName(v___y_2403_);
                v___x_2410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2410_, 0, v___x_2408_);
                crate::leanh::lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                v___x_2411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                v___x_2412_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2410_);
                crate::leanh::lean_ctor_set(v___x_2412_, 1, v___x_2411_);
                v___x_2413_ = l_Lean_MessageData_ofName(v_declName_2322_);
                v___x_2414_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2412_);
                crate::leanh::lean_ctor_set(v___x_2414_, 1, v___x_2413_);
                v___x_2415_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2415_, 0, v___x_2414_);
                crate::leanh::lean_ctor_set(v___x_2415_, 1, v___x_2408_);
                v___x_2416_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2415_, v___y_2407_, v___y_2406_);
                return v___x_2416_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_2421_) == 1 {
                    v_val_2425_ = crate::leanh::lean_ctor_get(v___y_2421_, 0);
                    crate::leanh::lean_inc(v_val_2425_);
                    v___x_2426_ = lean_array_get_size(v_a_2424_);
                    v___x_2427_ = lean_nat_dec_lt(v___x_2319_, v___x_2426_);
                    if v___x_2427_ == 0 {
                        crate::leanh::lean_dec(v___x_2319_);
                        crate::leanh::lean_dec(v___x_2318_);
                        v___y_2400_ = v_a_2424_;
                        v___y_2401_ = v___y_2418_;
                        v___y_2402_ = v___y_2419_;
                        v___y_2403_ = v_val_2425_;
                        v___y_2404_ = v___y_2420_;
                        v___y_2405_ = v___y_2421_;
                        v___y_2406_ = v___y_2423_;
                        v___y_2407_ = v___y_2422_;
                        state = 6;
                        continue;
                    } else {
                        if v___x_2427_ == 0 {
                            crate::leanh::lean_dec(v___x_2319_);
                            crate::leanh::lean_dec(v___x_2318_);
                            v___y_2400_ = v_a_2424_;
                            v___y_2401_ = v___y_2418_;
                            v___y_2402_ = v___y_2419_;
                            v___y_2403_ = v_val_2425_;
                            v___y_2404_ = v___y_2420_;
                            v___y_2405_ = v___y_2421_;
                            v___y_2406_ = v___y_2423_;
                            v___y_2407_ = v___y_2422_;
                            state = 6;
                            continue;
                        } else {
                            v___x_2428_ = 0usize;
                            v___x_2429_ = lean_usize_of_nat(v___x_2426_);
                            v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_val_2425_, v_a_2424_, v___x_2428_, v___x_2429_);
                            if v___x_2430_ == 0 {
                                crate::leanh::lean_dec(v___x_2319_);
                                crate::leanh::lean_dec(v___x_2318_);
                                v___y_2400_ = v_a_2424_;
                                v___y_2401_ = v___y_2418_;
                                v___y_2402_ = v___y_2419_;
                                v___y_2403_ = v_val_2425_;
                                v___y_2404_ = v___y_2420_;
                                v___y_2405_ = v___y_2421_;
                                v___y_2406_ = v___y_2423_;
                                v___y_2407_ = v___y_2422_;
                                state = 6;
                                continue;
                            } else {
                                v___y_2372_ = v_a_2424_;
                                v___y_2373_ = v___y_2418_;
                                v___y_2374_ = v___y_2419_;
                                v___y_2375_ = v_val_2425_;
                                v___y_2376_ = v___y_2420_;
                                v___y_2377_ = v___y_2421_;
                                v___y_2378_ = v___y_2422_;
                                v___y_2379_ = v___y_2423_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2431_ = lean_array_get_size(v_a_2424_);
                    v___x_2432_ = lean_nat_dec_lt(v___x_2319_, v___x_2431_);
                    crate::leanh::lean_dec(v___x_2319_);
                    if v___x_2432_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_2424_);
                        v___y_2363_ = v___y_2418_;
                        v___y_2364_ = v___y_2419_;
                        v___y_2365_ = v___y_2420_;
                        v___y_2366_ = v___y_2421_;
                        v___y_2367_ = v___y_2422_;
                        v___y_2368_ = v___y_2423_;
                        state = 4;
                        continue;
                    } else {
                        if v___x_2432_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_2424_);
                            v___y_2363_ = v___y_2418_;
                            v___y_2364_ = v___y_2419_;
                            v___y_2365_ = v___y_2420_;
                            v___y_2366_ = v___y_2421_;
                            v___y_2367_ = v___y_2422_;
                            v___y_2368_ = v___y_2423_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2433_ = 0usize;
                            v___x_2434_ = lean_usize_of_nat(v___x_2431_);
                            v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v___y_2420_, v_a_2424_, v___x_2433_, v___x_2434_);
                            crate::leanh::lean_dec_ref(v_a_2424_);
                            if v___x_2435_ == 0 {
                                v___y_2363_ = v___y_2418_;
                                v___y_2364_ = v___y_2419_;
                                v___y_2365_ = v___y_2420_;
                                v___y_2366_ = v___y_2421_;
                                v___y_2367_ = v___y_2422_;
                                v___y_2368_ = v___y_2423_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_2421_);
                                crate::leanh::lean_dec(v___y_2419_);
                                crate::leanh::lean_dec(v___y_2418_);
                                crate::leanh::lean_dec(v___x_2318_);
                                v___x_2436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                                v___x_2437_ = l_Lean_MessageData_ofName(v___y_2420_);
                                v___x_2438_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2438_, 0, v___x_2436_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2437_);
                                v___x_2439_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                                v___x_2440_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2440_, 0, v___x_2438_);
                                crate::leanh::lean_ctor_set(v___x_2440_, 1, v___x_2439_);
                                v___x_2441_ = l_Lean_MessageData_ofName(v_declName_2322_);
                                v___x_2442_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2442_, 0, v___x_2440_);
                                crate::leanh::lean_ctor_set(v___x_2442_, 1, v___x_2441_);
                                v___x_2443_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                                v___x_2444_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2444_, 0, v___x_2442_);
                                crate::leanh::lean_ctor_set(v___x_2444_, 1, v___x_2443_);
                                v___x_2445_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2444_, v___y_2422_, v___y_2423_);
                                return v___x_2445_;
                            }
                        }
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc(v_declName_2322_);
                v___x_2453_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_declName_2322_, v___y_2451_, v___y_2450_);
                if crate::leanh::lean_obj_tag(v___x_2453_) == 0 {
                    v_a_2454_ = crate::leanh::lean_ctor_get(v___x_2453_, 0);
                    crate::leanh::lean_inc(v_a_2454_);
                    crate::leanh::lean_dec_ref_known(v___x_2453_, 1);
                    v___x_2455_ = 0;
                    v___x_2456_ = 1;
                    v___x_2457_ = 0;
                    v___x_2458_ = 2;
                    v___x_2459_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 0 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 1 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 2 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 3 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 4 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 5 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 6 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 7 as u32, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 8 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 9 as u32, v___x_2456_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 10 as u32, v___x_2457_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 11 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 12 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 13 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 14 as u32, v___x_2458_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 15 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 16 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 17 as u32, v___x_2361_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2459_, 18 as u32, v___x_2361_);
                    v___x_2460_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2459_);
                    v___x_2461_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v___x_2461_, 0, v___x_2459_);
                    crate::leanh::lean_ctor_set_uint64(
                        v___x_2461_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2460_,
                    );
                    v___x_2462_ = crate::leanh::lean_box(1);
                    v___x_2463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2464_ = crate::leanh::lean_unsigned_to_nat(32);
                    v___x_2465_ = lean_mk_empty_array_with_capacity(v___x_2464_);
                    v___x_2466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
                    v___x_2467_ = 5usize;
                    crate::leanh::lean_inc_n(v___x_2319_, 7);
                    v___x_2468_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v___x_2468_, 0, v___x_2466_);
                    crate::leanh::lean_ctor_set(v___x_2468_, 1, v___x_2465_);
                    crate::leanh::lean_ctor_set(v___x_2468_, 2, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2468_, 3, v___x_2319_);
                    crate::leanh::lean_ctor_set_usize(v___x_2468_, 4, v___x_2467_);
                    crate::leanh::lean_inc_ref(v___x_2468_);
                    v___x_2469_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2469_, 0, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2469_, 1, v___x_2468_);
                    crate::leanh::lean_ctor_set(v___x_2469_, 2, v___x_2462_);
                    v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2319_);
                    v___x_2471_ = crate::leanh::lean_box(0);
                    v___x_2472_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v___x_2472_, 0, v___x_2461_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 1, v___x_2462_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 2, v___x_2469_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 3, v___x_2470_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 4, v___x_2471_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 5, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 6, v___x_2471_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v___x_2455_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v___x_2455_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v___x_2455_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v___x_2361_,
                    );
                    v___x_2473_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2473_, 0, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 1, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 2, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 3, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 4, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 5, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 6, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 7, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 8, v___x_2463_);
                    crate::leanh::lean_ctor_set(v___x_2473_, 9, v___x_2463_);
                    v___x_2474_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2475_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2473_);
                    crate::leanh::lean_ctor_set(v___x_2476_, 1, v___x_2474_);
                    crate::leanh::lean_ctor_set(v___x_2476_, 2, v___x_2462_);
                    crate::leanh::lean_ctor_set(v___x_2476_, 3, v___x_2468_);
                    crate::leanh::lean_ctor_set(v___x_2476_, 4, v___x_2475_);
                    v___x_2477_ = lean_st_mk_ref(v___x_2476_);
                    v___x_2478_ = l_Lean_ConstantInfo_type(v_a_2454_);
                    crate::leanh::lean_dec(v_a_2454_);
                    v___x_2479_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v___x_2478_, v___f_2320_, v___x_2455_, v___x_2455_, v___x_2472_, v___x_2477_, v___y_2451_, v___y_2450_);
                    crate::leanh::lean_dec_ref_known(v___x_2472_, 7);
                    if crate::leanh::lean_obj_tag(v___x_2479_) == 0 {
                        v_a_2480_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                        crate::leanh::lean_inc(v_a_2480_);
                        crate::leanh::lean_dec_ref_known(v___x_2479_, 1);
                        v___x_2481_ = lean_st_ref_get(v___x_2477_);
                        crate::leanh::lean_dec(v___x_2477_);
                        crate::leanh::lean_dec(v___x_2481_);
                        v___y_2418_ = v___y_2452_;
                        v___y_2419_ = v___y_2447_;
                        v___y_2420_ = v___y_2448_;
                        v___y_2421_ = v___y_2449_;
                        v___y_2422_ = v___y_2451_;
                        v___y_2423_ = v___y_2450_;
                        v_a_2424_ = v_a_2480_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2477_);
                        if crate::leanh::lean_obj_tag(v___x_2479_) == 0 {
                            v_a_2482_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                            crate::leanh::lean_inc(v_a_2482_);
                            crate::leanh::lean_dec_ref_known(v___x_2479_, 1);
                            v___y_2418_ = v___y_2452_;
                            v___y_2419_ = v___y_2447_;
                            v___y_2420_ = v___y_2448_;
                            v___y_2421_ = v___y_2449_;
                            v___y_2422_ = v___y_2451_;
                            v___y_2423_ = v___y_2450_;
                            v_a_2424_ = v_a_2482_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_2452_);
                            crate::leanh::lean_dec(v___y_2449_);
                            crate::leanh::lean_dec(v___y_2448_);
                            crate::leanh::lean_dec(v___y_2447_);
                            crate::leanh::lean_dec(v_declName_2322_);
                            crate::leanh::lean_dec(v___x_2319_);
                            crate::leanh::lean_dec(v___x_2318_);
                            v_a_2483_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                            v_isSharedCheck_2490_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2479_)) as u8;
                            if v_isSharedCheck_2490_ == 0 {
                                v___x_2485_ = v___x_2479_;
                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2483_);
                                crate::leanh::lean_dec(v___x_2479_);
                                v___x_2485_ = crate::leanh::lean_box(0);
                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2452_);
                    crate::leanh::lean_dec(v___y_2449_);
                    crate::leanh::lean_dec(v___y_2448_);
                    crate::leanh::lean_dec(v___y_2447_);
                    crate::leanh::lean_dec(v_declName_2322_);
                    crate::leanh::lean_dec_ref(v___f_2320_);
                    crate::leanh::lean_dec(v___x_2319_);
                    crate::leanh::lean_dec(v___x_2318_);
                    v_a_2491_ = crate::leanh::lean_ctor_get(v___x_2453_, 0);
                    v_isSharedCheck_2498_ = (!crate::leanh::lean_is_exclusive(v___x_2453_)) as u8;
                    if v_isSharedCheck_2498_ == 0 {
                        v___x_2493_ = v___x_2453_;
                        v_isShared_2494_ = v_isSharedCheck_2498_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2491_);
                        crate::leanh::lean_dec(v___x_2453_);
                        v___x_2493_ = crate::leanh::lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2498_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2486_ == 0 {
                    v___x_2488_ = v___x_2485_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
                    v___x_2488_ = v_reuseFailAlloc_2489_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2488_;
            }
            11 => {
                if v_isShared_2494_ == 0 {
                    v___x_2496_ = v___x_2493_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
                    v___x_2496_ = v_reuseFailAlloc_2497_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2496_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v___y_2500_) == 0 {
                    v___x_2506_ = crate::leanh::lean_box(0);
                    v___y_2447_ = v___y_2505_;
                    v___y_2448_ = v___y_2501_;
                    v___y_2449_ = v___y_2502_;
                    v___y_2450_ = v___y_2504_;
                    v___y_2451_ = v___y_2503_;
                    v___y_2452_ = v___x_2506_;
                    state = 8;
                    continue;
                } else {
                    v_val_2507_ = crate::leanh::lean_ctor_get(v___y_2500_, 0);
                    v_isSharedCheck_2515_ = (!crate::leanh::lean_is_exclusive(v___y_2500_)) as u8;
                    if v_isSharedCheck_2515_ == 0 {
                        v___x_2509_ = v___y_2500_;
                        v_isShared_2510_ = v_isSharedCheck_2515_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2507_);
                        crate::leanh::lean_dec(v___y_2500_);
                        v___x_2509_ = crate::leanh::lean_box(0);
                        v_isShared_2510_ = v_isSharedCheck_2515_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2511_ = l_Lean_TSyntax_getString(v_val_2507_);
                crate::leanh::lean_dec(v_val_2507_);
                if v_isShared_2510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2509_, 0, v___x_2511_);
                    v___x_2513_ = v___x_2509_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_2447_ = v___y_2505_;
                v___y_2448_ = v___y_2501_;
                v___y_2449_ = v___y_2502_;
                v___y_2450_ = v___y_2504_;
                v___y_2451_ = v___y_2503_;
                v___y_2452_ = v___x_2513_;
                state = 8;
                continue;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_2518_) == 0 {
                    v___x_2523_ = crate::leanh::lean_box(0);
                    v___y_2500_ = v___y_2517_;
                    v___y_2501_ = v___y_2519_;
                    v___y_2502_ = v___y_2522_;
                    v___y_2503_ = v___y_2521_;
                    v___y_2504_ = v___y_2520_;
                    v___y_2505_ = v___x_2523_;
                    state = 13;
                    continue;
                } else {
                    v_val_2524_ = crate::leanh::lean_ctor_get(v___y_2518_, 0);
                    v_isSharedCheck_2535_ = (!crate::leanh::lean_is_exclusive(v___y_2518_)) as u8;
                    if v_isSharedCheck_2535_ == 0 {
                        v___x_2526_ = v___y_2518_;
                        v_isShared_2527_ = v_isSharedCheck_2535_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2524_);
                        crate::leanh::lean_dec(v___y_2518_);
                        v___x_2526_ = crate::leanh::lean_box(0);
                        v_isShared_2527_ = v_isSharedCheck_2535_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_2528_ = l_Lean_TSyntax_getString(v_val_2524_);
                crate::leanh::lean_dec(v_val_2524_);
                v___x_2529_ = lean_string_utf8_byte_size(v___x_2528_);
                v___x_2530_ = lean_nat_dec_eq(v___x_2529_, v___x_2319_);
                if v___x_2530_ == 0 {
                    if v_isShared_2527_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2528_);
                        v___x_2532_ = v___x_2526_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2528_);
                        v___x_2532_ = v_reuseFailAlloc_2533_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2528_);
                    crate::leanh::lean_del_object(v___x_2526_);
                    v___x_2534_ = crate::leanh::lean_box(0);
                    v___y_2500_ = v___y_2517_;
                    v___y_2501_ = v___y_2519_;
                    v___y_2502_ = v___y_2522_;
                    v___y_2503_ = v___y_2521_;
                    v___y_2504_ = v___y_2520_;
                    v___y_2505_ = v___x_2534_;
                    state = 13;
                    continue;
                }
            }
            18 => {
                v___y_2500_ = v___y_2517_;
                v___y_2501_ = v___y_2519_;
                v___y_2502_ = v___y_2522_;
                v___y_2503_ = v___y_2521_;
                v___y_2504_ = v___y_2520_;
                v___y_2505_ = v___x_2532_;
                state = 13;
                continue;
            }
            19 => {
                v_oldArg_2546_ = l_Lean_TSyntax_getId(v_oldId_2539_);
                crate::leanh::lean_dec(v_oldId_2539_);
                if crate::leanh::lean_obj_tag(v___y_2542_) == 0 {
                    v___x_2547_ = crate::leanh::lean_box(0);
                    v___y_2517_ = v_since_x3f_2543_;
                    v___y_2518_ = v___y_2541_;
                    v___y_2519_ = v_oldArg_2546_;
                    v___y_2520_ = v___y_2545_;
                    v___y_2521_ = v___y_2544_;
                    v___y_2522_ = v___x_2547_;
                    state = 16;
                    continue;
                } else {
                    v_val_2548_ = crate::leanh::lean_ctor_get(v___y_2542_, 0);
                    v_isSharedCheck_2556_ = (!crate::leanh::lean_is_exclusive(v___y_2542_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2550_ = v___y_2542_;
                        v_isShared_2551_ = v_isSharedCheck_2556_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2548_);
                        crate::leanh::lean_dec(v___y_2542_);
                        v___x_2550_ = crate::leanh::lean_box(0);
                        v_isShared_2551_ = v_isSharedCheck_2556_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                v___x_2552_ = l_Lean_TSyntax_getId(v_val_2548_);
                crate::leanh::lean_dec(v_val_2548_);
                if v_isShared_2551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2550_, 0, v___x_2552_);
                    v___x_2554_ = v___x_2550_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
                    v___x_2554_ = v_reuseFailAlloc_2555_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_2517_ = v_since_x3f_2543_;
                v___y_2518_ = v___y_2541_;
                v___y_2519_ = v_oldArg_2546_;
                v___y_2520_ = v___y_2545_;
                v___y_2521_ = v___y_2544_;
                v___y_2522_ = v___x_2554_;
                state = 16;
                continue;
            }
            22 => {
                v___x_2563_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2564_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2563_);
                crate::leanh::lean_dec(v_stx_2323_);
                v___x_2565_ = l_Lean_Syntax_isNone(v___x_2564_);
                if v___x_2565_ == 0 {
                    v___x_2566_ = crate::leanh::lean_unsigned_to_nat(5);
                    crate::leanh::lean_inc(v___x_2564_);
                    v___x_2567_ = l_Lean_Syntax_matchesNull(v___x_2564_, v___x_2566_);
                    if v___x_2567_ == 0 {
                        crate::leanh::lean_dec(v___x_2564_);
                        crate::leanh::lean_dec(v_text_x3f_2560_);
                        crate::leanh::lean_dec(v___y_2558_);
                        crate::leanh::lean_dec(v_oldId_2539_);
                        crate::leanh::lean_dec(v_declName_2322_);
                        crate::leanh::lean_dec_ref(v___f_2320_);
                        crate::leanh::lean_dec(v___x_2319_);
                        crate::leanh::lean_dec(v___x_2318_);
                        v___x_2568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2569_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2568_, v___y_2561_, v___y_2562_);
                        return v___x_2569_;
                    } else {
                        v_since_x3f_2570_ = l_Lean_Syntax_getArg(v___x_2564_, v___y_2559_);
                        crate::leanh::lean_dec(v___x_2564_);
                        v___x_2571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2571_, 0, v_since_x3f_2570_);
                        v___y_2541_ = v_text_x3f_2560_;
                        v___y_2542_ = v___y_2558_;
                        v_since_x3f_2543_ = v___x_2571_;
                        v___y_2544_ = v___y_2561_;
                        v___y_2545_ = v___y_2562_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2564_);
                    v___x_2572_ = crate::leanh::lean_box(0);
                    v___y_2541_ = v_text_x3f_2560_;
                    v___y_2542_ = v___y_2558_;
                    v_since_x3f_2543_ = v___x_2572_;
                    v___y_2544_ = v___y_2561_;
                    v___y_2545_ = v___y_2562_;
                    state = 19;
                    continue;
                }
            }
            23 => {
                v___x_2577_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2578_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2577_);
                v___x_2579_ = l_Lean_Syntax_isNone(v___x_2578_);
                if v___x_2579_ == 0 {
                    crate::leanh::lean_inc(v___x_2578_);
                    v___x_2580_ = l_Lean_Syntax_matchesNull(v___x_2578_, v___x_2538_);
                    if v___x_2580_ == 0 {
                        crate::leanh::lean_dec(v___x_2578_);
                        crate::leanh::lean_dec(v_newId_x3f_2574_);
                        crate::leanh::lean_dec(v_oldId_2539_);
                        crate::leanh::lean_dec(v_stx_2323_);
                        crate::leanh::lean_dec(v_declName_2322_);
                        crate::leanh::lean_dec_ref(v___f_2320_);
                        crate::leanh::lean_dec(v___x_2319_);
                        crate::leanh::lean_dec(v___x_2318_);
                        v___x_2581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2582_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2581_, v___y_2575_, v___y_2576_);
                        return v___x_2582_;
                    } else {
                        v_text_x3f_2583_ = l_Lean_Syntax_getArg(v___x_2578_, v___x_2319_);
                        crate::leanh::lean_dec(v___x_2578_);
                        v___x_2584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2584_, 0, v_text_x3f_2583_);
                        v___y_2558_ = v_newId_x3f_2574_;
                        v___y_2559_ = v___x_2577_;
                        v_text_x3f_2560_ = v___x_2584_;
                        v___y_2561_ = v___y_2575_;
                        v___y_2562_ = v___y_2576_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2578_);
                    v___x_2585_ = crate::leanh::lean_box(0);
                    v___y_2558_ = v_newId_x3f_2574_;
                    v___y_2559_ = v___x_2577_;
                    v_text_x3f_2560_ = v___x_2585_;
                    v___y_2561_ = v___y_2575_;
                    v___y_2562_ = v___y_2576_;
                    state = 22;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v___x_2594_: *mut crate::leanh::LeanObject,
    mut v___x_2595_: *mut crate::leanh::LeanObject,
    mut v___x_2596_: *mut crate::leanh::LeanObject,
    mut v___x_2597_: *mut crate::leanh::LeanObject,
    mut v___f_2598_: *mut crate::leanh::LeanObject,
    mut v___x_2599_: *mut crate::leanh::LeanObject,
    mut v_declName_2600_: *mut crate::leanh::LeanObject,
    mut v_stx_2601_: *mut crate::leanh::LeanObject,
    mut v___kind_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___kind_boxed_2606_: u8 = 0;
    let mut v_res_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___kind_boxed_2606_ = (crate::leanh::lean_unbox(v___kind_2602_) as u8);
    v_res_2607_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_2594_, v___x_2595_, v___x_2596_, v___x_2597_, v___f_2598_, v___x_2599_, v_declName_2600_, v_stx_2601_, v___kind_boxed_2606_, v___y_2603_, v___y_2604_);
    crate::leanh::lean_dec(v___y_2604_);
    crate::leanh::lean_dec_ref(v___y_2603_);
    crate::leanh::lean_dec(v___x_2599_);
    return v_res_2607_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2610_ = l_Lean_stringToMessageData(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v___x_2614_: *mut crate::leanh::LeanObject,
    mut v_decl_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2620_ = l_Lean_MessageData_ofName(v___x_2614_);
    v___x_2621_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2621_, 0, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2621_, 1, v___x_2620_);
    v___x_2622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2623_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2623_, 1, v___x_2622_);
    v___x_2624_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2623_, v___y_2616_, v___y_2617_);
    return v___x_2624_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v___x_2625_: *mut crate::leanh::LeanObject,
    mut v_decl_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_2625_, v_decl_2626_, v___y_2627_, v___y_2628_);
    crate::leanh::lean_dec(v___y_2628_);
    crate::leanh::lean_dec_ref(v___y_2627_);
    crate::leanh::lean_dec(v_decl_2626_);
    return v_res_2630_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2672_ = crate::leanh::lean_unsigned_to_nat(3249530483);
    v___x_2673_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2674_ = l_Lean_Name_num___override(v___x_2673_, v___x_2672_);
    return v___x_2674_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2678_ = l_Lean_Name_str___override(v___x_2677_, v___x_2676_);
    return v___x_2678_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2681_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2682_ = l_Lean_Name_str___override(v___x_2681_, v___x_2680_);
    return v___x_2682_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2685_ = l_Lean_Name_num___override(v___x_2684_, v___x_2683_);
    return v___x_2685_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ = 0;
    v___x_2700_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2701_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2703_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    crate::leanh::lean_ctor_set(v___x_2703_, 1, v___x_2701_);
    crate::leanh::lean_ctor_set(v___x_2703_, 2, v___x_2700_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2703_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2699_,
    );
    return v___x_2703_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2704_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___f_2705_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2707_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2707_, 0, v___x_2706_);
    crate::leanh::lean_ctor_set(v___x_2707_, 1, v___f_2705_);
    crate::leanh::lean_ctor_set(v___x_2707_, 2, v___f_2704_);
    return v___x_2707_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2710_ = l_Lean_registerBuiltinAttribute(v___x_2709_);
    return v___x_2710_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v_a_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
    return v_res_2712_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2713_: *mut crate::leanh::LeanObject,
    mut v_msg_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_2714_, v___y_2715_, v___y_2716_);
    return v___x_2718_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2719_: *mut crate::leanh::LeanObject,
    mut v_msg_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(v_00_u03b1_2719_, v_msg_2720_, v___y_2721_, v___y_2722_);
    crate::leanh::lean_dec(v___y_2722_);
    crate::leanh::lean_dec_ref(v___y_2721_);
    return v_res_2724_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(
    mut v_sz_2725_: usize,
    mut v_i_2726_: usize,
    mut v_bs_2727_: *mut crate::leanh::LeanObject,
    mut v___y_2728_: *mut crate::leanh::LeanObject,
    mut v___y_2729_: *mut crate::leanh::LeanObject,
    mut v___y_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_2725_, v_i_2726_, v_bs_2727_, v___y_2728_, v___y_2730_, v___y_2731_);
    return v___x_2733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(
    mut v_sz_2734_: *mut crate::leanh::LeanObject,
    mut v_i_2735_: *mut crate::leanh::LeanObject,
    mut v_bs_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2742_: usize = 0;
    let mut v_i_boxed_2743_: usize = 0;
    let mut v_res_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2742_ = crate::leanh::lean_unbox_usize(v_sz_2734_);
    crate::leanh::lean_dec(v_sz_2734_);
    v_i_boxed_2743_ = crate::leanh::lean_unbox_usize(v_i_2735_);
    crate::leanh::lean_dec(v_i_2735_);
    v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(v_sz_boxed_2742_, v_i_boxed_2743_, v_bs_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
    crate::leanh::lean_dec(v___y_2740_);
    crate::leanh::lean_dec_ref(v___y_2739_);
    crate::leanh::lean_dec(v___y_2738_);
    crate::leanh::lean_dec_ref(v___y_2737_);
    return v_res_2744_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(
    mut v_00_u03b1_2745_: *mut crate::leanh::LeanObject,
    mut v_constName_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2746_, v___y_2747_, v___y_2748_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_00_u03b1_2751_: *mut crate::leanh::LeanObject,
    mut v_constName_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: *mut crate::leanh::LeanObject,
    mut v___y_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b1_2751_, v_constName_2752_, v___y_2753_, v___y_2754_);
    crate::leanh::lean_dec(v___y_2754_);
    crate::leanh::lean_dec_ref(v___y_2753_);
    return v_res_2756_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(
    mut v_00_u03b1_2757_: *mut crate::leanh::LeanObject,
    mut v_ref_2758_: *mut crate::leanh::LeanObject,
    mut v_constName_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2758_, v_constName_2759_, v___y_2760_, v___y_2761_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b1_2764_: *mut crate::leanh::LeanObject,
    mut v_ref_2765_: *mut crate::leanh::LeanObject,
    mut v_constName_2766_: *mut crate::leanh::LeanObject,
    mut v___y_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2770_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b1_2764_, v_ref_2765_, v_constName_2766_, v___y_2767_, v___y_2768_);
    crate::leanh::lean_dec(v___y_2768_);
    crate::leanh::lean_dec_ref(v___y_2767_);
    crate::leanh::lean_dec(v_ref_2765_);
    return v_res_2770_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(
    mut v_00_u03b1_2771_: *mut crate::leanh::LeanObject,
    mut v_ref_2772_: *mut crate::leanh::LeanObject,
    mut v_msg_2773_: *mut crate::leanh::LeanObject,
    mut v_declHint_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2772_, v_msg_2773_, v_declHint_2774_, v___y_2775_, v___y_2776_);
    return v___x_2778_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(
    mut v_00_u03b1_2779_: *mut crate::leanh::LeanObject,
    mut v_ref_2780_: *mut crate::leanh::LeanObject,
    mut v_msg_2781_: *mut crate::leanh::LeanObject,
    mut v_declHint_2782_: *mut crate::leanh::LeanObject,
    mut v___y_2783_: *mut crate::leanh::LeanObject,
    mut v___y_2784_: *mut crate::leanh::LeanObject,
    mut v___y_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(v_00_u03b1_2779_, v_ref_2780_, v_msg_2781_, v_declHint_2782_, v___y_2783_, v___y_2784_);
    crate::leanh::lean_dec(v___y_2784_);
    crate::leanh::lean_dec_ref(v___y_2783_);
    crate::leanh::lean_dec(v_ref_2780_);
    return v_res_2786_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(
    mut v_msg_2787_: *mut crate::leanh::LeanObject,
    mut v_declHint_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_2787_, v_declHint_2788_, v___y_2790_);
    return v___x_2792_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(
    mut v_msg_2793_: *mut crate::leanh::LeanObject,
    mut v_declHint_2794_: *mut crate::leanh::LeanObject,
    mut v___y_2795_: *mut crate::leanh::LeanObject,
    mut v___y_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(v_msg_2793_, v_declHint_2794_, v___y_2795_, v___y_2796_);
    crate::leanh::lean_dec(v___y_2796_);
    crate::leanh::lean_dec_ref(v___y_2795_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(
    mut v_00_u03b1_2799_: *mut crate::leanh::LeanObject,
    mut v_ref_2800_: *mut crate::leanh::LeanObject,
    mut v_msg_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
    mut v___y_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_2800_, v_msg_2801_, v___y_2802_, v___y_2803_);
    return v___x_2805_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(
    mut v_00_u03b1_2806_: *mut crate::leanh::LeanObject,
    mut v_ref_2807_: *mut crate::leanh::LeanObject,
    mut v_msg_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(v_00_u03b1_2806_, v_ref_2807_, v_msg_2808_, v___y_2809_, v___y_2810_);
    crate::leanh::lean_dec(v___y_2810_);
    crate::leanh::lean_dec_ref(v___y_2809_);
    crate::leanh::lean_dec(v_ref_2807_);
    return v_res_2812_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeprecatedArg(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_linter_deprecated_arg = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_linter_deprecated_arg);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_deprecatedArgExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_deprecatedArgExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeprecatedArg(
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
pub unsafe fn initialize_Lean_Elab_DeprecatedArg(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeprecatedArg(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeprecatedArg(builtin);
}
