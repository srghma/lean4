// Lean compiler output
// Module: Lean.Elab.DeprecatedArg
// Imports: Lean.EnvExtension Lean.Message Lean.Elab.Term
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getId, l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr5,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,13546154976408593379 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,1968078384074148898 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 97, 110, 100, 32, 101, 114, 114, 111, 114, 115, 32, 102, 111, 114, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,6273911876863363489 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,12134614065342578556 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,15915760593312485737 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value: LeanCtorObject<
    5,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_instInhabitedDeprecatedArgEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 114, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject,7421364113271725538 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value: LeanStringObject<7> =
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
        m_data: [96, 32, 111, 102, 32, 96, 0],
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value: LeanStringObject<22> =
    LeanStringObject {
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
            96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116,
            101, 100, 0,
        ],
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116,
            101, 100, 44, 32, 117, 115, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_formatDeprecatedArgMsg___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<138> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 138, m_capacity: 138, m_length: 137, m_data: [96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 104, 111, 117, 108, 100, 32, 115, 112, 101, 99, 105, 102, 121, 32, 116, 104, 101, 32, 100, 97, 116, 101, 32, 111, 114, 32, 108, 105, 98, 114, 97, 114, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 97, 116, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 115, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 100, 44, 32, 117, 115, 105, 110, 103, 32, 96, 40, 115, 105, 110, 99, 101, 32, 58, 61, 32, 34, 46, 46, 46, 34, 41, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 59, 32, 114, 101, 110, 97, 109, 101, 32, 105, 116, 32, 116, 111, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [96, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 96, 64, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [96, 59, 32, 114, 101, 109, 111, 118, 101, 32, 105, 116, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 96, 64, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,11531124740603029721 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,8394106201925823804 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,7342416184850389469 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,6378049578484137067 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,17236566213953443098 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,4850288449286909715 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,13121995851907617918 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,5210797880492880268 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,7133939494800887925 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 97, 114, 103, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanClosureObject<6> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*6) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 6, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject,12512396870021461549 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [109, 97, 114, 107, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 97, 115, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(
    mut v_name_1407_: *mut LeanObject,
    mut v_decl_1408_: *mut LeanObject,
    mut v_ref_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut v_unused_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1411_ = lean_ctor_get(v_decl_1408_, 0);
                v_descr_1412_ = lean_ctor_get(v_decl_1408_, 1);
                v_deprecation_x3f_1413_ = lean_ctor_get(v_decl_1408_, 2);
                v___x_1414_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1415_ = (lean_unbox(v_defValue_1411_) as u8);
                lean_ctor_set_uint8(v___x_1414_, 0 as u32, v___x_1415_);
                lean_inc(v_deprecation_x3f_1413_);
                lean_inc_ref(v_descr_1412_);
                lean_inc_n(v_name_1407_, 2);
                v___x_1416_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1416_, 0, v_name_1407_);
                lean_ctor_set(v___x_1416_, 1, v_ref_1409_);
                lean_ctor_set(v___x_1416_, 2, v___x_1414_);
                lean_ctor_set(v___x_1416_, 3, v_descr_1412_);
                lean_ctor_set(v___x_1416_, 4, v_deprecation_x3f_1413_);
                v___x_1417_ = lean_register_option(v_name_1407_, v___x_1416_);
                if lean_obj_tag(v___x_1417_) == 0 {
                    v_isSharedCheck_1425_ = (!lean_is_exclusive(v___x_1417_)) as u8;
                    if v_isSharedCheck_1425_ == 0 {
                        v_unused_1426_ = lean_ctor_get(v___x_1417_, 0);
                        lean_dec(v_unused_1426_);
                        v___x_1419_ = v___x_1417_;
                        v_isShared_1420_ = v_isSharedCheck_1425_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1417_);
                        v___x_1419_ = lean_box(0);
                        v_isShared_1420_ = v_isSharedCheck_1425_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1407_);
                    v_a_1427_ = lean_ctor_get(v___x_1417_, 0);
                    v_isSharedCheck_1434_ = (!lean_is_exclusive(v___x_1417_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1429_ = v___x_1417_;
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1427_);
                        lean_dec(v___x_1417_);
                        v___x_1429_ = lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1411_);
                v___x_1421_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1421_, 0, v_name_1407_);
                lean_ctor_set(v___x_1421_, 1, v_defValue_1411_);
                if v_isShared_1420_ == 0 {
                    lean_ctor_set(v___x_1419_, 0, v___x_1421_);
                    v___x_1423_ = v___x_1419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
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
                    v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
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
    mut v_name_1435_: *mut LeanObject,
    mut v_decl_1436_: *mut LeanObject,
    mut v_ref_1437_: *mut LeanObject,
    mut v_a_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1439_: *mut LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v_name_1435_, v_decl_1436_, v_ref_1437_);
    lean_dec_ref(v_decl_1436_);
    return v_res_1439_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1463_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1464_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
    v___x_1465_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v___x_1462_, v___x_1463_, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(
    mut v_a_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1467_: *mut LeanObject = core::ptr::null_mut();
    v_res_1467_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
    return v_res_1467_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(
    mut v_s_1473_: *mut LeanObject,
    mut v_e_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldArg_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_1475_ = lean_ctor_get(v_e_1474_, 0);
                lean_inc(v_declName_1475_);
                v_oldArg_1476_ = lean_ctor_get(v_e_1474_, 1);
                lean_inc(v_oldArg_1476_);
                v___x_1481_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1473_, v_declName_1475_);
                if lean_obj_tag(v___x_1481_) == 0 {
                    v___x_1482_ = lean_box(1);
                    v___y_1478_ = v___x_1482_;
                    state = 1;
                    continue;
                } else {
                    v_val_1483_ = lean_ctor_get(v___x_1481_, 0);
                    lean_inc(v_val_1483_);
                    lean_dec_ref_known(v___x_1481_, 1);
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
    mut v_es_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    v___x_1485_ = lean_array_mk(v_es_1484_);
    return v___x_1485_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_1486_: *mut LeanObject,
    mut v_i_1487_: usize,
    mut v_stop_1488_: usize,
    mut v_b_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1490_ = lean_usize_dec_eq(v_i_1487_, v_stop_1488_);
                if v___x_1490_ == 0 {
                    v___x_1491_ = lean_array_uget_borrowed(v_as_1486_, v_i_1487_);
                    lean_inc(v___x_1491_);
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
    mut v_as_1496_: *mut LeanObject,
    mut v_i_1497_: *mut LeanObject,
    mut v_stop_1498_: *mut LeanObject,
    mut v_b_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1500_: usize = 0;
    let mut v_stop_boxed_1501_: usize = 0;
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1500_ = lean_unbox_usize(v_i_1497_);
    lean_dec(v_i_1497_);
    v_stop_boxed_1501_ = lean_unbox_usize(v_stop_1498_);
    lean_dec(v_stop_1498_);
    v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v_as_1496_, v_i_boxed_1500_, v_stop_boxed_1501_, v_b_1499_);
    lean_dec_ref(v_as_1496_);
    return v_res_1502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_1503_: *mut LeanObject,
    mut v_i_1504_: usize,
    mut v_stop_1505_: usize,
    mut v_b_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: usize = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1512_ = lean_usize_dec_eq(v_i_1504_, v_stop_1505_);
                if v___x_1512_ == 0 {
                    v___x_1513_ = lean_array_uget_borrowed(v_as_1503_, v_i_1504_);
                    v___x_1514_ = lean_unsigned_to_nat(0);
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
    mut v_as_1524_: *mut LeanObject,
    mut v_i_1525_: *mut LeanObject,
    mut v_stop_1526_: *mut LeanObject,
    mut v_b_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1528_: usize = 0;
    let mut v_stop_boxed_1529_: usize = 0;
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1528_ = lean_unbox_usize(v_i_1525_);
    lean_dec(v_i_1525_);
    v_stop_boxed_1529_ = lean_unbox_usize(v_stop_1526_);
    lean_dec(v_stop_1526_);
    v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1524_, v_i_boxed_1528_, v_stop_boxed_1529_, v_b_1527_);
    lean_dec_ref(v_as_1524_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(
    mut v_initState_1531_: *mut LeanObject,
    mut v_as_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    v___x_1533_ = lean_unsigned_to_nat(0);
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
                let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
                v___x_1537_ = 0usize;
                v___x_1538_ = lean_usize_of_nat(v___x_1534_);
                v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1532_, v___x_1537_, v___x_1538_, v_initState_1531_);
                return v___x_1539_;
            }
        } else {
            let mut v___x_1540_: usize = 0;
            let mut v___x_1541_: usize = 0;
            let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
            v___x_1540_ = 0usize;
            v___x_1541_ = lean_usize_of_nat(v___x_1534_);
            v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_1532_, v___x_1540_, v___x_1541_, v_initState_1531_);
            return v___x_1542_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_1543_: *mut LeanObject,
    mut v_as_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1545_: *mut LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_1543_, v_as_1544_);
    lean_dec_ref(v_as_1544_);
    return v_res_1545_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    v___x_1563_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_;
    v___x_1564_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1563_);
    return v___x_1564_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(
    mut v_a_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1566_: *mut LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
    return v_res_1566_;
}
pub unsafe fn l_Lean_Elab_findDeprecatedArg_x3f(
    mut v_env_1567_: *mut LeanObject,
    mut v_declName_1568_: *mut LeanObject,
    mut v_argName_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_Elab_deprecatedArgExt;
    v_toEnvExtension_1571_ = lean_ctor_get(v___x_1570_, 0);
    v_asyncMode_1572_ = lean_ctor_get(v_toEnvExtension_1571_, 2);
    v___x_1573_ = lean_box(1);
    v___x_1574_ = lean_box(0);
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
    lean_dec(v___x_1575_);
    if lean_obj_tag(v___x_1576_) == 0 {
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        v___x_1577_ = lean_box(0);
        return v___x_1577_;
    } else {
        let mut v_val_1578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        v_val_1578_ = lean_ctor_get(v___x_1576_, 0);
        lean_inc(v_val_1578_);
        lean_dec_ref_known(v___x_1576_, 1);
        v___x_1579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_1578_, v_argName_1569_);
        lean_dec(v_val_1578_);
        return v___x_1579_;
    }
}
pub unsafe fn l_Lean_Elab_findDeprecatedArg_x3f___boxed(
    mut v_env_1580_: *mut LeanObject,
    mut v_declName_1581_: *mut LeanObject,
    mut v_argName_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1583_: *mut LeanObject = core::ptr::null_mut();
    v_res_1583_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_1580_, v_declName_1581_, v_argName_1582_);
    lean_dec(v_argName_1582_);
    lean_dec(v_declName_1581_);
    return v_res_1583_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1() -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__0;
    v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3() -> *mut LeanObject {
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    v___x_1588_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__2;
    v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
    return v___x_1589_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5() -> *mut LeanObject {
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1591_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__4;
    v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
    return v___x_1592_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7() -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__6;
    v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9() -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__8;
    v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11() -> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_Elab_formatDeprecatedArgMsg___closed__10;
    v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Lean_Elab_formatDeprecatedArgMsg(
    mut v_entry_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldArg_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newArg_x3f_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_1603_ = lean_ctor_get(v_entry_1602_, 0);
                lean_inc(v_declName_1603_);
                v_oldArg_1604_ = lean_ctor_get(v_entry_1602_, 1);
                lean_inc(v_oldArg_1604_);
                v_newArg_x3f_1605_ = lean_ctor_get(v_entry_1602_, 2);
                lean_inc(v_newArg_x3f_1605_);
                v_text_x3f_1606_ = lean_ctor_get(v_entry_1602_, 3);
                lean_inc(v_text_x3f_1606_);
                lean_dec_ref(v_entry_1602_);
                if lean_obj_tag(v_newArg_x3f_1605_) == 0 {
                    v___x_1614_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3,
                    );
                    v___x_1615_ = l_Lean_MessageData_ofName(v_oldArg_1604_);
                    v___x_1616_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1616_, 0, v___x_1614_);
                    lean_ctor_set(v___x_1616_, 1, v___x_1615_);
                    v___x_1617_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5,
                    );
                    v___x_1618_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    v___x_1619_ = 0;
                    v___x_1620_ = l_Lean_MessageData_ofConstName(v_declName_1603_, v___x_1619_);
                    v___x_1621_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1621_, 0, v___x_1618_);
                    lean_ctor_set(v___x_1621_, 1, v___x_1620_);
                    v___x_1622_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7,
                    );
                    v___x_1623_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1623_, 0, v___x_1621_);
                    lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                    v___y_1608_ = v___x_1623_;
                    state = 1;
                    continue;
                } else {
                    v_val_1624_ = lean_ctor_get(v_newArg_x3f_1605_, 0);
                    lean_inc(v_val_1624_);
                    lean_dec_ref_known(v_newArg_x3f_1605_, 1);
                    v___x_1625_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3,
                    );
                    v___x_1626_ = l_Lean_MessageData_ofName(v_oldArg_1604_);
                    v___x_1627_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1627_, 0, v___x_1625_);
                    lean_ctor_set(v___x_1627_, 1, v___x_1626_);
                    v___x_1628_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5,
                    );
                    v___x_1629_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1629_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1629_, 1, v___x_1628_);
                    v___x_1630_ = 0;
                    v___x_1631_ = l_Lean_MessageData_ofConstName(v_declName_1603_, v___x_1630_);
                    v___x_1632_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1632_, 0, v___x_1629_);
                    lean_ctor_set(v___x_1632_, 1, v___x_1631_);
                    v___x_1633_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9,
                    );
                    v___x_1634_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                    lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = l_Lean_MessageData_ofName(v_val_1624_);
                    v___x_1636_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                    lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                    v___x_1637_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11,
                    );
                    v___x_1638_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1638_, 0, v___x_1636_);
                    lean_ctor_set(v___x_1638_, 1, v___x_1637_);
                    v___y_1608_ = v___x_1638_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_text_x3f_1606_) == 0 {
                    return v___y_1608_;
                } else {
                    v_val_1609_ = lean_ctor_get(v_text_x3f_1606_, 0);
                    lean_inc(v_val_1609_);
                    lean_dec_ref_known(v_text_x3f_1606_, 1);
                    v___x_1610_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_formatDeprecatedArgMsg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once
                        ),
                        _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1,
                    );
                    v___x_1611_ = l_Lean_stringToMessageData(v_val_1609_);
                    v___x_1612_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1612_, 0, v___x_1610_);
                    lean_ctor_set(v___x_1612_, 1, v___x_1611_);
                    v___x_1613_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1613_, 0, v___y_1608_);
                    lean_ctor_set(v___x_1613_, 1, v___x_1612_);
                    return v___x_1613_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(
    mut v_k_1639_: *mut LeanObject,
    mut v_b_1640_: *mut LeanObject,
    mut v_c_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1645_);
    lean_inc_ref(v___y_1644_);
    lean_inc(v___y_1643_);
    lean_inc_ref(v___y_1642_);
    v___x_1647_ = lean_apply_7(
        v_k_1639_,
        v_b_1640_,
        v_c_1641_,
        v___y_1642_,
        v___y_1643_,
        v___y_1644_,
        v___y_1645_,
        lean_box(0),
    );
    return v___x_1647_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(
    mut v_k_1648_: *mut LeanObject,
    mut v_b_1649_: *mut LeanObject,
    mut v_c_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1656_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(v_k_1648_, v_b_1649_, v_c_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
    lean_dec(v___y_1654_);
    lean_dec_ref(v___y_1653_);
    lean_dec(v___y_1652_);
    lean_dec_ref(v___y_1651_);
    return v_res_1656_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(
    mut v_type_1657_: *mut LeanObject,
    mut v_k_1658_: *mut LeanObject,
    mut v_cleanupAnnotations_1659_: u8,
    mut v_whnfType_1660_: u8,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1666_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1666_, 0, v_k_1658_);
                v___x_1667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_1657_,
                    v___f_1666_,
                    v_cleanupAnnotations_1659_,
                    v_whnfType_1660_,
                    v___y_1661_,
                    v___y_1662_,
                    v___y_1663_,
                    v___y_1664_,
                );
                if lean_obj_tag(v___x_1667_) == 0 {
                    v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
                    v_isSharedCheck_1675_ = (!lean_is_exclusive(v___x_1667_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1667_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1668_);
                        lean_dec(v___x_1667_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1676_ = lean_ctor_get(v___x_1667_, 0);
                    v_isSharedCheck_1683_ = (!lean_is_exclusive(v___x_1667_)) as u8;
                    if v_isSharedCheck_1683_ == 0 {
                        v___x_1678_ = v___x_1667_;
                        v_isShared_1679_ = v_isSharedCheck_1683_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1676_);
                        lean_dec(v___x_1667_);
                        v___x_1678_ = lean_box(0);
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
                    v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
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
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
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
    mut v_type_1684_: *mut LeanObject,
    mut v_k_1685_: *mut LeanObject,
    mut v_cleanupAnnotations_1686_: *mut LeanObject,
    mut v_whnfType_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1693_: u8 = 0;
    let mut v_whnfType_boxed_1694_: u8 = 0;
    let mut v_res_1695_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1693_ = (lean_unbox(v_cleanupAnnotations_1686_) as u8);
    v_whnfType_boxed_1694_ = (lean_unbox(v_whnfType_1687_) as u8);
    v_res_1695_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_1684_, v_k_1685_, v_cleanupAnnotations_boxed_1693_, v_whnfType_boxed_1694_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    lean_dec(v___y_1691_);
    lean_dec_ref(v___y_1690_);
    lean_dec(v___y_1689_);
    lean_dec_ref(v___y_1688_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(
    mut v_00_u03b1_1696_: *mut LeanObject,
    mut v_type_1697_: *mut LeanObject,
    mut v_k_1698_: *mut LeanObject,
    mut v_cleanupAnnotations_1699_: u8,
    mut v_whnfType_1700_: u8,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_1697_, v_k_1698_, v_cleanupAnnotations_1699_, v_whnfType_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___boxed(
    mut v_00_u03b1_1707_: *mut LeanObject,
    mut v_type_1708_: *mut LeanObject,
    mut v_k_1709_: *mut LeanObject,
    mut v_cleanupAnnotations_1710_: *mut LeanObject,
    mut v_whnfType_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1717_: u8 = 0;
    let mut v_whnfType_boxed_1718_: u8 = 0;
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1717_ = (lean_unbox(v_cleanupAnnotations_1710_) as u8);
    v_whnfType_boxed_1718_ = (lean_unbox(v_whnfType_1711_) as u8);
    v_res_1719_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(v_00_u03b1_1707_, v_type_1708_, v_k_1709_, v_cleanupAnnotations_boxed_1717_, v_whnfType_boxed_1718_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
    lean_dec(v___y_1715_);
    lean_dec_ref(v___y_1714_);
    lean_dec(v___y_1713_);
    lean_dec_ref(v___y_1712_);
    return v_res_1719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(
    mut v_sz_1720_: usize,
    mut v_i_1721_: usize,
    mut v_bs_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: usize = 0;
    let mut v___x_1737_: usize = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1727_ = lean_usize_dec_lt(v_i_1721_, v_sz_1720_);
                if v___x_1727_ == 0 {
                    v___x_1728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1728_, 0, v_bs_1722_);
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
                    if lean_obj_tag(v___x_1731_) == 0 {
                        v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
                        lean_inc(v_a_1732_);
                        lean_dec_ref_known(v___x_1731_, 1);
                        v___x_1733_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1734_ = lean_array_uset(v_bs_1722_, v_i_1721_, v___x_1733_);
                        v___x_1735_ = l_Lean_LocalDecl_userName(v_a_1732_);
                        lean_dec(v_a_1732_);
                        v___x_1736_ = 1usize;
                        v___x_1737_ = lean_usize_add(v_i_1721_, v___x_1736_);
                        v___x_1738_ = lean_array_uset(v_bs_x27_1734_, v_i_1721_, v___x_1735_);
                        v_i_1721_ = v___x_1737_;
                        v_bs_1722_ = v___x_1738_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1722_);
                        v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
                        v_isSharedCheck_1747_ = (!lean_is_exclusive(v___x_1731_)) as u8;
                        if v_isSharedCheck_1747_ == 0 {
                            v___x_1742_ = v___x_1731_;
                            v_isShared_1743_ = v_isSharedCheck_1747_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1740_);
                            lean_dec(v___x_1731_);
                            v___x_1742_ = lean_box(0);
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
                    v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
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
    mut v_sz_1748_: *mut LeanObject,
    mut v_i_1749_: *mut LeanObject,
    mut v_bs_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1755_: usize = 0;
    let mut v_i_boxed_1756_: usize = 0;
    let mut v_res_1757_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1755_ = lean_unbox_usize(v_sz_1748_);
    lean_dec(v_sz_1748_);
    v_i_boxed_1756_ = lean_unbox_usize(v_i_1749_);
    lean_dec(v_i_1749_);
    v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_boxed_1755_, v_i_boxed_1756_, v_bs_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    lean_dec(v___y_1753_);
    lean_dec_ref(v___y_1752_);
    lean_dec_ref(v___y_1751_);
    return v_res_1757_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v_xs_1758_: *mut LeanObject,
    mut v_x_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1765_: usize = 0;
    let mut v___x_1766_: usize = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1765_ = lean_array_size(v_xs_1758_);
    v___x_1766_ = 0usize;
    v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_1765_, v___x_1766_, v_xs_1758_, v___y_1760_, v___y_1762_, v___y_1763_);
    return v___x_1767_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v_xs_1768_: *mut LeanObject,
    mut v_x_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1775_: *mut LeanObject = core::ptr::null_mut();
    v_res_1775_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v_xs_1768_, v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
    lean_dec(v___y_1773_);
    lean_dec_ref(v___y_1772_);
    lean_dec(v___y_1771_);
    lean_dec_ref(v___y_1770_);
    lean_dec_ref(v_x_1769_);
    return v_res_1775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(
    mut v_oldArg_1776_: *mut LeanObject,
    mut v_as_1777_: *mut LeanObject,
    mut v_i_1778_: usize,
    mut v_stop_1779_: usize,
) -> u8 {
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_oldArg_1787_: *mut LeanObject,
    mut v_as_1788_: *mut LeanObject,
    mut v_i_1789_: *mut LeanObject,
    mut v_stop_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1791_: usize = 0;
    let mut v_stop_boxed_1792_: usize = 0;
    let mut v_res_1793_: u8 = 0;
    let mut v_r_1794_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1791_ = lean_unbox_usize(v_i_1789_);
    lean_dec(v_i_1789_);
    v_stop_boxed_1792_ = lean_unbox_usize(v_stop_1790_);
    lean_dec(v_stop_1790_);
    v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_oldArg_1787_, v_as_1788_, v_i_boxed_1791_, v_stop_boxed_1792_);
    lean_dec_ref(v_as_1788_);
    lean_dec(v_oldArg_1787_);
    v_r_1794_ = lean_box((v_res_1793_) as usize);
    return v_r_1794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1795_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0);
    v___x_1797_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    v___x_1798_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_1799_ = lean_unsigned_to_nat(0);
    v___x_1800_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1800_, 0, v___x_1799_);
    lean_ctor_set(v___x_1800_, 1, v___x_1799_);
    lean_ctor_set(v___x_1800_, 2, v___x_1799_);
    lean_ctor_set(v___x_1800_, 3, v___x_1799_);
    lean_ctor_set(v___x_1800_, 4, v___x_1798_);
    lean_ctor_set(v___x_1800_, 5, v___x_1798_);
    lean_ctor_set(v___x_1800_, 6, v___x_1798_);
    lean_ctor_set(v___x_1800_, 7, v___x_1798_);
    lean_ctor_set(v___x_1800_, 8, v___x_1798_);
    lean_ctor_set(v___x_1800_, 9, v___x_1798_);
    return v___x_1800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1801_ = lean_unsigned_to_nat(32);
    v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1801_);
    v___x_1803_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1803_, 0, v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1804_: usize = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    v___x_1804_ = 5usize;
    v___x_1805_ = lean_unsigned_to_nat(0);
    v___x_1806_ = lean_unsigned_to_nat(32);
    v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
    v___x_1808_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
    v___x_1809_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    lean_ctor_set(v___x_1809_, 1, v___x_1807_);
    lean_ctor_set(v___x_1809_, 2, v___x_1805_);
    lean_ctor_set(v___x_1809_, 3, v___x_1805_);
    lean_ctor_set_usize(v___x_1809_, 4, v___x_1804_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = lean_box(1);
    v___x_1811_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4);
    v___x_1812_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_1813_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    lean_ctor_set(v___x_1813_, 2, v___x_1810_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    v___x_1815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6;
    v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
    return v___x_1816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8;
    v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
    return v___x_1819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10;
    v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
    return v___x_1822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12;
    v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
    return v___x_1825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14;
    v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
    return v___x_1828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16;
    v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18;
    v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(
    mut v_msg_1835_: *mut LeanObject,
    mut v_declHint_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v_isExporting_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1839_ = lean_st_ref_get(v___y_1837_);
                v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
                lean_inc_ref(v_env_1840_);
                lean_dec(v___x_1839_);
                v___x_1841_ = l_Lean_Name_isAnonymous(v_declHint_1836_);
                if v___x_1841_ == 0 {
                    v_isExporting_1842_ = lean_ctor_get_uint8(
                        v_env_1840_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1842_ == 0 {
                        lean_dec_ref(v_env_1840_);
                        lean_dec(v_declHint_1836_);
                        v___x_1843_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1843_, 0, v_msg_1835_);
                        return v___x_1843_;
                    } else {
                        lean_inc_ref(v_env_1840_);
                        v___x_1844_ = l_Lean_Environment_setExporting(v_env_1840_, v___x_1841_);
                        lean_inc(v_declHint_1836_);
                        lean_inc_ref(v___x_1844_);
                        v___x_1845_ = l_Lean_Environment_contains(
                            v___x_1844_,
                            v_declHint_1836_,
                            v_isExporting_1842_,
                        );
                        if v___x_1845_ == 0 {
                            lean_dec_ref(v___x_1844_);
                            lean_dec_ref(v_env_1840_);
                            lean_dec(v_declHint_1836_);
                            v___x_1846_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1846_, 0, v_msg_1835_);
                            return v___x_1846_;
                        } else {
                            v___x_1847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
                            v___x_1848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
                            v___x_1849_ = l_Lean_Options_empty;
                            v___x_1850_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1850_, 0, v___x_1844_);
                            lean_ctor_set(v___x_1850_, 1, v___x_1847_);
                            lean_ctor_set(v___x_1850_, 2, v___x_1848_);
                            lean_ctor_set(v___x_1850_, 3, v___x_1849_);
                            lean_inc(v_declHint_1836_);
                            v___x_1851_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1836_, v___x_1841_);
                            v_c_1852_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1852_, 0, v___x_1850_);
                            lean_ctor_set(v_c_1852_, 1, v___x_1851_);
                            v___x_1853_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1840_,
                                v_declHint_1836_,
                            );
                            if lean_obj_tag(v___x_1853_) == 0 {
                                lean_dec_ref(v_env_1840_);
                                lean_dec(v_declHint_1836_);
                                v___x_1854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
                                v___x_1855_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                                lean_ctor_set(v___x_1855_, 1, v_c_1852_);
                                v___x_1856_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9);
                                v___x_1857_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1857_, 0, v___x_1855_);
                                lean_ctor_set(v___x_1857_, 1, v___x_1856_);
                                v___x_1858_ = l_Lean_MessageData_note(v___x_1857_);
                                v___x_1859_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1859_, 0, v_msg_1835_);
                                lean_ctor_set(v___x_1859_, 1, v___x_1858_);
                                v___x_1860_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1860_, 0, v___x_1859_);
                                return v___x_1860_;
                            } else {
                                v_val_1861_ = lean_ctor_get(v___x_1853_, 0);
                                v_isSharedCheck_1896_ = (!lean_is_exclusive(v___x_1853_)) as u8;
                                if v_isSharedCheck_1896_ == 0 {
                                    v___x_1863_ = v___x_1853_;
                                    v_isShared_1864_ = v_isSharedCheck_1896_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1861_);
                                    lean_dec(v___x_1853_);
                                    v___x_1863_ = lean_box(0);
                                    v_isShared_1864_ = v_isSharedCheck_1896_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1840_);
                    lean_dec(v_declHint_1836_);
                    v___x_1897_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1897_, 0, v_msg_1835_);
                    return v___x_1897_;
                }
            }
            1 => {
                v___x_1865_ = lean_box(0);
                v___x_1866_ = l_Lean_Environment_header(v_env_1840_);
                lean_dec_ref(v_env_1840_);
                v___x_1867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1866_);
                v_mod_1868_ = lean_array_get(v___x_1865_, v___x_1867_, v_val_1861_);
                lean_dec(v_val_1861_);
                lean_dec_ref(v___x_1867_);
                v___x_1869_ = l_Lean_isPrivateName(v_declHint_1836_);
                lean_dec(v_declHint_1836_);
                if v___x_1869_ == 0 {
                    v___x_1870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11);
                    v___x_1871_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1871_, 0, v___x_1870_);
                    lean_ctor_set(v___x_1871_, 1, v_c_1852_);
                    v___x_1872_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13);
                    v___x_1873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1873_, 0, v___x_1871_);
                    lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                    v___x_1874_ = l_Lean_MessageData_ofName(v_mod_1868_);
                    v___x_1875_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                    lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                    v___x_1876_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15);
                    v___x_1877_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1877_, 0, v___x_1875_);
                    lean_ctor_set(v___x_1877_, 1, v___x_1876_);
                    v___x_1878_ = l_Lean_MessageData_note(v___x_1877_);
                    v___x_1879_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1879_, 0, v_msg_1835_);
                    lean_ctor_set(v___x_1879_, 1, v___x_1878_);
                    if v_isShared_1864_ == 0 {
                        lean_ctor_set_tag(v___x_1863_, 0);
                        lean_ctor_set(v___x_1863_, 0, v___x_1879_);
                        v___x_1881_ = v___x_1863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
                    v___x_1884_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    lean_ctor_set(v___x_1884_, 1, v_c_1852_);
                    v___x_1885_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17);
                    v___x_1886_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1886_, 0, v___x_1884_);
                    lean_ctor_set(v___x_1886_, 1, v___x_1885_);
                    v___x_1887_ = l_Lean_MessageData_ofName(v_mod_1868_);
                    v___x_1888_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1888_, 0, v___x_1886_);
                    lean_ctor_set(v___x_1888_, 1, v___x_1887_);
                    v___x_1889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19);
                    v___x_1890_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1890_, 0, v___x_1888_);
                    lean_ctor_set(v___x_1890_, 1, v___x_1889_);
                    v___x_1891_ = l_Lean_MessageData_note(v___x_1890_);
                    v___x_1892_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1892_, 0, v_msg_1835_);
                    lean_ctor_set(v___x_1892_, 1, v___x_1891_);
                    if v_isShared_1864_ == 0 {
                        lean_ctor_set_tag(v___x_1863_, 0);
                        lean_ctor_set(v___x_1863_, 0, v___x_1892_);
                        v___x_1894_ = v___x_1863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
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
    mut v_msg_1898_: *mut LeanObject,
    mut v_declHint_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1898_, v_declHint_1899_, v___y_1900_);
    lean_dec(v___y_1900_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(
    mut v_msg_1903_: *mut LeanObject,
    mut v_declHint_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1908_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1903_, v_declHint_1904_, v___y_1906_);
                v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
                v_isSharedCheck_1918_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                if v_isSharedCheck_1918_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    v_isShared_1912_ = v_isSharedCheck_1918_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1909_);
                    lean_dec(v___x_1908_);
                    v___x_1911_ = lean_box(0);
                    v_isShared_1912_ = v_isSharedCheck_1918_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1913_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1914_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                lean_ctor_set(v___x_1914_, 1, v_a_1909_);
                if v_isShared_1912_ == 0 {
                    lean_ctor_set(v___x_1911_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
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
    mut v_msg_1919_: *mut LeanObject,
    mut v_declHint_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1924_: *mut LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_1919_, v_declHint_1920_, v___y_1921_, v___y_1922_);
    lean_dec(v___y_1922_);
    lean_dec_ref(v___y_1921_);
    return v_res_1924_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = lean_st_ref_get(v___y_1927_);
    v_env_1930_ = lean_ctor_get(v___x_1929_, 0);
    lean_inc_ref(v_env_1930_);
    lean_dec(v___x_1929_);
    v_options_1931_ = lean_ctor_get(v___y_1926_, 2);
    v___x_1932_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
    v___x_1933_ = lean_unsigned_to_nat(32);
    v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
    lean_dec_ref(v___x_1934_);
    v___x_1935_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
    lean_inc_ref(v_options_1931_);
    v___x_1936_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1936_, 0, v_env_1930_);
    lean_ctor_set(v___x_1936_, 1, v___x_1932_);
    lean_ctor_set(v___x_1936_, 2, v___x_1935_);
    lean_ctor_set(v___x_1936_, 3, v_options_1931_);
    v___x_1937_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    lean_ctor_set(v___x_1937_, 1, v_msgData_1925_);
    v___x_1938_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1938_, 0, v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1943_: *mut LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1939_, v___y_1940_, v___y_1941_);
    lean_dec(v___y_1941_);
    lean_dec_ref(v___y_1940_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1948_ = lean_ctor_get(v___y_1945_, 5);
                v___x_1949_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msg_1944_, v___y_1945_, v___y_1946_);
                v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
                v_isSharedCheck_1958_ = (!lean_is_exclusive(v___x_1949_)) as u8;
                if v_isSharedCheck_1958_ == 0 {
                    v___x_1952_ = v___x_1949_;
                    v_isShared_1953_ = v_isSharedCheck_1958_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1950_);
                    lean_dec(v___x_1949_);
                    v___x_1952_ = lean_box(0);
                    v_isShared_1953_ = v_isSharedCheck_1958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1948_);
                v___x_1954_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1954_, 0, v_ref_1948_);
                lean_ctor_set(v___x_1954_, 1, v_a_1950_);
                if v_isShared_1953_ == 0 {
                    lean_ctor_set_tag(v___x_1952_, 1);
                    lean_ctor_set(v___x_1952_, 0, v___x_1954_);
                    v___x_1956_ = v___x_1952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
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
    mut v_msg_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_1959_, v___y_1960_, v___y_1961_);
    lean_dec(v___y_1961_);
    lean_dec_ref(v___y_1960_);
    return v_res_1963_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(
    mut v_ref_1964_: *mut LeanObject,
    mut v_msg_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1981_: u8 = 0;
    let mut v_cancelTk_x3f_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1983_: u8 = 0;
    let mut v_inheritedTraceOptions_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1969_ = lean_ctor_get(v___y_1966_, 0);
    v_fileMap_1970_ = lean_ctor_get(v___y_1966_, 1);
    v_options_1971_ = lean_ctor_get(v___y_1966_, 2);
    v_currRecDepth_1972_ = lean_ctor_get(v___y_1966_, 3);
    v_maxRecDepth_1973_ = lean_ctor_get(v___y_1966_, 4);
    v_ref_1974_ = lean_ctor_get(v___y_1966_, 5);
    v_currNamespace_1975_ = lean_ctor_get(v___y_1966_, 6);
    v_openDecls_1976_ = lean_ctor_get(v___y_1966_, 7);
    v_initHeartbeats_1977_ = lean_ctor_get(v___y_1966_, 8);
    v_maxHeartbeats_1978_ = lean_ctor_get(v___y_1966_, 9);
    v_quotContext_1979_ = lean_ctor_get(v___y_1966_, 10);
    v_currMacroScope_1980_ = lean_ctor_get(v___y_1966_, 11);
    v_diag_1981_ = lean_ctor_get_uint8(
        v___y_1966_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1982_ = lean_ctor_get(v___y_1966_, 12);
    v_suppressElabErrors_1983_ = lean_ctor_get_uint8(
        v___y_1966_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1984_ = lean_ctor_get(v___y_1966_, 13);
    v_ref_1985_ = l_Lean_replaceRef(v_ref_1964_, v_ref_1974_);
    lean_inc_ref(v_inheritedTraceOptions_1984_);
    lean_inc(v_cancelTk_x3f_1982_);
    lean_inc(v_currMacroScope_1980_);
    lean_inc(v_quotContext_1979_);
    lean_inc(v_maxHeartbeats_1978_);
    lean_inc(v_initHeartbeats_1977_);
    lean_inc(v_openDecls_1976_);
    lean_inc(v_currNamespace_1975_);
    lean_inc(v_maxRecDepth_1973_);
    lean_inc(v_currRecDepth_1972_);
    lean_inc_ref(v_options_1971_);
    lean_inc_ref(v_fileMap_1970_);
    lean_inc_ref(v_fileName_1969_);
    v___x_1986_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1986_, 0, v_fileName_1969_);
    lean_ctor_set(v___x_1986_, 1, v_fileMap_1970_);
    lean_ctor_set(v___x_1986_, 2, v_options_1971_);
    lean_ctor_set(v___x_1986_, 3, v_currRecDepth_1972_);
    lean_ctor_set(v___x_1986_, 4, v_maxRecDepth_1973_);
    lean_ctor_set(v___x_1986_, 5, v_ref_1985_);
    lean_ctor_set(v___x_1986_, 6, v_currNamespace_1975_);
    lean_ctor_set(v___x_1986_, 7, v_openDecls_1976_);
    lean_ctor_set(v___x_1986_, 8, v_initHeartbeats_1977_);
    lean_ctor_set(v___x_1986_, 9, v_maxHeartbeats_1978_);
    lean_ctor_set(v___x_1986_, 10, v_quotContext_1979_);
    lean_ctor_set(v___x_1986_, 11, v_currMacroScope_1980_);
    lean_ctor_set(v___x_1986_, 12, v_cancelTk_x3f_1982_);
    lean_ctor_set(v___x_1986_, 13, v_inheritedTraceOptions_1984_);
    lean_ctor_set_uint8(
        v___x_1986_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1981_,
    );
    lean_ctor_set_uint8(
        v___x_1986_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1983_,
    );
    v___x_1987_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_1965_, v___x_1986_, v___y_1967_);
    lean_dec_ref_known(v___x_1986_, 14);
    return v___x_1987_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(
    mut v_ref_1988_: *mut LeanObject,
    mut v_msg_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1988_, v_msg_1989_, v___y_1990_, v___y_1991_);
    lean_dec(v___y_1991_);
    lean_dec_ref(v___y_1990_);
    lean_dec(v_ref_1988_);
    return v_res_1993_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(
    mut v_ref_1994_: *mut LeanObject,
    mut v_msg_1995_: *mut LeanObject,
    mut v_declHint_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_1995_, v_declHint_1996_, v___y_1997_, v___y_1998_);
    v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
    lean_inc(v_a_2001_);
    lean_dec_ref(v___x_2000_);
    v___x_2002_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1994_, v_a_2001_, v___y_1997_, v___y_1998_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(
    mut v_ref_2003_: *mut LeanObject,
    mut v_msg_2004_: *mut LeanObject,
    mut v_declHint_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2009_: *mut LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2003_, v_msg_2004_, v_declHint_2005_, v___y_2006_, v___y_2007_);
    lean_dec(v___y_2007_);
    lean_dec_ref(v___y_2006_);
    lean_dec(v_ref_2003_);
    return v_res_2009_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    v___x_2011_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0;
    v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
    return v___x_2012_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2;
    v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(
    mut v_ref_2016_: *mut LeanObject,
    mut v_constName_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    v___x_2021_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1);
    v___x_2022_ = 0;
    lean_inc(v_constName_2017_);
    v___x_2023_ = l_Lean_MessageData_ofConstName(v_constName_2017_, v___x_2022_);
    v___x_2024_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2024_, 0, v___x_2021_);
    lean_ctor_set(v___x_2024_, 1, v___x_2023_);
    v___x_2025_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
    v___x_2026_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2026_, 0, v___x_2024_);
    lean_ctor_set(v___x_2026_, 1, v___x_2025_);
    v___x_2027_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2016_, v___x_2026_, v_constName_2017_, v___y_2018_, v___y_2019_);
    return v___x_2027_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(
    mut v_ref_2028_: *mut LeanObject,
    mut v_constName_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2033_: *mut LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2028_, v_constName_2029_, v___y_2030_, v___y_2031_);
    lean_dec(v___y_2031_);
    lean_dec_ref(v___y_2030_);
    lean_dec(v_ref_2028_);
    return v_res_2033_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(
    mut v_constName_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2038_ = lean_ctor_get(v___y_2035_, 5);
    v___x_2039_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2038_, v_constName_2034_, v___y_2035_, v___y_2036_);
    return v___x_2039_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(
    mut v_constName_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2044_: *mut LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2040_, v___y_2041_, v___y_2042_);
    lean_dec(v___y_2042_);
    lean_dec_ref(v___y_2041_);
    return v_res_2044_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(
    mut v_constName_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2049_ = lean_st_ref_get(v___y_2047_);
                v_env_2050_ = lean_ctor_get(v___x_2049_, 0);
                lean_inc_ref(v_env_2050_);
                lean_dec(v___x_2049_);
                v___x_2051_ = 0;
                lean_inc(v_constName_2045_);
                v___x_2052_ =
                    l_Lean_Environment_find_x3f(v_env_2050_, v_constName_2045_, v___x_2051_);
                if lean_obj_tag(v___x_2052_) == 0 {
                    v___x_2053_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2045_, v___y_2046_, v___y_2047_);
                    return v___x_2053_;
                } else {
                    lean_dec(v_constName_2045_);
                    v_val_2054_ = lean_ctor_get(v___x_2052_, 0);
                    v_isSharedCheck_2061_ = (!lean_is_exclusive(v___x_2052_)) as u8;
                    if v_isSharedCheck_2061_ == 0 {
                        v___x_2056_ = v___x_2052_;
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2054_);
                        lean_dec(v___x_2052_);
                        v___x_2056_ = lean_box(0);
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2057_ == 0 {
                    lean_ctor_set_tag(v___x_2056_, 0);
                    v___x_2059_ = v___x_2056_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_val_2054_);
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
    mut v_constName_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2066_: *mut LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_constName_2062_, v___y_2063_, v___y_2064_);
    lean_dec(v___y_2064_);
    lean_dec_ref(v___y_2063_);
    return v_res_2066_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(
    mut v___y_2074_: u8,
    mut v_suppressElabErrors_2075_: u8,
    mut v_x_2076_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2076_) == 1 {
        let mut v_pre_2077_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2077_ = lean_ctor_get(v_x_2076_, 0);
        match lean_obj_tag(v_pre_2077_) {
            1 => {
                let mut v_pre_2078_: *mut LeanObject = core::ptr::null_mut();
                v_pre_2078_ = lean_ctor_get(v_pre_2077_, 0);
                match lean_obj_tag(v_pre_2078_) {
                    0 => {
                        let mut v_str_2079_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_2080_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2082_: u8 = 0;
                        v_str_2079_ = lean_ctor_get(v_x_2076_, 1);
                        v_str_2080_ = lean_ctor_get(v_pre_2077_, 1);
                        v___x_2081_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_;
                        v___x_2082_ = lean_string_dec_eq(v_str_2080_, v___x_2081_);
                        if v___x_2082_ == 0 {
                            let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2084_: u8 = 0;
                            v___x_2083_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0;
                            v___x_2084_ = lean_string_dec_eq(v_str_2080_, v___x_2083_);
                            if v___x_2084_ == 0 {
                                return v___y_2074_;
                            } else {
                                let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_2089_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_2089_ = lean_ctor_get(v_pre_2078_, 0);
                        if lean_obj_tag(v_pre_2089_) == 0 {
                            let mut v_str_2090_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2091_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2092_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2094_: u8 = 0;
                            v_str_2090_ = lean_ctor_get(v_x_2076_, 1);
                            v_str_2091_ = lean_ctor_get(v_pre_2077_, 1);
                            v_str_2092_ = lean_ctor_get(v_pre_2078_, 1);
                            v___x_2093_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3;
                            v___x_2094_ = lean_string_dec_eq(v_str_2092_, v___x_2093_);
                            if v___x_2094_ == 0 {
                                return v___y_2074_;
                            } else {
                                let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2096_: u8 = 0;
                                v___x_2095_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4;
                                v___x_2096_ = lean_string_dec_eq(v_str_2091_, v___x_2095_);
                                if v___x_2096_ == 0 {
                                    return v___y_2074_;
                                } else {
                                    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_2099_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2101_: u8 = 0;
                v_str_2099_ = lean_ctor_get(v_x_2076_, 1);
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
    mut v___y_2102_: *mut LeanObject,
    mut v_suppressElabErrors_2103_: *mut LeanObject,
    mut v_x_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10682__boxed_2105_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2106_: u8 = 0;
    let mut v_res_2107_: u8 = 0;
    let mut v_r_2108_: *mut LeanObject = core::ptr::null_mut();
    v___y_10682__boxed_2105_ = (lean_unbox(v___y_2102_) as u8);
    v_suppressElabErrors_boxed_2106_ = (lean_unbox(v_suppressElabErrors_2103_) as u8);
    v_res_2107_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_10682__boxed_2105_, v_suppressElabErrors_boxed_2106_, v_x_2104_);
    lean_dec(v_x_2104_);
    v_r_2108_ = lean_box((v_res_2107_) as usize);
    return v_r_2108_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(
    mut v_opts_2109_: *mut LeanObject,
    mut v_opt_2110_: *mut LeanObject,
) -> u8 {
    let mut v_name_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v_name_2111_ = lean_ctor_get(v_opt_2110_, 0);
    v_defValue_2112_ = lean_ctor_get(v_opt_2110_, 1);
    v_map_2113_ = lean_ctor_get(v_opts_2109_, 0);
    v___x_2114_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2113_,
            v_name_2111_,
        );
    if lean_obj_tag(v___x_2114_) == 0 {
        let mut v___x_2115_: u8 = 0;
        v___x_2115_ = (lean_unbox(v_defValue_2112_) as u8);
        return v___x_2115_;
    } else {
        let mut v_val_2116_: *mut LeanObject = core::ptr::null_mut();
        v_val_2116_ = lean_ctor_get(v___x_2114_, 0);
        lean_inc(v_val_2116_);
        lean_dec_ref_known(v___x_2114_, 1);
        if lean_obj_tag(v_val_2116_) == 1 {
            let mut v_v_2117_: u8 = 0;
            v_v_2117_ = lean_ctor_get_uint8(v_val_2116_, 0 as u32);
            lean_dec_ref_known(v_val_2116_, 0);
            return v_v_2117_;
        } else {
            let mut v___x_2118_: u8 = 0;
            lean_dec(v_val_2116_);
            v___x_2118_ = (lean_unbox(v_defValue_2112_) as u8);
            return v___x_2118_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(
    mut v_opts_2119_: *mut LeanObject,
    mut v_opt_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2121_: u8 = 0;
    let mut v_r_2122_: *mut LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_opts_2119_, v_opt_2120_);
    lean_dec_ref(v_opt_2120_);
    lean_dec_ref(v_opts_2119_);
    v_r_2122_ = lean_box((v_res_2121_) as usize);
    return v_r_2122_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(
    mut v_ref_2124_: *mut LeanObject,
    mut v_msgData_2125_: *mut LeanObject,
    mut v_severity_2126_: u8,
    mut v_isSilent_2127_: u8,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: u8 = 0;
    let mut v___y_2138_: u8 = 0;
    let mut v___y_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v___y_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: u8 = 0;
    let mut v___y_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: u8 = 0;
    let mut v___y_2174_: u8 = 0;
    let mut v___y_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v___y_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: u8 = 0;
    let mut v___y_2197_: u8 = 0;
    let mut v___y_2198_: u8 = 0;
    let mut v___y_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: u8 = 0;
    let mut v___y_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2209_: u8 = 0;
    let mut v___y_2210_: u8 = 0;
    let mut v_ref_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___y_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: u8 = 0;
    let mut v___y_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: u8 = 0;
    let mut v___y_2223_: u8 = 0;
    let mut v___y_2225_: u8 = 0;
    let mut v_fileName_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2230_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_2125_);
                    v___x_2241_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2125_);
                    v___y_2225_ = v___x_2241_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2141_ = lean_st_ref_take(v___y_2140_);
                v_currNamespace_2142_ = lean_ctor_get(v___y_2139_, 6);
                v_openDecls_2143_ = lean_ctor_get(v___y_2139_, 7);
                v_env_2144_ = lean_ctor_get(v___x_2141_, 0);
                v_nextMacroScope_2145_ = lean_ctor_get(v___x_2141_, 1);
                v_ngen_2146_ = lean_ctor_get(v___x_2141_, 2);
                v_auxDeclNGen_2147_ = lean_ctor_get(v___x_2141_, 3);
                v_traceState_2148_ = lean_ctor_get(v___x_2141_, 4);
                v_cache_2149_ = lean_ctor_get(v___x_2141_, 5);
                v_messages_2150_ = lean_ctor_get(v___x_2141_, 6);
                v_infoState_2151_ = lean_ctor_get(v___x_2141_, 7);
                v_snapshotTasks_2152_ = lean_ctor_get(v___x_2141_, 8);
                v_isSharedCheck_2166_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                if v_isSharedCheck_2166_ == 0 {
                    v___x_2154_ = v___x_2141_;
                    v_isShared_2155_ = v_isSharedCheck_2166_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2152_);
                    lean_inc(v_infoState_2151_);
                    lean_inc(v_messages_2150_);
                    lean_inc(v_cache_2149_);
                    lean_inc(v_traceState_2148_);
                    lean_inc(v_auxDeclNGen_2147_);
                    lean_inc(v_ngen_2146_);
                    lean_inc(v_nextMacroScope_2145_);
                    lean_inc(v_env_2144_);
                    lean_dec(v___x_2141_);
                    v___x_2154_ = lean_box(0);
                    v_isShared_2155_ = v_isSharedCheck_2166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_2143_);
                lean_inc(v_currNamespace_2142_);
                v___x_2156_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2156_, 0, v_currNamespace_2142_);
                lean_ctor_set(v___x_2156_, 1, v_openDecls_2143_);
                v___x_2157_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                lean_ctor_set(v___x_2157_, 1, v___y_2135_);
                lean_inc_ref(v___y_2136_);
                lean_inc_ref(v___y_2133_);
                v___x_2158_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2158_, 0, v___y_2133_);
                lean_ctor_set(v___x_2158_, 1, v___y_2134_);
                lean_ctor_set(v___x_2158_, 2, v___y_2132_);
                lean_ctor_set(v___x_2158_, 3, v___y_2136_);
                lean_ctor_set(v___x_2158_, 4, v___x_2157_);
                lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2138_,
                );
                lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2137_,
                );
                lean_ctor_set_uint8(
                    v___x_2158_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2127_,
                );
                v___x_2159_ = l_Lean_MessageLog_add(v___x_2158_, v_messages_2150_);
                if v_isShared_2155_ == 0 {
                    lean_ctor_set(v___x_2154_, 6, v___x_2159_);
                    v___x_2161_ = v___x_2154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_env_2144_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_nextMacroScope_2145_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_ngen_2146_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_auxDeclNGen_2147_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_traceState_2148_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 5, v_cache_2149_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 6, v___x_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 7, v_infoState_2151_);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 8, v_snapshotTasks_2152_);
                    v___x_2161_ = v_reuseFailAlloc_2165_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2162_ = lean_st_ref_set(v___y_2140_, v___x_2161_);
                v___x_2163_ = lean_box(0);
                v___x_2164_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2164_, 0, v___x_2163_);
                return v___x_2164_;
            }
            4 => {
                v___x_2176_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2125_,
                    );
                v___x_2177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v___x_2176_, v___y_2128_, v___y_2129_);
                v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
                v_isSharedCheck_2191_ = (!lean_is_exclusive(v___x_2177_)) as u8;
                if v_isSharedCheck_2191_ == 0 {
                    v___x_2180_ = v___x_2177_;
                    v_isShared_2181_ = v_isSharedCheck_2191_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_2178_);
                    lean_dec(v___x_2177_);
                    v___x_2180_ = lean_box(0);
                    v_isShared_2181_ = v_isSharedCheck_2191_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_2169_, 2);
                v___x_2182_ = l_Lean_FileMap_toPosition(v___y_2169_, v___y_2172_);
                lean_dec(v___y_2172_);
                v___x_2183_ = l_Lean_FileMap_toPosition(v___y_2169_, v___y_2175_);
                lean_dec(v___y_2175_);
                v___x_2184_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                v___x_2185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0;
                if v___y_2171_ == 0 {
                    lean_del_object(v___x_2180_);
                    lean_dec_ref(v___y_2168_);
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
                    lean_inc(v_a_2178_);
                    v___x_2186_ = l_Lean_MessageData_hasTag(v___y_2168_, v_a_2178_);
                    if v___x_2186_ == 0 {
                        lean_dec_ref_known(v___x_2184_, 1);
                        lean_dec_ref(v___x_2182_);
                        lean_dec(v_a_2178_);
                        v___x_2187_ = lean_box(0);
                        if v_isShared_2181_ == 0 {
                            lean_ctor_set(v___x_2180_, 0, v___x_2187_);
                            v___x_2189_ = v___x_2180_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
                            v___x_2189_ = v_reuseFailAlloc_2190_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2180_);
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
                lean_dec(v___y_2199_);
                if lean_obj_tag(v___x_2201_) == 0 {
                    lean_inc(v___y_2200_);
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
                    v_val_2202_ = lean_ctor_get(v___x_2201_, 0);
                    lean_inc(v_val_2202_);
                    lean_dec_ref_known(v___x_2201_, 1);
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
                if lean_obj_tag(v___x_2212_) == 0 {
                    v___x_2213_ = lean_unsigned_to_nat(0);
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
                    v_val_2214_ = lean_ctor_get(v___x_2212_, 0);
                    lean_inc(v_val_2214_);
                    lean_dec_ref_known(v___x_2212_, 1);
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
                    v_fileName_2226_ = lean_ctor_get(v___y_2128_, 0);
                    v_fileMap_2227_ = lean_ctor_get(v___y_2128_, 1);
                    v_options_2228_ = lean_ctor_get(v___y_2128_, 2);
                    v_ref_2229_ = lean_ctor_get(v___y_2128_, 5);
                    v_suppressElabErrors_2230_ = lean_ctor_get_uint8(
                        v___y_2128_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2231_ = lean_box((v___y_2225_) as usize);
                    v___x_2232_ = lean_box((v_suppressElabErrors_2230_) as usize);
                    v___f_2233_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2233_, 0, v___x_2231_);
                    lean_closure_set(v___f_2233_, 1, v___x_2232_);
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
                    lean_dec_ref(v_msgData_2125_);
                    v___x_2238_ = lean_box(0);
                    v___x_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                    return v___x_2239_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(
    mut v_ref_2242_: *mut LeanObject,
    mut v_msgData_2243_: *mut LeanObject,
    mut v_severity_2244_: *mut LeanObject,
    mut v_isSilent_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2249_: u8 = 0;
    let mut v_isSilent_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2249_ = (lean_unbox(v_severity_2244_) as u8);
    v_isSilent_boxed_2250_ = (lean_unbox(v_isSilent_2245_) as u8);
    v_res_2251_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_2242_, v_msgData_2243_, v_severity_boxed_2249_, v_isSilent_boxed_2250_, v___y_2246_, v___y_2247_);
    lean_dec(v___y_2247_);
    lean_dec_ref(v___y_2246_);
    lean_dec(v_ref_2242_);
    return v_res_2251_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_2252_: *mut LeanObject,
    mut v_severity_2253_: u8,
    mut v_isSilent_2254_: u8,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2258_ = lean_ctor_get(v___y_2255_, 5);
    v___x_2259_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_2258_, v_msgData_2252_, v_severity_2253_, v_isSilent_2254_, v___y_2255_, v___y_2256_);
    return v___x_2259_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_2260_: *mut LeanObject,
    mut v_severity_2261_: *mut LeanObject,
    mut v_isSilent_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2266_: u8 = 0;
    let mut v_isSilent_boxed_2267_: u8 = 0;
    let mut v_res_2268_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2266_ = (lean_unbox(v_severity_2261_) as u8);
    v_isSilent_boxed_2267_ = (lean_unbox(v_isSilent_2262_) as u8);
    v_res_2268_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2260_, v_severity_boxed_2266_, v_isSilent_boxed_2267_, v___y_2263_, v___y_2264_);
    lean_dec(v___y_2264_);
    lean_dec_ref(v___y_2263_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(
    mut v_msgData_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: u8 = 0;
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = 1;
    v___x_2274_ = 0;
    v___x_2275_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2269_, v___x_2273_, v___x_2274_, v___y_2270_, v___y_2271_);
    return v___x_2275_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(
    mut v_msgData_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v_msgData_2276_, v___y_2277_, v___y_2278_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    return v_res_2280_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2281_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2282_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2283_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2284_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2285_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2285_, 0, v___x_2284_);
    lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    v___x_2289_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2290_ = l_Lean_MessageData_ofFormat(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_2295_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
    return v___x_2296_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    v___x_2298_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    v___x_2301_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2306_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    v___x_2307_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2308_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    return v___x_2308_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2310_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2310_, 0, v___x_2309_);
    lean_ctor_set(v___x_2310_, 1, v___x_2309_);
    lean_ctor_set(v___x_2310_, 2, v___x_2309_);
    lean_ctor_set(v___x_2310_, 3, v___x_2309_);
    lean_ctor_set(v___x_2310_, 4, v___x_2309_);
    lean_ctor_set(v___x_2310_, 5, v___x_2309_);
    return v___x_2310_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2312_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    lean_ctor_set(v___x_2312_, 1, v___x_2311_);
    lean_ctor_set(v___x_2312_, 2, v___x_2311_);
    lean_ctor_set(v___x_2312_, 3, v___x_2311_);
    lean_ctor_set(v___x_2312_, 4, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2314_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v___x_2316_: *mut LeanObject,
    mut v___x_2317_: *mut LeanObject,
    mut v___x_2318_: *mut LeanObject,
    mut v___x_2319_: *mut LeanObject,
    mut v___f_2320_: *mut LeanObject,
    mut v___x_2321_: *mut LeanObject,
    mut v_declName_2322_: *mut LeanObject,
    mut v_stx_2323_: *mut LeanObject,
    mut v___kind_2324_: u8,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_unused_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___y_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: usize = 0;
    let mut v___x_2429_: usize = 0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: usize = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u64 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v_a_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldId_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldArg_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut v___y_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newId_x3f_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newId_x3f_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2360_ = l_Lean_Name_mkStr2(v___x_2316_, v___x_2317_);
                lean_inc(v_stx_2323_);
                v___x_2361_ = l_Lean_Syntax_isOfKind(v_stx_2323_, v___x_2360_);
                lean_dec(v___x_2360_);
                if v___x_2361_ == 0 {
                    lean_dec(v_stx_2323_);
                    lean_dec(v_declName_2322_);
                    lean_dec_ref(v___f_2320_);
                    lean_dec(v___x_2319_);
                    lean_dec(v___x_2318_);
                    v___x_2536_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2537_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2536_, v___y_2325_, v___y_2326_);
                    return v___x_2537_;
                } else {
                    v___x_2538_ = lean_unsigned_to_nat(1);
                    v_oldId_2539_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2538_);
                    v___x_2586_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2321_);
                    v___x_2587_ = l_Lean_Syntax_isNone(v___x_2586_);
                    if v___x_2587_ == 0 {
                        lean_inc(v___x_2586_);
                        v___x_2588_ = l_Lean_Syntax_matchesNull(v___x_2586_, v___x_2538_);
                        if v___x_2588_ == 0 {
                            lean_dec(v___x_2586_);
                            lean_dec(v_oldId_2539_);
                            lean_dec(v_stx_2323_);
                            lean_dec(v_declName_2322_);
                            lean_dec_ref(v___f_2320_);
                            lean_dec(v___x_2319_);
                            lean_dec(v___x_2318_);
                            v___x_2589_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2590_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2589_, v___y_2325_, v___y_2326_);
                            return v___x_2590_;
                        } else {
                            v_newId_x3f_2591_ = l_Lean_Syntax_getArg(v___x_2586_, v___x_2319_);
                            lean_dec(v___x_2586_);
                            v___x_2592_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2592_, 0, v_newId_x3f_2591_);
                            v_newId_x3f_2574_ = v___x_2592_;
                            v___y_2575_ = v___y_2325_;
                            v___y_2576_ = v___y_2326_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2586_);
                        v___x_2593_ = lean_box(0);
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
                v_env_2335_ = lean_ctor_get(v___x_2334_, 0);
                v_nextMacroScope_2336_ = lean_ctor_get(v___x_2334_, 1);
                v_ngen_2337_ = lean_ctor_get(v___x_2334_, 2);
                v_auxDeclNGen_2338_ = lean_ctor_get(v___x_2334_, 3);
                v_traceState_2339_ = lean_ctor_get(v___x_2334_, 4);
                v_messages_2340_ = lean_ctor_get(v___x_2334_, 6);
                v_infoState_2341_ = lean_ctor_get(v___x_2334_, 7);
                v_snapshotTasks_2342_ = lean_ctor_get(v___x_2334_, 8);
                v_isSharedCheck_2358_ = (!lean_is_exclusive(v___x_2334_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v_unused_2359_ = lean_ctor_get(v___x_2334_, 5);
                    lean_dec(v_unused_2359_);
                    v___x_2344_ = v___x_2334_;
                    v_isShared_2345_ = v_isSharedCheck_2358_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2342_);
                    lean_inc(v_infoState_2341_);
                    lean_inc(v_messages_2340_);
                    lean_inc(v_traceState_2339_);
                    lean_inc(v_auxDeclNGen_2338_);
                    lean_inc(v_ngen_2337_);
                    lean_inc(v_nextMacroScope_2336_);
                    lean_inc(v_env_2335_);
                    lean_dec(v___x_2334_);
                    v___x_2344_ = lean_box(0);
                    v_isShared_2345_ = v_isSharedCheck_2358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2346_ = l_Lean_Elab_deprecatedArgExt;
                v_toEnvExtension_2347_ = lean_ctor_get(v___x_2346_, 0);
                v_asyncMode_2348_ = lean_ctor_get(v_toEnvExtension_2347_, 2);
                v___x_2349_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2349_, 0, v_declName_2322_);
                lean_ctor_set(v___x_2349_, 1, v___y_2331_);
                lean_ctor_set(v___x_2349_, 2, v___y_2332_);
                lean_ctor_set(v___x_2349_, 3, v___y_2330_);
                lean_ctor_set(v___x_2349_, 4, v___y_2329_);
                v___x_2350_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2346_,
                    v_env_2335_,
                    v___x_2349_,
                    v_asyncMode_2348_,
                    v___x_2318_,
                );
                v___x_2351_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                if v_isShared_2345_ == 0 {
                    lean_ctor_set(v___x_2344_, 5, v___x_2351_);
                    lean_ctor_set(v___x_2344_, 0, v___x_2350_);
                    v___x_2353_ = v___x_2344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2350_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_nextMacroScope_2336_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_ngen_2337_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_auxDeclNGen_2338_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_traceState_2339_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 5, v___x_2351_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 6, v_messages_2340_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 7, v_infoState_2341_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 8, v_snapshotTasks_2342_);
                    v___x_2353_ = v_reuseFailAlloc_2357_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2354_ = lean_st_ref_set(v___y_2333_, v___x_2353_);
                v___x_2355_ = lean_box(0);
                v___x_2356_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2356_, 0, v___x_2355_);
                return v___x_2356_;
            }
            4 => {
                if lean_obj_tag(v___y_2363_) == 0 {
                    if v___x_2361_ == 0 {
                        v___y_2329_ = v___y_2363_;
                        v___y_2330_ = v___y_2364_;
                        v___y_2331_ = v___y_2365_;
                        v___y_2332_ = v___y_2366_;
                        v___y_2333_ = v___y_2368_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2370_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v___x_2369_, v___y_2367_, v___y_2368_);
                        if lean_obj_tag(v___x_2370_) == 0 {
                            lean_dec_ref_known(v___x_2370_, 1);
                            v___y_2329_ = v___y_2363_;
                            v___y_2330_ = v___y_2364_;
                            v___y_2331_ = v___y_2365_;
                            v___y_2332_ = v___y_2366_;
                            v___y_2333_ = v___y_2368_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___y_2366_);
                            lean_dec(v___y_2365_);
                            lean_dec(v___y_2364_);
                            lean_dec(v_declName_2322_);
                            lean_dec(v___x_2318_);
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
                lean_dec(v___x_2319_);
                if v___x_2381_ == 0 {
                    lean_dec(v___y_2375_);
                    lean_dec_ref(v___y_2372_);
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
                        lean_dec(v___y_2375_);
                        lean_dec_ref(v___y_2372_);
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
                        lean_dec_ref(v___y_2372_);
                        if v___x_2384_ == 0 {
                            lean_dec(v___y_2375_);
                            v___y_2363_ = v___y_2373_;
                            v___y_2364_ = v___y_2374_;
                            v___y_2365_ = v___y_2376_;
                            v___y_2366_ = v___y_2377_;
                            v___y_2367_ = v___y_2378_;
                            v___y_2368_ = v___y_2379_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___y_2377_);
                            lean_dec(v___y_2374_);
                            lean_dec(v___y_2373_);
                            lean_dec(v___x_2318_);
                            v___x_2385_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                            v___x_2386_ = l_Lean_MessageData_ofName(v___y_2376_);
                            v___x_2387_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2387_, 0, v___x_2385_);
                            lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                            v___x_2388_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2389_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2389_, 0, v___x_2387_);
                            lean_ctor_set(v___x_2389_, 1, v___x_2388_);
                            v___x_2390_ = l_Lean_MessageData_ofName(v_declName_2322_);
                            v___x_2391_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2391_, 0, v___x_2389_);
                            lean_ctor_set(v___x_2391_, 1, v___x_2390_);
                            v___x_2392_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2393_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2393_, 0, v___x_2391_);
                            lean_ctor_set(v___x_2393_, 1, v___x_2392_);
                            v___x_2394_ = l_Lean_MessageData_ofName(v___y_2375_);
                            v___x_2395_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2395_, 0, v___x_2393_);
                            lean_ctor_set(v___x_2395_, 1, v___x_2394_);
                            v___x_2396_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                            v___x_2397_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2397_, 0, v___x_2395_);
                            lean_ctor_set(v___x_2397_, 1, v___x_2396_);
                            v___x_2398_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2397_, v___y_2378_, v___y_2379_);
                            return v___x_2398_;
                        }
                    }
                }
            }
            6 => {
                lean_dec(v___y_2405_);
                lean_dec(v___y_2404_);
                lean_dec(v___y_2402_);
                lean_dec(v___y_2401_);
                lean_dec_ref(v___y_2400_);
                v___x_2408_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                v___x_2409_ = l_Lean_MessageData_ofName(v___y_2403_);
                v___x_2410_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2410_, 0, v___x_2408_);
                lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                v___x_2411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                v___x_2412_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2412_, 0, v___x_2410_);
                lean_ctor_set(v___x_2412_, 1, v___x_2411_);
                v___x_2413_ = l_Lean_MessageData_ofName(v_declName_2322_);
                v___x_2414_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2414_, 0, v___x_2412_);
                lean_ctor_set(v___x_2414_, 1, v___x_2413_);
                v___x_2415_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2415_, 0, v___x_2414_);
                lean_ctor_set(v___x_2415_, 1, v___x_2408_);
                v___x_2416_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2415_, v___y_2407_, v___y_2406_);
                return v___x_2416_;
            }
            7 => {
                if lean_obj_tag(v___y_2421_) == 1 {
                    v_val_2425_ = lean_ctor_get(v___y_2421_, 0);
                    lean_inc(v_val_2425_);
                    v___x_2426_ = lean_array_get_size(v_a_2424_);
                    v___x_2427_ = lean_nat_dec_lt(v___x_2319_, v___x_2426_);
                    if v___x_2427_ == 0 {
                        lean_dec(v___x_2319_);
                        lean_dec(v___x_2318_);
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
                            lean_dec(v___x_2319_);
                            lean_dec(v___x_2318_);
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
                                lean_dec(v___x_2319_);
                                lean_dec(v___x_2318_);
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
                    lean_dec(v___x_2319_);
                    if v___x_2432_ == 0 {
                        lean_dec_ref(v_a_2424_);
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
                            lean_dec_ref(v_a_2424_);
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
                            lean_dec_ref(v_a_2424_);
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
                                lean_dec(v___y_2421_);
                                lean_dec(v___y_2419_);
                                lean_dec(v___y_2418_);
                                lean_dec(v___x_2318_);
                                v___x_2436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
                                v___x_2437_ = l_Lean_MessageData_ofName(v___y_2420_);
                                v___x_2438_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2438_, 0, v___x_2436_);
                                lean_ctor_set(v___x_2438_, 1, v___x_2437_);
                                v___x_2439_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                                v___x_2440_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2440_, 0, v___x_2438_);
                                lean_ctor_set(v___x_2440_, 1, v___x_2439_);
                                v___x_2441_ = l_Lean_MessageData_ofName(v_declName_2322_);
                                v___x_2442_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2442_, 0, v___x_2440_);
                                lean_ctor_set(v___x_2442_, 1, v___x_2441_);
                                v___x_2443_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                                v___x_2444_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2444_, 0, v___x_2442_);
                                lean_ctor_set(v___x_2444_, 1, v___x_2443_);
                                v___x_2445_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2444_, v___y_2422_, v___y_2423_);
                                return v___x_2445_;
                            }
                        }
                    }
                }
            }
            8 => {
                lean_inc(v_declName_2322_);
                v___x_2453_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_declName_2322_, v___y_2451_, v___y_2450_);
                if lean_obj_tag(v___x_2453_) == 0 {
                    v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
                    lean_inc(v_a_2454_);
                    lean_dec_ref_known(v___x_2453_, 1);
                    v___x_2455_ = 0;
                    v___x_2456_ = 1;
                    v___x_2457_ = 0;
                    v___x_2458_ = 2;
                    v___x_2459_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v___x_2459_, 0 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 1 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 2 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 3 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 4 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 5 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 6 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 7 as u32, v___x_2455_);
                    lean_ctor_set_uint8(v___x_2459_, 8 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 9 as u32, v___x_2456_);
                    lean_ctor_set_uint8(v___x_2459_, 10 as u32, v___x_2457_);
                    lean_ctor_set_uint8(v___x_2459_, 11 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 12 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 13 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 14 as u32, v___x_2458_);
                    lean_ctor_set_uint8(v___x_2459_, 15 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 16 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 17 as u32, v___x_2361_);
                    lean_ctor_set_uint8(v___x_2459_, 18 as u32, v___x_2361_);
                    v___x_2460_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2459_);
                    v___x_2461_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v___x_2461_, 0, v___x_2459_);
                    lean_ctor_set_uint64(
                        v___x_2461_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2460_,
                    );
                    v___x_2462_ = lean_box(1);
                    v___x_2463_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2464_ = lean_unsigned_to_nat(32);
                    v___x_2465_ = lean_mk_empty_array_with_capacity(v___x_2464_);
                    v___x_2466_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
                    v___x_2467_ = 5usize;
                    lean_inc_n(v___x_2319_, 7);
                    v___x_2468_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v___x_2468_, 0, v___x_2466_);
                    lean_ctor_set(v___x_2468_, 1, v___x_2465_);
                    lean_ctor_set(v___x_2468_, 2, v___x_2319_);
                    lean_ctor_set(v___x_2468_, 3, v___x_2319_);
                    lean_ctor_set_usize(v___x_2468_, 4, v___x_2467_);
                    lean_inc_ref(v___x_2468_);
                    v___x_2469_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2469_, 0, v___x_2463_);
                    lean_ctor_set(v___x_2469_, 1, v___x_2468_);
                    lean_ctor_set(v___x_2469_, 2, v___x_2462_);
                    v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2319_);
                    v___x_2471_ = lean_box(0);
                    v___x_2472_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v___x_2472_, 0, v___x_2461_);
                    lean_ctor_set(v___x_2472_, 1, v___x_2462_);
                    lean_ctor_set(v___x_2472_, 2, v___x_2469_);
                    lean_ctor_set(v___x_2472_, 3, v___x_2470_);
                    lean_ctor_set(v___x_2472_, 4, v___x_2471_);
                    lean_ctor_set(v___x_2472_, 5, v___x_2319_);
                    lean_ctor_set(v___x_2472_, 6, v___x_2471_);
                    lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v___x_2455_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v___x_2455_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v___x_2455_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2472_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v___x_2361_,
                    );
                    v___x_2473_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v___x_2473_, 0, v___x_2319_);
                    lean_ctor_set(v___x_2473_, 1, v___x_2319_);
                    lean_ctor_set(v___x_2473_, 2, v___x_2319_);
                    lean_ctor_set(v___x_2473_, 3, v___x_2319_);
                    lean_ctor_set(v___x_2473_, 4, v___x_2463_);
                    lean_ctor_set(v___x_2473_, 5, v___x_2463_);
                    lean_ctor_set(v___x_2473_, 6, v___x_2463_);
                    lean_ctor_set(v___x_2473_, 7, v___x_2463_);
                    lean_ctor_set(v___x_2473_, 8, v___x_2463_);
                    lean_ctor_set(v___x_2473_, 9, v___x_2463_);
                    v___x_2474_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                    v___x_2476_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_2476_, 0, v___x_2473_);
                    lean_ctor_set(v___x_2476_, 1, v___x_2474_);
                    lean_ctor_set(v___x_2476_, 2, v___x_2462_);
                    lean_ctor_set(v___x_2476_, 3, v___x_2468_);
                    lean_ctor_set(v___x_2476_, 4, v___x_2475_);
                    v___x_2477_ = lean_st_mk_ref(v___x_2476_);
                    v___x_2478_ = l_Lean_ConstantInfo_type(v_a_2454_);
                    lean_dec(v_a_2454_);
                    v___x_2479_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v___x_2478_, v___f_2320_, v___x_2455_, v___x_2455_, v___x_2472_, v___x_2477_, v___y_2451_, v___y_2450_);
                    lean_dec_ref_known(v___x_2472_, 7);
                    if lean_obj_tag(v___x_2479_) == 0 {
                        v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
                        lean_inc(v_a_2480_);
                        lean_dec_ref_known(v___x_2479_, 1);
                        v___x_2481_ = lean_st_ref_get(v___x_2477_);
                        lean_dec(v___x_2477_);
                        lean_dec(v___x_2481_);
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
                        lean_dec(v___x_2477_);
                        if lean_obj_tag(v___x_2479_) == 0 {
                            v_a_2482_ = lean_ctor_get(v___x_2479_, 0);
                            lean_inc(v_a_2482_);
                            lean_dec_ref_known(v___x_2479_, 1);
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
                            lean_dec(v___y_2452_);
                            lean_dec(v___y_2449_);
                            lean_dec(v___y_2448_);
                            lean_dec(v___y_2447_);
                            lean_dec(v_declName_2322_);
                            lean_dec(v___x_2319_);
                            lean_dec(v___x_2318_);
                            v_a_2483_ = lean_ctor_get(v___x_2479_, 0);
                            v_isSharedCheck_2490_ = (!lean_is_exclusive(v___x_2479_)) as u8;
                            if v_isSharedCheck_2490_ == 0 {
                                v___x_2485_ = v___x_2479_;
                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2483_);
                                lean_dec(v___x_2479_);
                                v___x_2485_ = lean_box(0);
                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_2452_);
                    lean_dec(v___y_2449_);
                    lean_dec(v___y_2448_);
                    lean_dec(v___y_2447_);
                    lean_dec(v_declName_2322_);
                    lean_dec_ref(v___f_2320_);
                    lean_dec(v___x_2319_);
                    lean_dec(v___x_2318_);
                    v_a_2491_ = lean_ctor_get(v___x_2453_, 0);
                    v_isSharedCheck_2498_ = (!lean_is_exclusive(v___x_2453_)) as u8;
                    if v_isSharedCheck_2498_ == 0 {
                        v___x_2493_ = v___x_2453_;
                        v_isShared_2494_ = v_isSharedCheck_2498_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2491_);
                        lean_dec(v___x_2453_);
                        v___x_2493_ = lean_box(0);
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
                    v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
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
                    v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
                    v___x_2496_ = v_reuseFailAlloc_2497_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2496_;
            }
            13 => {
                if lean_obj_tag(v___y_2500_) == 0 {
                    v___x_2506_ = lean_box(0);
                    v___y_2447_ = v___y_2505_;
                    v___y_2448_ = v___y_2501_;
                    v___y_2449_ = v___y_2502_;
                    v___y_2450_ = v___y_2504_;
                    v___y_2451_ = v___y_2503_;
                    v___y_2452_ = v___x_2506_;
                    state = 8;
                    continue;
                } else {
                    v_val_2507_ = lean_ctor_get(v___y_2500_, 0);
                    v_isSharedCheck_2515_ = (!lean_is_exclusive(v___y_2500_)) as u8;
                    if v_isSharedCheck_2515_ == 0 {
                        v___x_2509_ = v___y_2500_;
                        v_isShared_2510_ = v_isSharedCheck_2515_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_val_2507_);
                        lean_dec(v___y_2500_);
                        v___x_2509_ = lean_box(0);
                        v_isShared_2510_ = v_isSharedCheck_2515_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2511_ = l_Lean_TSyntax_getString(v_val_2507_);
                lean_dec(v_val_2507_);
                if v_isShared_2510_ == 0 {
                    lean_ctor_set(v___x_2509_, 0, v___x_2511_);
                    v___x_2513_ = v___x_2509_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
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
                if lean_obj_tag(v___y_2518_) == 0 {
                    v___x_2523_ = lean_box(0);
                    v___y_2500_ = v___y_2517_;
                    v___y_2501_ = v___y_2519_;
                    v___y_2502_ = v___y_2522_;
                    v___y_2503_ = v___y_2521_;
                    v___y_2504_ = v___y_2520_;
                    v___y_2505_ = v___x_2523_;
                    state = 13;
                    continue;
                } else {
                    v_val_2524_ = lean_ctor_get(v___y_2518_, 0);
                    v_isSharedCheck_2535_ = (!lean_is_exclusive(v___y_2518_)) as u8;
                    if v_isSharedCheck_2535_ == 0 {
                        v___x_2526_ = v___y_2518_;
                        v_isShared_2527_ = v_isSharedCheck_2535_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_val_2524_);
                        lean_dec(v___y_2518_);
                        v___x_2526_ = lean_box(0);
                        v_isShared_2527_ = v_isSharedCheck_2535_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_2528_ = l_Lean_TSyntax_getString(v_val_2524_);
                lean_dec(v_val_2524_);
                v___x_2529_ = lean_string_utf8_byte_size(v___x_2528_);
                v___x_2530_ = lean_nat_dec_eq(v___x_2529_, v___x_2319_);
                if v___x_2530_ == 0 {
                    if v_isShared_2527_ == 0 {
                        lean_ctor_set(v___x_2526_, 0, v___x_2528_);
                        v___x_2532_ = v___x_2526_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2528_);
                        v___x_2532_ = v_reuseFailAlloc_2533_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2528_);
                    lean_del_object(v___x_2526_);
                    v___x_2534_ = lean_box(0);
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
                lean_dec(v_oldId_2539_);
                if lean_obj_tag(v___y_2542_) == 0 {
                    v___x_2547_ = lean_box(0);
                    v___y_2517_ = v_since_x3f_2543_;
                    v___y_2518_ = v___y_2541_;
                    v___y_2519_ = v_oldArg_2546_;
                    v___y_2520_ = v___y_2545_;
                    v___y_2521_ = v___y_2544_;
                    v___y_2522_ = v___x_2547_;
                    state = 16;
                    continue;
                } else {
                    v_val_2548_ = lean_ctor_get(v___y_2542_, 0);
                    v_isSharedCheck_2556_ = (!lean_is_exclusive(v___y_2542_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2550_ = v___y_2542_;
                        v_isShared_2551_ = v_isSharedCheck_2556_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_val_2548_);
                        lean_dec(v___y_2542_);
                        v___x_2550_ = lean_box(0);
                        v_isShared_2551_ = v_isSharedCheck_2556_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                v___x_2552_ = l_Lean_TSyntax_getId(v_val_2548_);
                lean_dec(v_val_2548_);
                if v_isShared_2551_ == 0 {
                    lean_ctor_set(v___x_2550_, 0, v___x_2552_);
                    v___x_2554_ = v___x_2550_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
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
                v___x_2563_ = lean_unsigned_to_nat(4);
                v___x_2564_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2563_);
                lean_dec(v_stx_2323_);
                v___x_2565_ = l_Lean_Syntax_isNone(v___x_2564_);
                if v___x_2565_ == 0 {
                    v___x_2566_ = lean_unsigned_to_nat(5);
                    lean_inc(v___x_2564_);
                    v___x_2567_ = l_Lean_Syntax_matchesNull(v___x_2564_, v___x_2566_);
                    if v___x_2567_ == 0 {
                        lean_dec(v___x_2564_);
                        lean_dec(v_text_x3f_2560_);
                        lean_dec(v___y_2558_);
                        lean_dec(v_oldId_2539_);
                        lean_dec(v_declName_2322_);
                        lean_dec_ref(v___f_2320_);
                        lean_dec(v___x_2319_);
                        lean_dec(v___x_2318_);
                        v___x_2568_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2569_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2568_, v___y_2561_, v___y_2562_);
                        return v___x_2569_;
                    } else {
                        v_since_x3f_2570_ = l_Lean_Syntax_getArg(v___x_2564_, v___y_2559_);
                        lean_dec(v___x_2564_);
                        v___x_2571_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2571_, 0, v_since_x3f_2570_);
                        v___y_2541_ = v_text_x3f_2560_;
                        v___y_2542_ = v___y_2558_;
                        v_since_x3f_2543_ = v___x_2571_;
                        v___y_2544_ = v___y_2561_;
                        v___y_2545_ = v___y_2562_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2564_);
                    v___x_2572_ = lean_box(0);
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
                v___x_2577_ = lean_unsigned_to_nat(3);
                v___x_2578_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2577_);
                v___x_2579_ = l_Lean_Syntax_isNone(v___x_2578_);
                if v___x_2579_ == 0 {
                    lean_inc(v___x_2578_);
                    v___x_2580_ = l_Lean_Syntax_matchesNull(v___x_2578_, v___x_2538_);
                    if v___x_2580_ == 0 {
                        lean_dec(v___x_2578_);
                        lean_dec(v_newId_x3f_2574_);
                        lean_dec(v_oldId_2539_);
                        lean_dec(v_stx_2323_);
                        lean_dec(v_declName_2322_);
                        lean_dec_ref(v___f_2320_);
                        lean_dec(v___x_2319_);
                        lean_dec(v___x_2318_);
                        v___x_2581_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
                        v___x_2582_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2581_, v___y_2575_, v___y_2576_);
                        return v___x_2582_;
                    } else {
                        v_text_x3f_2583_ = l_Lean_Syntax_getArg(v___x_2578_, v___x_2319_);
                        lean_dec(v___x_2578_);
                        v___x_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2584_, 0, v_text_x3f_2583_);
                        v___y_2558_ = v_newId_x3f_2574_;
                        v___y_2559_ = v___x_2577_;
                        v_text_x3f_2560_ = v___x_2584_;
                        v___y_2561_ = v___y_2575_;
                        v___y_2562_ = v___y_2576_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2578_);
                    v___x_2585_ = lean_box(0);
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
    mut v___x_2594_: *mut LeanObject,
    mut v___x_2595_: *mut LeanObject,
    mut v___x_2596_: *mut LeanObject,
    mut v___x_2597_: *mut LeanObject,
    mut v___f_2598_: *mut LeanObject,
    mut v___x_2599_: *mut LeanObject,
    mut v_declName_2600_: *mut LeanObject,
    mut v_stx_2601_: *mut LeanObject,
    mut v___kind_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___kind_boxed_2606_: u8 = 0;
    let mut v_res_2607_: *mut LeanObject = core::ptr::null_mut();
    v___kind_boxed_2606_ = (lean_unbox(v___kind_2602_) as u8);
    v_res_2607_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_2594_, v___x_2595_, v___x_2596_, v___x_2597_, v___f_2598_, v___x_2599_, v_declName_2600_, v_stx_2601_, v___kind_boxed_2606_, v___y_2603_, v___y_2604_);
    lean_dec(v___y_2604_);
    lean_dec_ref(v___y_2603_);
    lean_dec(v___x_2599_);
    return v_res_2607_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2610_ = l_Lean_stringToMessageData(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2612_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(
    mut v___x_2614_: *mut LeanObject,
    mut v_decl_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2619_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2620_ = l_Lean_MessageData_ofName(v___x_2614_);
    v___x_2621_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2621_, 0, v___x_2619_);
    lean_ctor_set(v___x_2621_, 1, v___x_2620_);
    v___x_2622_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2623_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2623_, 0, v___x_2621_);
    lean_ctor_set(v___x_2623_, 1, v___x_2622_);
    v___x_2624_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_2623_, v___y_2616_, v___y_2617_);
    return v___x_2624_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v___x_2625_: *mut LeanObject,
    mut v_decl_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2630_: *mut LeanObject = core::ptr::null_mut();
    v_res_2630_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_2625_, v_decl_2626_, v___y_2627_, v___y_2628_);
    lean_dec(v___y_2628_);
    lean_dec_ref(v___y_2627_);
    lean_dec(v_decl_2626_);
    return v_res_2630_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    v___x_2672_ = lean_unsigned_to_nat(3249530483);
    v___x_2673_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2674_ = l_Lean_Name_num___override(v___x_2673_, v___x_2672_);
    return v___x_2674_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    v___x_2676_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2677_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2678_ = l_Lean_Name_str___override(v___x_2677_, v___x_2676_);
    return v___x_2678_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2680_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2681_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2682_ = l_Lean_Name_str___override(v___x_2681_, v___x_2680_);
    return v___x_2682_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = lean_unsigned_to_nat(2);
    v___x_2684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2685_ = l_Lean_Name_num___override(v___x_2684_, v___x_2683_);
    return v___x_2685_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    v___x_2699_ = 0;
    v___x_2700_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2701_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2702_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2703_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    lean_ctor_set(v___x_2703_, 1, v___x_2701_);
    lean_ctor_set(v___x_2703_, 2, v___x_2700_);
    lean_ctor_set_uint8(
        v___x_2703_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2699_,
    );
    return v___x_2703_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    v___f_2704_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___f_2705_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
    v___x_2706_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2707_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2707_, 0, v___x_2706_);
    lean_ctor_set(v___x_2707_, 1, v___f_2705_);
    lean_ctor_set(v___x_2707_, 2, v___f_2704_);
    return v___x_2707_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    v___x_2709_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
    v___x_2710_ = l_Lean_registerBuiltinAttribute(v___x_2709_);
    return v___x_2710_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(
    mut v_a_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2712_: *mut LeanObject = core::ptr::null_mut();
    v_res_2712_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
    return v_res_2712_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2713_: *mut LeanObject,
    mut v_msg_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    v___x_2718_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_2714_, v___y_2715_, v___y_2716_);
    return v___x_2718_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2719_: *mut LeanObject,
    mut v_msg_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(v_00_u03b1_2719_, v_msg_2720_, v___y_2721_, v___y_2722_);
    lean_dec(v___y_2722_);
    lean_dec_ref(v___y_2721_);
    return v_res_2724_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(
    mut v_sz_2725_: usize,
    mut v_i_2726_: usize,
    mut v_bs_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_2725_, v_i_2726_, v_bs_2727_, v___y_2728_, v___y_2730_, v___y_2731_);
    return v___x_2733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(
    mut v_sz_2734_: *mut LeanObject,
    mut v_i_2735_: *mut LeanObject,
    mut v_bs_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2742_: usize = 0;
    let mut v_i_boxed_2743_: usize = 0;
    let mut v_res_2744_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2742_ = lean_unbox_usize(v_sz_2734_);
    lean_dec(v_sz_2734_);
    v_i_boxed_2743_ = lean_unbox_usize(v_i_2735_);
    lean_dec(v_i_2735_);
    v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(v_sz_boxed_2742_, v_i_boxed_2743_, v_bs_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
    lean_dec(v___y_2740_);
    lean_dec_ref(v___y_2739_);
    lean_dec(v___y_2738_);
    lean_dec_ref(v___y_2737_);
    return v_res_2744_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(
    mut v_00_u03b1_2745_: *mut LeanObject,
    mut v_constName_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    v___x_2750_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_2746_, v___y_2747_, v___y_2748_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_00_u03b1_2751_: *mut LeanObject,
    mut v_constName_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b1_2751_, v_constName_2752_, v___y_2753_, v___y_2754_);
    lean_dec(v___y_2754_);
    lean_dec_ref(v___y_2753_);
    return v_res_2756_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(
    mut v_00_u03b1_2757_: *mut LeanObject,
    mut v_ref_2758_: *mut LeanObject,
    mut v_constName_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_2758_, v_constName_2759_, v___y_2760_, v___y_2761_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b1_2764_: *mut LeanObject,
    mut v_ref_2765_: *mut LeanObject,
    mut v_constName_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2770_: *mut LeanObject = core::ptr::null_mut();
    v_res_2770_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b1_2764_, v_ref_2765_, v_constName_2766_, v___y_2767_, v___y_2768_);
    lean_dec(v___y_2768_);
    lean_dec_ref(v___y_2767_);
    lean_dec(v_ref_2765_);
    return v_res_2770_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(
    mut v_00_u03b1_2771_: *mut LeanObject,
    mut v_ref_2772_: *mut LeanObject,
    mut v_msg_2773_: *mut LeanObject,
    mut v_declHint_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_2772_, v_msg_2773_, v_declHint_2774_, v___y_2775_, v___y_2776_);
    return v___x_2778_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(
    mut v_00_u03b1_2779_: *mut LeanObject,
    mut v_ref_2780_: *mut LeanObject,
    mut v_msg_2781_: *mut LeanObject,
    mut v_declHint_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2786_: *mut LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(v_00_u03b1_2779_, v_ref_2780_, v_msg_2781_, v_declHint_2782_, v___y_2783_, v___y_2784_);
    lean_dec(v___y_2784_);
    lean_dec_ref(v___y_2783_);
    lean_dec(v_ref_2780_);
    return v_res_2786_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(
    mut v_msg_2787_: *mut LeanObject,
    mut v_declHint_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_2787_, v_declHint_2788_, v___y_2790_);
    return v___x_2792_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(
    mut v_msg_2793_: *mut LeanObject,
    mut v_declHint_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2798_: *mut LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(v_msg_2793_, v_declHint_2794_, v___y_2795_, v___y_2796_);
    lean_dec(v___y_2796_);
    lean_dec_ref(v___y_2795_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(
    mut v_00_u03b1_2799_: *mut LeanObject,
    mut v_ref_2800_: *mut LeanObject,
    mut v_msg_2801_: *mut LeanObject,
    mut v___y_2802_: *mut LeanObject,
    mut v___y_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_2800_, v_msg_2801_, v___y_2802_, v___y_2803_);
    return v___x_2805_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(
    mut v_00_u03b1_2806_: *mut LeanObject,
    mut v_ref_2807_: *mut LeanObject,
    mut v_msg_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(v_00_u03b1_2806_, v_ref_2807_, v_msg_2808_, v___y_2809_, v___y_2810_);
    lean_dec(v___y_2810_);
    lean_dec_ref(v___y_2809_);
    lean_dec(v_ref_2807_);
    return v_res_2812_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeprecatedArg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_linter_deprecated_arg = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_linter_deprecated_arg);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_deprecatedArgExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_deprecatedArgExt);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeprecatedArg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeprecatedArg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeprecatedArg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DeprecatedArg(builtin);
}
